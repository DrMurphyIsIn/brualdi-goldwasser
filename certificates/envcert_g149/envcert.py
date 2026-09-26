"""Sharded, kernel-checkable envelope certificate for the BG finite range (generator + exact re-check).

Every quantity here is an exact integer or Fraction and mirrors the Lean definitions in
proof/formalization/R3Cert/BGEnvCert/*.lean bit for bit (fixed point with P fractional bits; packed
lanes of width W).  See proof/docs/BG_ENVCERT_2026-09-25.md for the math.

Stored lane value x of a W_s / Wn_s table represents the real (x - OFF)/2^P; a c-part knapsack table
entry represents (x - c*OFF)/2^P.  All tables are (rows = size 0..Smax) x (columns = grid 0..H-1),
lane index = row*H + column.
"""
import math, sys, os, time, json
from fractions import Fraction as Fr
import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

P = 34                  # fractional bits
OFF = 1 << 47           # stored offset (real range [-8192, 8192) for W tables)
W = 56                  # lane width (guard bit W-1)
H = 100                 # grid size
MU = [Fr(g + 1, 2 * H) for g in range(H)]
FSTAR = math.log(621 / 64) / 11
FQ = Fr(round(FSTAR * 2 ** 40), 2 ** 40)   # the rational rate used everywhere (it cancels exactly)
NL = 30                 # series terms for a reduced log
NL2 = 60                # series terms for log 2
UDEN = 1 << 30          # denominator of the tangent points u
SCALE = 1 << P


def lser(x, n):
    """sum_{i<n} x^(i+1)/(i+1)  (Lean: EnvCert.lser)."""
    s = Fr(0)
    for i in range(n):
        s += x ** (i + 1) / (i + 1)
    return s


def lerr(x, n):
    ax = abs(x)
    return ax ** (n + 1) / (1 - ax)


L2UP = lser(Fr(1, 2), NL2) + lerr(Fr(1, 2), NL2)
L2LO = lser(Fr(1, 2), NL2) - lerr(Fr(1, 2), NL2)


def pow2(m):
    return Fr(2) ** m


def logOK(z, m):
    return z > 0 and abs(1 - pow2(m) / z) < 1


def logUB(z, m):
    """Upper bound for log z (Lean: EnvCert.logUB): m log 2 + (-log(1-x)), x = 1 - 2^m/z."""
    x = 1 - pow2(m) / z
    return m * (L2UP if m >= 0 else L2LO) + (lser(x, NL) + lerr(x, NL))


def logLB(z, m):
    x = 1 - pow2(m) / z
    return m * (L2LO if m >= 0 else L2UP) + (lser(x, NL) - lerr(x, NL))


def redm(z):
    """exponent m with z/2^m in [3/4, 3/2)."""
    return math.floor(math.log2(float(z) / 0.75))


def ceil_fr(q):
    return -((-q.numerator) // q.denominator)


def floor_fr(q):
    return q.numerator // q.denominator


# ---------------------------------------------------------------- tangent constants per (g, h)
_tan = {}


def tangent(g, h):
    """(u, m, A, N): u rational tangent point, A >= 2^P (log u + 2mu/u - 1 - f), N >= 2^P nu, nu <= mu_h."""
    key = (g, h)
    if key in _tan:
        return _tan[key]
    mu, muh = MU[g], MU[h]
    disc = 1 - 4 * float(mu) * float(muh)
    ust = (1 + math.sqrt(max(disc, 0.0))) / (2 * float(muh))
    u = Fr(math.ceil(ust * UDEN), UDEN)
    while (u - mu) / u ** 2 > muh:
        u += Fr(1, UDEN)
    assert u >= 2 * mu and u > 0
    nu = (u - mu) / u ** 2
    m = redm(u)
    A = ceil_fr(SCALE * (logUB(u, m) + 2 * mu / u - 1 - FQ))
    N = ceil_fr(SCALE * nu)
    _tan[key] = (u, m, A, N)
    return _tan[key]


def tangent_float(g, h):
    mu, muh = float(MU[g]), float(MU[h])
    disc = 1 - 4 * mu * muh
    u = (1 + math.sqrt(max(disc, 0.0))) / (2 * muh)
    nu = (u - mu) / u ** 2
    return (math.log(u) + 2 * mu / u - 1 - float(FQ)) * SCALE, nu * SCALE


_ld = {}


def logd_lo(d):
    if d not in _ld:
        m = redm(d)
        _ld[d] = (m, floor_fr(SCALE * logLB(Fr(d), m)))
    return _ld[d]


# ---------------------------------------------------------------- the DP (true, row by row)
BIG = 1 << 60


def cst_matrix_float(c):
    """float estimate of Cst(c, g, h) for witness selection."""
    d = c + 1
    M = np.empty((H, H))
    for g in range(H):
        for h in range(H):
            a, n = tangent_float(g, h)
            M[g, h] = a + n * d - math.log(d) * SCALE
    return M


_cstf = {}


def cstf(c):
    if c not in _cstf:
        _cstf[c] = cst_matrix_float(c)
    return _cstf[c]


def cst_exact(c, g, h):
    u, m, A, N = tangent(g, h)
    return A + N * (c + 1) - logd_lo(c + 1)[1]


def shift_rows(T, m):
    out = np.zeros_like(T)
    if m < T.shape[0]:
        out[m:] = T[:T.shape[0] - m]
    return out


class CapTables:
    """Envelope tables for cap C (children per vertex <= C), rows 0..Smax; root tables up to k = C+1."""

    def __init__(self, C, Smax, kmax):
        self.C, self.Smax, self.kmax = C, Smax, kmax
        self.build()

    def build(self):
        C, S = self.C, self.Smax
        Wa = np.zeros((S + 1, H), dtype=np.int64)
        Wn = np.zeros((S + 1, H), dtype=np.int64)
        for g in range(H):
            Wa[1, g] = OFF + ceil_fr(SCALE * (MU[g] - FQ))
        K = {c: np.zeros((S + 1, H), dtype=np.int64) for c in range(1, C + 1)}
        Kx = {c: np.zeros((S + 1, H), dtype=np.int64) for c in range(1, C + 1)}
        K1p = np.zeros((S + 1, H), dtype=np.int64)       # Wa rows >= 3 (c = 1 non-atom)
        wit_a = {}   # (c, g) -> set(h)
        wit_n = {}
        # exact Cst matrices lazily per c, only on selected (g,h)
        for s in range(1, S + 1):
            N = s - 1
            if s >= 2:
                # knapsack rows N for c >= 2 (true DP: m <= N)
                for c in range(2, C + 1):
                    if N == 0:
                        continue
                    ms = np.arange(1, N + 1)
                    K[c][N] = np.max(K[c - 1][N - ms] + Wa[ms], axis=0)
                    t1 = np.max(Kx[c - 1][N - ms] + Wa[ms], axis=0)
                    ms2 = ms[ms != 2]
                    t2 = np.max(K[c - 1][N - ms2] + Wa[ms2], axis=0) if len(ms2) else np.zeros(H, np.int64)
                    Kx[c][N] = np.maximum(t1, t2)
                va = None
                vn = None
                for c in range(1, min(C, N) + 1):
                    Kc = K[c][N]
                    Kxc = Kx[c][N] if c >= 2 else K1p[N]
                    # float-guided argmin over h, then exact
                    Mf = cstf(c) + Kc[None, :].astype(np.float64)
                    hs = np.argmin(Mf, axis=1)
                    Mfx = cstf(c) + Kxc[None, :].astype(np.float64)
                    hsx = np.argmin(Mfx, axis=1)
                    ra = np.empty(H, dtype=np.int64)
                    rn = np.empty(H, dtype=np.int64)
                    for g in range(H):
                        best = None
                        for h in cand(hs[g], Mf[g]):
                            v = cst_exact(c, g, h) + int(Kc[h]) - c * OFF
                            if best is None or v < best[0]:
                                best = (v, h)
                        ra[g] = best[0]
                        wit_a.setdefault((c, g), set()).add(best[1])
                        if True:   # c = 1, N < 3: K1p row is 0 (vacuous), keep the lane consistent
                            best = None
                            for h in cand(hsx[g], Mfx[g]):
                                v = cst_exact(c, g, h) + int(Kxc[h]) - c * OFF
                                if best is None or v < best[0]:
                                    best = (v, h)
                            rn[g] = best[0]
                            wit_n.setdefault((c, g), set()).add(best[1])
                        else:
                            rn[g] = -BIG
                    va = ra if va is None else np.maximum(va, ra)
                    vn = rn if vn is None else np.maximum(vn, rn)
                Wa[s] = OFF + va
                Wn[s] = np.maximum(OFF + vn, 0)
            # K rows for c = 1
            K[1][s] = Wa[s]
            Kx[1][s] = Wa[s] if s != 2 else 0
            K1p[s] = Wa[s] if s >= 3 else 0
        assert Wa.min() >= 0 and Wa.max() < 2 * OFF and Wn.max() < 2 * OFF
        self.Wa, self.Wn = Wa, Wn
        self.wit_a, self.wit_n = wit_a, wit_n


def cand(h0, row):
    """candidate h set around the float argmin (exact tie-break)."""
    order = np.argsort(row)[:3]
    return sorted(set(int(x) for x in order) | {int(h0)})


# ---------------------------------------------------------------- kernel replica (exactly the Lean check)
def kernel_tables(Wa, Wn, C, kmax):
    """K_c (c<=C), Kx_c (c<=C), R_c (c<=kmax) exactly as the Lean kernel computes them (all m in 1..Smax)."""
    S = Wa.shape[0] - 1
    K = {1: Wa.copy()}
    Kx = {1: Wa.copy()}
    Kx[1][2] = 0
    R = {1: Wn.copy()}
    top = max(C, kmax)
    for c in range(2, top + 1):
        acc = np.zeros_like(Wa)
        accx = np.zeros_like(Wa)
        accr = np.zeros_like(Wa)
        for m in range(1, S + 1):
            bw = Wa[m][None, :]
            if c <= C:
                acc = np.maximum(acc, shift_rows(K[c - 1], m) + bw)
                accx = np.maximum(accx, shift_rows(Kx[c - 1], m) + bw)
                if m != 2:
                    accx = np.maximum(accx, shift_rows(K[c - 1], m) + bw)
            if c <= kmax:
                accr = np.maximum(accr, shift_rows(R[c - 1], m) + bw)
                accr = np.maximum(accr, shift_rows(K[c - 1], m) + Wn[m][None, :])
        if c <= C:
            K[c], Kx[c] = acc, accx
        if c <= kmax:
            R[c] = accr
    return K, Kx, R


def bellman_check(Wa, Wn, K, Kx, C, wit_a, wit_n):
    """lane (s,g), s in 2..Smax: for every c <= C some witness h passes (exactly the Lean predicate)."""
    S = Wa.shape[0] - 1
    K1p = Wa.copy()
    K1p[:3] = 0
    bad = 0
    for c in range(1, C + 1):
        for g in range(H):
            for tab, Wt, wit in ((K[c], Wa, wit_a), (Kx[c] if c >= 2 else K1p, Wn, wit_n)):
                hs = sorted(wit.get((c, g), {0}))
                ok = np.zeros(S + 1, dtype=bool)
                for h in hs:
                    Cst = cst_exact(c, g, h)
                    X = Wt[:, g] + c * OFF - Cst
                    Y = np.zeros(S + 1, dtype=np.int64)
                    Y[1:] = tab[:S, h]
                    Y = Y + OFF
                    ok |= (X >= Y)
                lo = 2 if Wt is Wa else 3      # non-atoms have size >= 3
                bad += int((~ok[lo:]).sum())
    return bad


# ---------------------------------------------------------------- spiders and the root
_spider = None


def best_spiders(nmax):
    global _spider
    import bg_spider_reduction as B
    if _spider is None or max(_spider) < nmax:
        _spider = B.spider_max(nmax + 1)
    return _spider


def atom_T_y(nm):
    if nm == "L":
        return Fr(1), Fr(1)
    if nm == "C":
        return Fr(3, 2), Fr(1, 3)
    j = int(nm[1:])
    return Fr(3, 2) ** j * Fr(4 * j + 3, 3 * j + 3), Fr(3, 4 * j + 3)


def spider_Q(rep):
    k = len(rep)
    Pp, S = Fr(1), Fr(0)
    for nm in rep:
        T, y = atom_T_y(nm)
        Pp *= T
        S += y
    return Pp * (1 + S / k)


def phi_lo(n, rep):
    Q = spider_Q(rep)
    m = redm(Q)
    return floor_fr(SCALE * (logLB(Q, m) - (n - 1) * FQ)), m


_troot = {}


def troot(k, g):
    key = (k, g)
    if key not in _troot:
        t = 1 / (k * MU[g])
        m = redm(t)
        _troot[key] = (m, ceil_fr(SCALE * (logUB(t, m) + 1 / t - 1)))
    return _troot[key]


def troot_float(k, g):
    t = 1 / (k * float(MU[g]))
    return (math.log(t) + 1 / t - 1) * SCALE


def root_margins(R, kset, nmin, nmax, phis):
    """for each (n, k): best g and margin PHI_lo - bound (units 2^-P)."""
    out = {}
    for k in kset:
        Rk = R[k]
        for n in range(max(nmin, k + 1), nmax + 1):
            vals = [troot_float(k, g) + float(Rk[n - 1, g]) - k * OFF for g in range(H)]
            order = np.argsort(vals)[:3]
            best = None
            for g in order:
                v = troot(k, int(g))[1] + int(Rk[n - 1, g]) - k * OFF
                if best is None or v < best[0]:
                    best = (v, int(g))
            out[(n, k)] = (phis[n][0] - best[0], best[1])
    return out


def cap_of(k, caps):
    return min(c for c in caps if c >= k - 1)


def run(nmax, caps, nmin=7, verbose=True):
    t0 = time.time()
    sp = best_spiders(nmax)
    phis = {n: phi_lo(n, sp[n][1][0]) for n in range(nmin, nmax + 1)}
    Smax = nmax - 1
    groups = {}
    for k in range(2, nmax):
        groups.setdefault(cap_of(k, caps), []).append(k)
    res = {}
    allm = {}
    for C in sorted(groups):
        ks = groups[C]
        kmax = max(ks)
        ct = CapTables(C, Smax, kmax)
        K, Kx, R = kernel_tables(ct.Wa, ct.Wn, C, kmax)
        bad = bellman_check(ct.Wa, ct.Wn, K, Kx, C, ct.wit_a, ct.wit_n)
        mg = root_margins(R, ks, nmin, nmax, phis)
        nw = sum(len(v) for v in ct.wit_a.values()) + sum(len(v) for v in ct.wit_n.values())
        worst = min(mg.values())
        if verbose:
            print(f"cap {C}: k={ks[0]}..{ks[-1]} bellman-bad={bad} witnesses={nw} "
                  f"worst root margin={worst[0] / SCALE:.3e} {time.time() - t0:.1f}s", flush=True)
        res[C] = (ct, ks, mg, bad)
        allm.update(mg)
    worst_n = {}
    for (n, k), (mgv, g) in allm.items():
        if n not in worst_n or mgv < worst_n[n][0]:
            worst_n[n] = (mgv, k, g)
    fails = sorted(n for n, v in worst_n.items() if v[0] <= 0)
    if verbose:
        print("failures:", fails)
        ws = sorted((v[0], n, v[1]) for n, v in worst_n.items())[:8]
        print("smallest margins:", [(round(m / SCALE, 7), n, k) for m, n, k in ws])
    return res, phis, worst_n


if __name__ == "__main__":
    nmax = int(sys.argv[1])
    caps = [int(x) for x in sys.argv[2].split(",")]
    run(nmax, caps)
