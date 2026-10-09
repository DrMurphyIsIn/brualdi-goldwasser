"""RIGOROUS (mpmath.iv, outward rounding; exact rationals for Z, x): the comparison with explicit spiders
(rate gaps Gamma_K; the comparison with explicit spiders, parts (i) and (iii)).

Setting (the rate potential at lambda = 1): for cap C = k-1 and H = h - eta_C w,
  g(R) = eta|R| + H(x_R) + delta^H(R),  delta^H(R) = sum of per-vertex rate slacks >= 0.
For a maximizer T (n >= 7) rooted at a vertex r of maximum degree k <= 23 that is not a spider centre:
  every minimal non-atom (w.r.t. r) is an end hub [C^c A_s^m1 A_{s+1}^m2] (c+m1+m2>=2, m1+m2>=1) or a stalk [A_j],
  j<=4 (the possible shapes of minimal non-atoms); its branch B has delta^H(B) >= gamma_C := min over these shapes.
  Case A (>=2 non-atom branches at r):  Phi <= Psi_k - eta N - 2 gamma.
  Case B (exactly one, Q):  Phi <= Psi'_k - eta N - gamma,
     Psi'_k = max over the k-1 atoms at r (no leaves if k>=3; arms balanced) and x_Q in [0,1/2] of
              log(1+(S_atoms + x_Q)/k) - H(x_Q) - sum_atoms (g(a) - eta|a|).
Compare with Phi*_lo(n) from explicit table spiders (exact pi, interval log)."""
import os; os.environ.setdefault("OMP_NUM_THREADS", "1")
import sys, json, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from fractions import Fraction as Fr
from mpmath import iv, mpf
from ivtools import LAM, F, H_iv, bb_upper, hull
from spider_table import parse
from core import pi_rooted
iv.prec = 120
cert = json.load(open(os.path.join(HERE, 'certify_out.json')))   # written by ../bg_rate/certify.py
ETA = {int(C): Fr(v) for C, v in cert['etas'].items()}

def br(ch):
    c = len(ch); Z = Fr(1); S = Fr(0)
    for z, x, n in ch: Z *= z; S += x
    return (Z * (c + 1 + S) / (c + 1), 1 / (c + 1 + S), 1 + sum(n for _, _, n in ch))
L = (Fr(1), Fr(1), 1); C = br([L])
ARM = {0: L}
def A(j):
    if j not in ARM: ARM[j] = br([C] * j)
    return ARM[j]
def logfr(z): return iv.log(F(z))
def g_iv(b): return b[2] * LAM - logfr(b[0])
def dH(b, eta):   # delta^H(b) = g - eta|b| - H(x)
    return g_iv(b) - F(eta) * b[2] - H_iv(F(b[1]), eta)

# ---- tail bound for arms: delta^H(A_j) >= j(beta-2eta) + lam - log(4/3) - kappa q^2 + 10 eta  (x_j<q, w>=11) ----
from ivtools import BETA, KAP, QI
def tail_lb(j, eta): return j * (BETA - 2 * F(eta)) + LAM - iv.log(F(Fr(4, 3))) - KAP * QI * QI + 10 * F(eta)

LOGZ = {}
def logZ_atom(j):
    if j not in LOGZ: LOGZ[j] = logfr(A(j)[0]) if j > 0 else F(0)
    return LOGZ[j]
LOGC = logfr(C[0])
def dH_hub(eta, parts):
    """parts: list of (count, atom index: 'C' or j); delta^H of the hub with these children"""
    Zlog = F(0); S = Fr(0); n = 1; c = 0
    for cnt, a in parts:
        if cnt == 0: continue
        if a == 'C': Zlog += cnt * LOGC; S += cnt * C[1]; n += 2 * cnt
        else: Zlog += cnt * logZ_atom(a); S += cnt * A(a)[1]; n += cnt * (2 * a + 1)
        c += cnt
    Zlog += iv.log(F((c + 1 + S) / (c + 1)))
    x = 1 / (c + 1 + S)
    return n * LAM - Zlog - F(eta) * n - H_iv(F(x), eta)

def gamma(Ccap, J=18):
    eta = ETA[Ccap]; best = None; arg = None
    for j in range(1, 5):
        v = dH_hub(eta, [(1, j)])
        if best is None or v.a < best.a: best, arg = v, ('stalk', j)
    for s_ in range(1, J + 1):
        for tot in range(2, Ccap + 1):
            for m in range(1, tot + 1):
                for m1 in range(0, m + 1):
                    m2 = m - m1; c = tot - m
                    v = dH_hub(eta, [(c, 'C'), (m1, s_), (m2, s_ + 1)])
                    if v.a < best.a: best, arg = v, ('hub', (c, s_, m1, m2))
    if Ccap >= 2:
        assert (BETA - 2 * F(eta)).a > 0
        if not tail_lb(J + 1, eta).a > best.b:
            return gamma(Ccap, J + 6)
    return best, arg

# ---- spider lower bounds ----
rows = parse()
def phistar_lo(n):
    ch = rows[n]
    p = pi_rooted(ch)
    return (iv.log(F(p)) - (n - 1) * LAM).a

# ---- Psi_k (upper bounds) and Psi'_k ----
def Psi(k):
    eta = ETA[k - 1]
    ub, _ = bb_upper(lambda Y: iv.log(1 + Y) - k * H_iv(Y, eta), mpf(0), mpf(1), nmax=3000)
    return ub
def PsiB(k, J=18, NG=400, jn=1):
    """rigorous upper bound: U(S) = max_{x in [0,1/2]} log(1+(S+x)/k) - H(x) is increasing in S;
    bound U on a grid of S and use the grid point above each configuration's S."""
    eta = ETA[k - 1]; m = k - jn
    if m < 0: return None, None
    Smax = Fr(max(m, 1))  # messages <= 1
    grid = [Smax * i / NG for i in range(NG + 1)]
    U = []
    for Sg in grid:
        ub, _ = bb_upper(lambda X, Sg=Sg: iv.log(1 + (F(Sg) + jn * X) / k) - jn * H_iv(X, eta), mpf(0), mpf(0.5), nmax=300)
        U.append(ub)
    def cost(j):   # g - eta|a| for atom index ('C', j>=1, or 0 = leaf)
        if j == 'C': return 2 * LAM - LOGC - 2 * F(eta), C[1]
        if j == 0: return LAM - F(eta), Fr(1)
        return (2 * j + 1) * LAM - logZ_atom(j) - (2 * j + 1) * F(eta), A(j)[1]
    CO = {a: cost(a) for a in ['C', 0] + list(range(1, J + 2))}
    best = None; barg = None; lst = []
    cfgs = []
    for s_ in range(1, J + 1):
        for m1 in range(0, m + 1):
            for m2 in range(0, m - m1 + 1):
                cfgs.append(((m - m1 - m2, 'C'), (m1, s_), (m2, s_ + 1)))
    if k == 2 and m == 1: cfgs.append(((1, 0),))
    if m == 0: cfgs = [((0, 'C'),)]
    for cf in cfgs:
        K = F(0); S = Fr(0); size = 0
        for cnt, a in cf:
            if cnt:
                K += cnt * CO[a][0]; S += cnt * CO[a][1]
                size += cnt * (2 if a == 'C' else (1 if a == 0 else 2 * a + 1))
        i = min(NG, -((-S * NG) // Smax))   # ceil
        v = (iv.mpf(U[i]) - K).b
        lst.append((v, size, cf))
        if best is None or v > best: best, barg = v, cf
    return best, barg, lst

if __name__ == "__main__":
    MINQ = 4   # a non-atom branch has at least 4 vertices
    res = {}
    KR = range(int(sys.argv[1]), int(sys.argv[2]) + 1) if len(sys.argv) > 2 else range(2, 24)
    for k in KR:
        gm, arg = gamma(k - 1)
        eta = ETA[k - 1]
        P = Psi(k)
        cands = []   # (value upper bound, minimal N for feasibility)
        # tail: any configuration containing an arm A_j with j > 18: value <= Psi_k - delta^H(A_19) - j_n * gamma, j_n >= 1
        cands.append(((iv.mpf(P) - tail_lb(19, eta) - gm.a).b, MINQ))
        jn = 1
        while jn <= k:
            if (iv.mpf(P) - jn * gm.a).b <= min(c[0] for c in cands): break
            _, _, lst = PsiB(k, jn=jn)
            for v, size, cf in lst:
                cands.append(((iv.mpf(v) - jn * gm.a).b, size + jn * MINQ))
            # all larger jn: bounded by Psi_k - jn*gamma (no size information used)
            jn += 1
        cands.append(((iv.mpf(P) - jn * gm.a).b, jn * MINQ))
        cands.sort(key=lambda c: c[1])
        bad = []
        for n in range(7, 316):
            N = n - 1
            V = max(c[0] for c in cands if c[1] <= N) if any(c[1] <= N for c in cands) else None
            if V is None: continue
            if (iv.mpf(V) - F(eta) * N).b >= phistar_lo(n): bad.append(n)
        n0 = (max(bad) + 1) if bad else 7
        res[k] = dict(eta=str(eta), gamma_lo=float(gm.a), gamma_arg=str(arg), Psi=float(P), n0=n0,
                      Vmax=float(max(c[0] for c in cands)), bad=bad)
        print(k, "eta=%.7f gamma>=%.6f (%s) Psi<=%.5f Vmax<=%.5f n0=%d" % (float(eta), float(gm.a), arg, float(P), res[k]['Vmax'], n0), flush=True)
    N0 = max(v['n0'] for v in res.values())
    print("N0 =", N0)
    ceil = iv.log(F(Fr(26, 23))) - F(Fr(12445, 10**6))
    mn = min(phistar_lo(n) for n in range(25, 316))
    print("high degree: ceiling <= %.7f < min table Phi*_lo(25..315) = %.7f : %s" % (float(ceil.b), float(mn), ceil.b < mn))
    json.dump(dict(res=res, N0=N0), open('conc_out.json' if len(sys.argv) <= 2 else 'conc_out_%s_%s.json' % (sys.argv[1], sys.argv[2]), 'w'), indent=1)
