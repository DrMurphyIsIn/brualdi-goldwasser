"""
Exact optimization of Aobj over the two-level spider family (B2, 2026-09-24).

Family.  A centre whose children are cherries P (pendant 2-paths) and arms A_j (a vertex adjacent to the
centre carrying j cherries; A_0 is a leaf).  A configuration X is the multiset of children:
C cherries and k_j arms A_j.  n = 1 + 2C + sum_j k_j (2j + 1).  D = C + sum_j k_j (centre degree).

Closed form (cavity recursion of hwh_coverage_large_n.py at the centre; checked against aobj_exact below):
    child   cost c   weight g                   r
    P       2        3/2                        1/3
    A_j     2j+1     (3/2)^j alpha_j            b_j,    alpha_j = (4j+3)/(3(j+1)),  b_j = 3/(4j+3)
    F(X) = prod g * (1 + R/D),   R = sum r.
i.e. pi = (3/2)^(C + sum j) * prod alpha_j * (1 + (L + C/3 + sum_j 3/(4j+3)) / D)  with L = k_0 leaves.

Proved structure (analytic identities, see `symbolic`, and Lean R3Cert/BGSpiderOpt.lean):
  * balance: for j >= k+2 and any other children with count D0 and r-sum R0, replacing A_j, A_k by
    A_{j-1}, A_{k+1} multiplies F by 1 + (j-k-1)((c-3)(4j+4k+7)+3) / (9 (k+1)(k+2) j (j+1) Q) with
    c = D + R0 = D0 + 2 + R0, Q = alpha_j alpha_k (c + b_j + b_k) > 0.  So if D >= 3 the maximizer is balanced:
    all arm sizes (leaves count as A_0) lie in {s, s+1}.
  * leaves: A_0 + A_0 -> P never decreases F (strict unless the two leaves are the only children).
  * cherry absorption P + A_j -> A_{j+1}: explicit polynomial criterion (`symbolic`).

Exhaustive search (`search`): for every n, (i) all configurations with D <= 2 exactly, (ii) all balanced
configurations with D >= 3 (parameters C and m = number of arms determine it), float log prefilter with a
1e-9 margin (float error < 1e-11 for n <= 10^4), every candidate inside the margin decided in exact Fractions.
By the balance lemma (i)+(ii) is the whole family, so this is an exact maximization over the family.

Subcommands (run from proof/verification/):
  python3 bg_spider_opt.py closedform            F == aobj_exact on the built tree, random + all small configs
  python3 bg_spider_opt.py symbolic              sympy: balance / leaf / absorption identities
  python3 bg_spider_opt.py dp 400                independent exact Pareto DP over the whole family, n<=400
  python3 bg_spider_opt.py search 4 3000 F.json  exhaustive per-n maximizer(s) over the family (24 workers)
  python3 bg_spider_opt.py asymptotic 2320       certificate: for all n >= N*, R_inf(n) is the unique maximizer
  python3 bg_spider_opt.py rule F.json           compare the search table with the stated optimal rule
  python3 bg_spider_opt.py membership            n=4..100: family max == max over ALL trees (FrontierDP)

RESULT (2026-09-24; doc proof/docs/BG_SPIDER_OPTIMIZATION_2026-09-24.md):
  * exhaustive exact family optimum for n = 4..2400 (and 2401..4000 as a check); agrees with the independent
    Pareto DP (n <= 600) and, for n <= 100, with the all-tree maximum and maximizer set.
  * certificate `asymptotic 2320` is True (False at 2319, where R_inf is not optimal): for every n >= 2320 the
    unique maximizer is R_inf(n) = only 5-arms plus k6 = s sixes (s <= 4) or k4 = 11-s fours (s >= 5),
    s = 6(n-1) mod 11.
  * rule for n >= 244 (`rule_config`): R_inf except s=1, n<=333 (C=1, all 5-arms) and s in {2,3,4} with
    n <= 423 / 722 / 2319 (11-s fours).  Table for n <= 243 in bg_spider_opt_4_2400.json.
conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import random
import sys
from fractions import Fraction as Fr
from multiprocessing import Pool

H = Fr(3, 2)


# ============================================================================ closed form
def alpha(j):
    return Fr(4 * j + 3, 3 * (j + 1))


def bj(j):
    return Fr(3, 4 * j + 3)


def g_arm(j):
    return H ** j * alpha(j)


def F_exact(C, arms):
    """arms: dict j -> count (j = 0 is a leaf).  Exact closed form."""
    D = C + sum(arms.values())
    if D == 0:
        return Fr(1)
    G = H ** C
    R = Fr(C, 3)
    for j, k in arms.items():
        if k:
            G *= g_arm(j) ** k
            R += k * bj(j)
    return G * (D + R) / D


def n_of(C, arms):
    return 1 + 2 * C + sum(k * (2 * j + 1) for j, k in arms.items())


def label(C, arms):
    """Table notation of BG_HWH_COVERAGE_LARGE_N (e.g. L0C7A[6, 6, 5]); compact (L0C0A{5:210,4:1}) if > 12 arms."""
    L = arms.get(0, 0)
    A = sorted((j for j, k in arms.items() if j > 0 for _ in range(k)), reverse=True)
    if len(A) > 12:
        return f"L{L}C{C}A{{" + ",".join(f"{j}:{arms[j]}" for j in sorted(arms, reverse=True) if j > 0) + "}"
    return f"L{L}C{C}" + (f"A{A}" if A else "")


def build_tree(C, arms):
    edges = []
    cnt = [1]

    def new(p):
        v = cnt[0]
        cnt[0] += 1
        edges.append((p, v))
        return v

    for _ in range(C):
        new(new(0))
    for j, k in sorted(arms.items()):
        for _ in range(k):
            a = new(0)
            for _ in range(j):
                new(new(a))
    adj = [[] for _ in range(cnt[0])]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def run_closedform():
    from hwh_coverage_large_n import aobj_exact
    cnt = 0
    # every configuration with n <= 22
    def gen(n_left, jmin, C, arms):
        yield C, dict(arms)
        for j in range(jmin, n_left):
            if 2 * j + 1 <= n_left:
                arms[j] = arms.get(j, 0) + 1
                yield from gen(n_left - 2 * j - 1, j, C, arms)
                arms[j] -= 1
                if not arms[j]:
                    del arms[j]
    for n in range(2, 23):
        for C in range(0, (n - 1) // 2 + 1):
            for C2, arms in gen(n - 1 - 2 * C, 0, C, {}):
                if n_of(C2, arms) != n:
                    continue
                adj = build_tree(C2, arms)
                assert len(adj) == n
                assert aobj_exact(adj) == F_exact(C2, arms), (C2, arms)
                cnt += 1
    small = cnt
    rng = random.Random(1)
    for _ in range(3000):
        C = rng.randint(0, 8)
        arms = {}
        for _ in range(rng.randint(0, 6)):
            j = rng.randint(0, 9)
            arms[j] = arms.get(j, 0) + 1
        if C + sum(arms.values()) == 0:
            continue
        adj = build_tree(C, arms)
        assert aobj_exact(adj) == F_exact(C, arms)
        cnt += 1
    print(f"[closedform] F_exact == aobj_exact(tree) on {cnt} configurations "
          f"(all {small} with n <= 22, plus {cnt - small} random with C <= 8, <= 6 arms of size <= 9)")


# ============================================================================ symbolic identities
def run_symbolic():
    from sympy import Rational, symbols, together, fraction, factor, expand, simplify
    j, k, c, D0, R0 = symbols('j k c D0 R0')
    al = lambda x: (4 * x + 3) / (3 * (x + 1))
    b = lambda x: Rational(3) / (4 * x + 3)
    # balance: Q_c(u,v) = alpha_u alpha_v (c + b_u + b_v), c = D + R0 (D = total children count)
    Q = lambda x, y: al(x) * al(y) * (c + b(x) + b(y))
    lhs = Q(j - 1, k + 1) - Q(j, k)
    rhs = (j - k - 1) * ((c - 3) * (4 * j + 4 * k + 7) + 3) / (9 * (k + 1) * (k + 2) * j * (j + 1))
    assert simplify(lhs - rhs) == 0
    print("[symbolic] balance: Q(j-1,k+1) - Q(j,k) = (j-k-1)((c-3)(4j+4k+7)+3) / (9(k+1)(k+2)j(j+1))  OK")
    # F(new)/F(old) for the balance move equals Q(j-1,k+1)/Q(j,k) (same D, same other children)
    # leaf pair: A0+A0 -> P, rest (D0, R0):  3/2 (D0+1+R0+1/3)(D0+2) - (D0+2+R0+2)(D0+1)
    e1 = Rational(3, 2) * (D0 + 1 + R0 + Rational(1, 3)) * (D0 + 2) - (D0 + 2 + R0 + 2) * (D0 + 1)
    assert simplify(e1 - (D0 ** 2 + D0 * R0 + 4 * R0) / 2) == 0
    print("[symbolic] leaves: [F(P+rest) - F(A0+A0+rest)] * D(D-1)/G = (D0^2 + D0 R0 + 4 R0)/2 >= 0  OK")
    # cherry absorption P + A_j -> A_{j+1}
    e2 = al(j + 1) * (D0 + 1 + R0 + b(j + 1)) * (D0 + 2) - al(j) * (D0 + 2 + R0 + Rational(1, 3) + b(j)) * (D0 + 1)
    num = 3 * D0 ** 2 + D0 * (3 * R0 - 4 * j ** 2 - 11 * j - 6) + R0 * (12 * j ** 2 + 33 * j + 24) - 4 * j ** 2 - 2 * j
    assert simplify(e2 - num / (9 * (j + 1) * (j + 2))) == 0
    print("[symbolic] absorption P+A_j -> A_{j+1} improves iff "
          "3D0^2 + D0(3R0 - 4j^2 - 11j - 6) + R0(12j^2+33j+24) - 4j^2 - 2j > 0  OK")


# ============================================================================ independent Pareto DP
def run_dp(nmax):
    from hwh_coverage_large_n import _prune
    types = ['P'] + list(range(0, nmax))
    item = lambda t: (2, H, Fr(1, 3)) if t == 'P' else (2 * t + 1, g_arm(t), bj(t))
    types = [t for t in types if item(t)[0] <= nmax - 1]
    states = {(0, 0): [(Fr(1), Fr(0), ())]}
    for t in types:
        c, g, r = item(t)
        for s in range(0, nmax - c):
            for k in range(0, s + 1):
                src = states.get((k, s))
                if not src:
                    continue
                key = (k + 1, s + c)
                dst = states.setdefault(key, [])
                dst.extend((G * g, R + r, rep + (t,)) for G, R, rep in src)
                states[key] = _prune(dst, k + 1)
    best = {}
    for (k, s), pts in states.items():
        if k == 0:
            continue
        for G, R, rep in pts:
            v = G * (k + R) / k
            n = s + 1
            if n not in best or v > best[n][0]:
                best[n] = (v, [rep])
            elif v == best[n][0]:
                best[n][1].append(rep)
    out = {}
    for n in range(2, nmax + 1):
        v, reps = best[n]
        labs = set()
        for rep in reps:
            C = rep.count('P')
            arms = {}
            for t in rep:
                if t != 'P':
                    arms[t] = arms.get(t, 0) + 1
            assert F_exact(C, arms) == v
            labs.add(label(C, arms))
        out[n] = (v, sorted(labs))
    return out


# ============================================================================ exhaustive search
LN15 = math.log(1.5)
_LA = [j * LN15 + math.log((4 * j + 3) / (3 * (j + 1))) for j in range(0, 6000)]
_B = [3 / (4 * j + 3) for j in range(0, 6000)]
MARGIN = 1e-9


def configs_D_le_2(n):
    """All configurations with D <= 2 at size n, as (C, arms)."""
    out = []
    N = n - 1
    types = [('P', 2)] + [(j, 2 * j + 1) for j in range(0, N + 1) if 2 * j + 1 <= N]
    for t, c in types:
        if c == N:
            out.append((1, {}) if t == 'P' else (0, {t: 1}))
    for i, (t1, c1) in enumerate(types):
        for t2, c2 in types[i:]:
            if c1 + c2 == N:
                C = (t1 == 'P') + (t2 == 'P')
                arms = {}
                for t in (t1, t2):
                    if t != 'P':
                        arms[t] = arms.get(t, 0) + 1
                out.append((C, arms))
    return out


def balanced_float(n):
    """Yield (logF, C, m, s, t) for every balanced configuration with D >= 3 (float)."""
    import numpy as np
    LA = np.array(_LA)
    Bv = np.array(_B)
    rows = []
    for C in range(0, (n - 1) // 2 + 1):
        V = n - 1 - 2 * C
        if V == 0:
            if C >= 3:
                rows.append((C * LN15 + math.log1p((C / 3) / C), C, 0, 0, 0))
            continue
        m = np.arange(1, V + 1)
        m = m[((V - m) % 2 == 0) & (C + m >= 3)]
        if m.size == 0:
            continue
        J = (V - m) // 2
        s = J // m
        t = J % m
        lg = (m - t) * LA[s] + t * LA[np.minimum(s + 1, len(LA) - 1)]
        R = C / 3 + (m - t) * Bv[s] + t * Bv[np.minimum(s + 1, len(Bv) - 1)]
        D = C + m
        v = C * LN15 + lg + np.log1p(R / D)
        rows.append((v, C, m, s, t))
    return rows


def flog(C, arms):
    """float log F (prefilter only)."""
    D = C + sum(arms.values())
    R = C / 3 + sum(k * _B[j] for j, k in arms.items())
    return C * LN15 + sum(k * _LA[j] for j, k in arms.items()) + math.log1p(R / D)


def solve_n(n):
    """Exact maximum of F over the whole family at size n (uses the balance lemma for D >= 3).
    Returns (n, max, maximizers, log gap to the best non-maximizer)."""
    import numpy as np
    near = []                      # (float logF, C, arms) within 0.1 of the float max
    flat = []
    for C, arms in configs_D_le_2(n):
        flat.append((flog(C, arms), C, arms))
    rows = balanced_float(n)
    fmax = max([f[0] for f in flat] + [r[0] if isinstance(r[0], float) else float(r[0].max()) for r in rows])
    near = [f for f in flat if f[0] >= fmax - 0.1]
    for v, C, m, s, t in rows:
        if isinstance(v, float):
            if v >= fmax - 0.1:
                near.append((v, C, {}))
            continue
        for i in np.nonzero(v >= fmax - 0.1)[0]:
            mm, ss, tt = int(m[i]), int(s[i]), int(t[i])
            arms = {}
            if mm - tt:
                arms[ss] = mm - tt
            if tt:
                arms[ss + 1] = tt
            near.append((float(v[i]), C, arms))
    exact = [(F_exact(C, arms), C, arms) for v, C, arms in near if v >= fmax - MARGIN]
    top = max(e[0] for e in exact)
    winners, seen = [], set()
    for v, C, arms in exact:
        if v == top and label(C, arms) not in seen:
            seen.add(label(C, arms))
            winners.append((C, arms))
    lesser_exact = [e[0] for e in exact if e[0] < top]
    lesser_float = [v for v, C, arms in near if v < fmax - MARGIN]
    ltop = math.log(top) if top < Fr(10) ** 300 else fmax
    cand = []
    if lesser_exact:
        cand.append(ltop - (math.log(max(lesser_exact)) if max(lesser_exact) < Fr(10) ** 300 else fmax))
    if lesser_float:
        cand.append(fmax - max(lesser_float))
    gap = min(cand) if cand else 0.1
    return n, top, winners, gap


def run_search(a, b, out_path, workers=24):
    res = {}
    with Pool(workers) as p:
        for n, top, winners, gap in p.imap(solve_n, range(a, b + 1), chunksize=4):
            res[n] = {"max_float": float(top) if top < Fr(10) ** 300 else None,
                      "max_exact": f"{top.numerator}/{top.denominator}" if n <= 120 else None,
                      "maximizers": [{"C": C, "arms": {str(j): k for j, k in sorted(arms.items())},
                                      "label": label(C, arms)} for C, arms in winners],
                      "log_gap_to_next": gap}
            if n % 250 == 0:
                print(f"[search] n={n} {[label(C, a_) for C, a_ in winners]} gap={gap:.3e}", flush=True)
    json.dump(res, open(out_path, "w"), indent=0)
    print(f"[search] wrote {out_path} for n={a}..{b}")
    return res


# ============================================================================ rigorous logs
def ln_iv(x, terms=60):
    """Rigorous rational enclosure (lo, hi) of ln(x), x > 0 rational."""
    x = Fr(x)
    if x == 1:
        return Fr(0), Fr(0)
    if x < 1:
        lo, hi = ln_iv(1 / x, terms)
        return -hi, -lo
    # reduce: ln x = k ln 2 + ln(x/2^k) with x/2^k in [1,2)
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    z = (x - 1) / (x + 1)          # in [0, 1/3)
    s = Fr(0)
    zp = z
    for i in range(terms):
        s += zp / (2 * i + 1)
        zp *= z * z
    lo = 2 * s
    hi = lo + 2 * zp / ((2 * terms + 1) * (1 - z * z))
    if k:
        l2lo, l2hi = ln2_iv(terms)
        return lo + k * l2lo, hi + k * l2hi
    return lo, hi


_LN2 = None


def ln2_iv(terms=60):
    global _LN2
    if _LN2 is None:
        z = Fr(1, 3)                 # ln 2 = 2 atanh(1/3)
        s = Fr(0)
        zp = z
        for i in range(terms):
            s += zp / (2 * i + 1)
            zp *= z * z
        _LN2 = (2 * s, 2 * s + 2 * zp / ((2 * terms + 1) * (1 - z * z)))
    return _LN2


class IV:
    """Closed rational interval arithmetic (only what the certificate needs)."""

    def __init__(self, lo, hi=None):
        self.lo = Fr(lo)
        self.hi = Fr(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, o):
        o = o if isinstance(o, IV) else IV(o)
        return IV(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, IV) else IV(o)
        return IV(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return IV(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, IV) else IV(o)
        ps = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return IV(min(ps), max(ps))

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = o if isinstance(o, IV) else IV(o)
        assert o.lo > 0 or o.hi < 0
        return self * IV(1 / o.hi, 1 / o.lo) if o.lo > 0 else self * IV(1 / o.hi, 1 / o.lo)

    def __repr__(self):
        return f"[{float(self.lo):.9g}, {float(self.hi):.9g}]"


def LN(x):
    return IV(*ln_iv(Fr(x)))


# ============================================================================ asymptotic certificate
def rinf(n):
    """The asymptotic optimal configuration R_inf(n) (L = C = 0; 5-arms plus k6 = s or k4 = 11 - s)."""
    s = (6 * (n - 1)) % 11
    if s <= 4:
        k4, k6 = 0, s
    else:
        k4, k6 = 11 - s, 0
    a5 = (n - 1 - 9 * k4 - 13 * k6)
    assert a5 % 11 == 0
    a5 //= 11
    arms = {j: k for j, k in ((4, k4), (5, a5), (6, k6)) if k}
    return 0, arms


def quad_neg_from(a, b, c, x0):
    """a x^2 + b x + c < 0 for every integer x >= x0 (exact)."""
    if a > 0 or (a == 0 and b > 0) or (a == 0 and b == 0 and c >= 0):
        return False
    # the quadratic is eventually decreasing; it is decreasing for x >= xv (a<0) or everywhere (a=0,b<0)
    if a < 0:
        xv = -b / (2 * a)
        top = max(x0, math.ceil(xv) + 1)
        for xi in range(x0, top + 1):
            if a * xi * xi + b * xi + c >= 0:
                return False
        return True
    return a * x0 * x0 + b * x0 + c < 0


def run_asymptotic(Nstar, verbose=True):
    """Certificate that for every n >= Nstar the unique maximizer over the family is R_inf(n).
    Uses: balance (D >= 3 maximizers are balanced), D <= 2 bound, rigorous log accounting."""
    ok = True
    g5 = g_arm(5)
    rho = LN(g5) / 11                                    # log-weight per vertex of A_5
    pen = {}
    pen['P'] = 2 * rho - LN(H)
    for j in range(0, 21):
        pen[j] = (2 * j + 1) * rho - LN(g_arm(j))
    assert pen['P'].lo > 0 and all(pen[j].lo > 0 for j in range(21) if j != 5)
    if verbose:
        print(f"[asym] rho = {rho}; pen P {pen['P']}, pen4 {pen[4]}, pen6 {pen[6]}, pen3 {pen[3]}, pen7 {pen[7]}")
    # per-vertex penalty rates mu_j = pen_j/(2j+1) >= mu for all j != 5, j >= 1 (and cherries >= muP)
    mu_small = min((pen[j] / (2 * j + 1)).lo for j in range(1, 21) if j != 5)
    # j >= 21: rho_j <= ln(1.5)/2 + (ln(4/3) - ln(1.5)/2)/(2j+1) <= that at j = 21
    tail_rate = (LN(H) / 2 + (LN(Fr(4, 3)) - LN(H) / 2) / 43)
    mu_tail = (rho - tail_rate).lo
    mu = min(mu_small, mu_tail)
    muP = (pen['P'] / 2).lo
    assert mu > 0 and mu_tail > 0
    if verbose:
        print(f"[asym] min per-vertex penalty over arms j != 5: mu = {float(mu):.6e} (j>=21 tail bound {float(mu_tail):.4e}); cherry {float(muP):.4e}")
    b4, b5, b6 = bj(4), bj(5), bj(6)
    # Pen(R_inf) by class
    Pinf = {}
    for s in range(11):
        Pinf[s] = (s * pen[6]) if s <= 4 else ((11 - s) * pen[4])
    Pbar = max(Pinf[s].hi for s in range(11))
    # (0) D <= 2 configurations: F <= 3 (3/2)^((n-2)/2) for n >= 6 (see doc); need
    #     ln F(R_inf) >= rho (n-1) - Pbar + ln(1 + b6) > ln 3 + (n-2)/2 ln 1.5
    lhs = (rho * (Nstar - 1) - Pbar + LN(1 + b6)) - (LN(3) + LN(H) * Fr(Nstar - 2, 2))
    step0 = lhs.lo > 0 and (rho - LN(H) / 2).lo > 0
    ok &= step0
    # (1) s = 0 (all arms are A_0/A_1): Pen >= (n-1) * min(muP, pen1/3, pen0) ; bracket <= 2
    Bud0 = Pbar + (LN(2) - LN(1 + b6)).hi
    rate0 = min(muP, (pen[1] / 3).lo, pen[0].lo)
    step1 = rate0 * (Nstar - 1) > Bud0
    ok &= step1
    # (2) s >= 1, s not in {4,5}: bracket <= 1 + 3/7 (every r <= 3/7), all arms have size != 5
    Bud1 = Pbar + (LN(Fr(10, 7)) - LN(1 + b6)).hi
    step2 = min(mu, muP) * (Nstar - 1) > Bud1
    ok &= step2
    Cmax1 = math.floor(Bud1 / pen['P'].lo)
    if verbose:
        print(f"[asym] Pbar={float(Pbar):.6f}  step0 (D<=2 beaten) {step0}  step1 (s=0) {step1}  "
              f"step2 (s in {{4,5}}: need (n-1)*{float(min(mu, muP)):.4e} > {float(Bud1):.4f}) {step2}  C <= {Cmax1}")
    # (3) s in {4,5}: D >= m >= (n-1-2C)/13.  Refined budget per class.
    Dlo = Fr(Nstar - 1 - 2 * Cmax1, 13)
    Dinf_lo = Fr(Nstar - 1, 13)
    eP = (Fr(1, 3) - b5) / (Dlo * (1 + b5))
    e4 = (b4 - b5) / (Dlo * (1 + b5))
    y = 4 * (b5 - b6) / (Dinf_lo * (1 + b5))
    corr = y / (1 - y)
    cP = pen['P'].lo - eP
    c4 = pen[4].lo - e4
    c6 = pen[6].lo
    assert cP > 0 and c4 > 0
    residual = {}
    for s in range(11):
        bud = Pinf[s].hi + corr
        lst = []
        for C in range(0, math.floor(bud / cP) + 1):
            for k4 in range(0, math.floor((bud - C * cP) / c4) + 1):
                for k6 in range(0, math.floor((bud - C * cP - k4 * c4) / c6) + 1):
                    if k4 and k6:
                        continue           # balanced: sizes {4,5} or {5,6}
                    if (2 * (C + k6 - k4) - s * 2 * 1) % 11:     # 2(C+k6-k4) == n-1 == 2s (mod 11)
                        continue
                    if C * cP + k4 * c4 + k6 * c6 <= bud:
                        lst.append((C, k4, k6))
        residual[s] = lst
    # (4) exact comparison of every residual candidate with R_inf, for all n >= Nstar in the class
    cmp_ok = True
    report = []
    for s in range(11):
        k4i, k6i = (0, s) if s <= 4 else (11 - s, 0)
        for (C, k4, k6) in residual[s]:
            if (C, k4, k6) == (0, k4i, k6i):
                continue
            # n = 11 N + 1 + 9 k4i + 13 k6i, N = a5(R_inf);  a5(Z) = N + d
            num = 9 * k4i + 13 * k6i - 2 * C - 9 * k4 - 13 * k6
            assert num % 11 == 0
            d = num // 11
            K = H ** C * g_arm(4) ** (k4 - k4i) * g_arm(6) ** (k6 - k6i) * g5 ** d
            # D_Z = N + (C + k4 + k6 + d), R_Z = b5 N + (C/3 + k4 b4 + k6 b6 + d b5)
            dz0 = C + k4 + k6 + d
            rz0 = Fr(C, 3) + k4 * b4 + k6 * b6 + d * b5
            dr0 = k4i + k6i
            rr0 = k4i * b4 + k6i * b6
            # sign of K (D_Z + R_Z) D_R - (D_R + R_R) D_Z  as a quadratic in N
            # (p1 N + q1)(N + dr0) with p1 = K(1+b5), q1 = K(dz0 + rz0);  (p2 N + q2)(N + dz0), p2 = 1+b5
            p1, q1 = K * (1 + b5), K * (dz0 + rz0)
            p2, q2 = (1 + b5), dr0 + rr0
            a = p1 - p2
            bq = p1 * dr0 + q1 - p2 * dz0 - q2
            cq = q1 * dr0 - q2 * dz0
            N0 = math.ceil(Fr(Nstar - 1 - 9 * k4i - 13 * k6i, 11))
            N0 = max(N0, -d if d < 0 else 0)
            good = quad_neg_from(a, bq, cq, N0)
            # also the last N where Z >= R_inf (threshold), for the report
            report.append((s, (C, k4, k6), float(K), good))
            cmp_ok &= good
    ok &= cmp_ok
    if verbose:
        for s in range(11):
            print(f"[asym] class s={s} (n-1 == 2s mod 11): R_inf k4={0 if s <= 4 else 11 - s} k6={s if s <= 4 else 0}; "
                  f"residual candidates {residual[s]}")
        bad = [r for r in report if not r[3]]
        print(f"[asym] exact comparisons: {len(report)} residual candidates, all strictly below R_inf for n >= {Nstar}: {cmp_ok}"
              + (f"  FAILURES {bad}" if bad else ""))
        print(f"[asym] CERTIFICATE for all n >= {Nstar}: {ok}")
    return ok


# ============================================================================ the rule
RULE_THRESH = {2: 423, 3: 722, 4: 2319}      # class s in {2,3,4}: k4 = 11-s fours up to this n, then k6 = s


def rule_config(n):
    """The optimal rule for n >= 244 (proved: exhaustive search for 244 <= n <= 2319, certificate for
    n >= 2320).  Returns the maximizer (C, arms), or None for n < 244 (the finite table applies)."""
    if n < 244:
        return None
    s = (6 * (n - 1)) % 11                     # n - 1 == 2s (mod 11)
    if s == 1 and n <= 333:
        C, k4, k6 = 1, 0, 0
    elif s in RULE_THRESH and n <= RULE_THRESH[s]:
        C, k4, k6 = 0, 11 - s, 0
    else:
        C, k4, k6 = (0, 0, s) if s <= 4 else (0, 11 - s, 0)
    a5 = n - 1 - 2 * C - 9 * k4 - 13 * k6
    assert a5 % 11 == 0 and a5 > 0
    return C, {j: k for j, k in ((4, k4), (5, a5 // 11), (6, k6)) if k}


def in_candidates(C, arms):
    """Cand(n): C <= 8 cherries, all arms in {4,5,6}, at most 9 fours, at most 4 sixes, not both."""
    k4, k6 = arms.get(4, 0), arms.get(6, 0)
    return (C <= 8 and set(arms) <= {4, 5, 6} and k4 <= 9 and k6 <= 4 and not (k4 and k6))


def run_rule(path):
    res = json.load(open(path))
    mism, outside = [], []
    for n_s, row in res.items():
        n = int(n_s)
        got = sorted(m["label"] for m in row["maximizers"])
        if n >= 46:
            for m in row["maximizers"]:
                if not in_candidates(m["C"], {int(j): k for j, k in m["arms"].items()}):
                    outside.append((n, m["label"]))
        rc = rule_config(n)
        if rc is not None and [label(*rc)] != got:
            mism.append((n, label(*rc), got))
    ns = sorted(int(x) for x in res)
    print(f"[rule] n={ns[0]}..{ns[-1]}: closed-form rule (n >= 244) mismatches: {len(mism)} {mism[:5]}")
    print(f"[rule] n >= 46 maximizers outside Cand(n): {len(outside)} {outside[:5]}")


def run_membership():
    from hwh_coverage_large_n import FrontierDP, canon
    dp = FrontierDP(100, "all")
    bad = []
    for n in range(4, 101):
        mx, args = dp.top(n)
        _, top, winners, _ = solve_n(n)
        cs = {canon(build_tree(C, a)) for C, a in winners}
        if top != mx or cs != {canon(a) for a in args}:
            bad.append(n)
    print(f"[membership] n=4..100: family max == all-tree max and maximizer sets agree, except: {bad}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "closedform"
    if cmd == "closedform":
        run_closedform()
    elif cmd == "symbolic":
        run_symbolic()
    elif cmd == "dp":
        N = int(sys.argv[2])
        out = run_dp(N)
        for n in range(4, N + 1):
            print(n, float(out[n][0]), out[n][1])
    elif cmd == "search":
        run_search(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif cmd == "asymptotic":
        run_asymptotic(int(sys.argv[2]))
    elif cmd == "rule":
        run_rule(sys.argv[2])
    elif cmd == "membership":
        run_membership()
