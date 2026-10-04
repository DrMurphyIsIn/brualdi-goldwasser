"""Rigorous certification (interval arithmetic) of the results built on the potential h
 (paper: prop:bg-gap, prop:bg-high, lem:bg-rate, Psi_k of lem:bg-compare, and lem:bg-compare(ii)).
 B. non-atom gap:   g(R) >= h(x(R)) + DELTA0 for every non-atom branch R
 C. high degree:    root degree k>=24 and a non-atom branch  =>  Phi(T) <= log(26/23) - (DELTA0 - mu0^2/(4 kappa))
 D. rate lemma:     for each cap C<=22 (<=C children per vertex): lam-eta+sum H(x_i)-log(1+S/(c+1)) >= H(r),
                    H = h - eta_C w  (so g(R) >= eta_C |R| + H(x(R)))
 E/F/G. thresholds: max-degree-k trees (2<=k<=23): Phi(T) <= Psi_k - eta N; compare with explicit spiders.
"""
import os; os.environ.setdefault("OMP_NUM_THREADS", "1")
import math, json, sys
from fractions import Fraction as Fr
from mpmath import iv, mpf
from ivtools import *
from core import log_encl, LAM_LO, LAM_HI, KAP_LO, KAP_HI, Q, pi_rooted, CHERRY, LEAF, ARM, bval
from spider_table import parse

out = {}
def lo(x): return float(x.a)
def hi(x): return float(x.b)

# ---------------- B. non-atom gap ----------------
def PhiI(c, S):   # Phi_c at an exact point / interval S (eta = 0)
    SI = S if isinstance(S, iv.mpf) else F(S)
    return PhiH_iv(c, SI, 0)

def D_minus(c):
    r = F(Fr(3, 4 * c + 3))
    return 2 * KAP * (THIRD - QI) - r + 2 * KAP * (r - QI) * r ** 2
def D_plus(c):
    r = F(Fr(3, 4 * c + 3))
    return GAM - r + 2 * KAP * (r - QI) * r ** 2

def atom_slack(j):
    """total slack of atom: leaf 0, cherry 0, A_1: Phi_1(1/3), A_j (j>=2): Phi_j(j/3) (Jensen gap 0)"""
    if j == 'L' or j == 'C':
        return iv.mpf(0)
    return PhiI(j, Fr(j, 3))

def atom_x(j):
    return Fr(1) if j == 'L' else (Fr(1, 3) if j == 'C' else Fr(3, 4 * j + 3))

def w_c(c, x):
    """per-child penalty lower bound (2<=c<=9): kappa(1/3-x)^2+|D-|(1/3-x) (x<=1/3), D+(x-1/3) (x>=1/3)"""
    X = F(x)
    if x <= Fr(1, 3):
        return KAP * (THIRD - X) ** 2 + (-D_minus(c)) * (THIRD - X)
    return D_plus(c) * (X - THIRD)

J = 30
rows = []
for c in range(2, 10):
    assert D_minus(c).b < 0 < D_plus(c).a
    mc = PhiI(c, Fr(c, 3))
    cands = [('L', mc + w_c(c, Fr(1)))]
    for j in range(1, J + 1):
        cands.append((f'A{j}', mc + w_c(c, atom_x(j)) + atom_slack(j)))
    cands.append((f'A>{J}', mc + w_c(c, atom_x(J + 1))))   # tail: w_c increasing in j, s_j >= 0
    best = min(cands, key=lambda t: t[1].a)
    rows.append((c, best[0], best[1]))
c1 = PhiI(1, Fr(3, 7))          # c=1: child an arm, x<=3/7, Phi_1 decreasing
rows.append((1, 'A_j (Phi_1(3/7))', c1))
# c>=10: min_S Phi_c(S) >= Q(c) ; B&B for c=10,11,12
for c in (10, 11, 12):
    lb, ub = bb_lower(lambda X, c=c: PhiH_iv(c, X, 0), mpf(0), mpf(c), nmax=3000)
    rows.append((c, 'any', iv.mpf([lb, ub])))
p = 1 + Q
def Qc(c):
    L = log_encl((1 + p * c) / (c + 1))
    return LAM - KAP * F(Q) ** 2 - ivfr(L[0], L[1]) - F(c) / (4 * KAP * F(1 + p * c) ** 2)
rows.append(('>=13', 'any (Q(13))', Qc(13)))
print("B. non-atom gap: lower bounds by child count c of the lowest non-atom vertex")
for c, arg, v in rows:
    print(f"   c={c}: min over configs >= {lo(v):.6f}  (at {arg})")
DELTA0 = min(lo(v) for _, _, v in rows)
DELTA0_R = Fr(1426, 100000)
assert DELTA0 >= float(DELTA0_R), DELTA0
print(f"   DELTA0 = {DELTA0:.6f}  >= 0.01426   [true inf over searched branches: 0.014465 at [C^5,A4]]")
out['delta0'] = DELTA0

# ---------------- C. high degree ----------------
mu0 = Fr(23, 624)
def g_atom(j):
    b = LEAF if j == 'L' else (CHERRY if j == 'C' else ARM(j))
    Z, x, n = bval(b)
    L = log_encl(Z)
    return n * LAM - ivfr(L[0], L[1])
ok = True
for j in ['L', 'C', 1, 2, 3, 4]:
    marg = g_atom(j) - F(mu0) * (F(atom_x(j)) - QI)
    print(f"C. atom {j}: g - mu0 (x - q) >= {lo(marg):.3e}")
    ok &= marg.a > 0
lA4 = -g_atom(4)
assert lA4.a >= mpf(-1) / 960
Lg = log_encl(Fr(26, 23)); LOG2623 = ivfr(Lg[0], Lg[1])
gapC = F(DELTA0_R) - F(mu0) ** 2 / (4 * KAP)
print(f"C. DELTA0 - mu0^2/(4 kappa) >= {lo(gapC):.6f}  vs 10/960 = {10/960:.6f};  l(A4) >= {lo(lA4):.7f} >= -1/960")
ok &= gapC.a > mpf(10) / 960
assert ok
out['highdeg_margin'] = lo(gapC) - 10 / 960
BENCH = LOG2623 - F(Fr(10, 960))
print(f"   benchmark spider (N>=90): Phi >= log(26/23) - 10/960 >= {lo(BENCH):.6f}; "
      f"non-spider with a vertex of degree>=24: Phi <= {hi(LOG2623 - gapC):.6f}")

# ---------------- D. rate lemma ----------------
from rate_explore import best_eta, A as Afloat
S_TAN = 2 * KAP * (THIRD - QI)
etas = {}
for C in range(1, 23):
    e = best_eta(C, Afloat)
    etas[C] = Fr(int(e * 0.99 * 1e7), 10**7)
print("D. rate lemma: per cap C, eta_C and verification of Phi^H_c >= 0 on [0,c] for all c<=C")
certD = {}
for C in range(1, 23):
    eta = etas[C]
    conv = F(eta) * (AWI - F(Fr(3, 2))) <= GAM - S_TAN
    assert (F(eta) * (AWI - F(Fr(3, 2)))).b <= (GAM - S_TAN).a, "H not convex"
    allok = True
    for c in range(1, C + 1):
        eq = ()
        if c == 1: eq = (mpf(1),)
        if c == 5: eq = (mpf(5) / 3,)
        def deriv(I, side, c=c, eta=eta):
            if c == 1:
                return dPhiH_iv(1, I, eta, 'L')
            return dPhiH_iv(c, I, eta, 'Q' if side == 'left' else 'L')
        res = bb_min_ge0(lambda X, c=c, eta=eta: PhiH_iv(c, X, eta), mpf(0), mpf(c), eq, deriv)
        allok &= res
        if not res:
            print("   FAIL", C, c)
    certD[C] = allok
    print(f"   cap C={C:2d}: eta = {float(eta):.7f} ({eta})  verified={allok}", flush=True)
assert all(certD.values())
out['etas'] = {C: str(e) for C, e in etas.items()}

# ---------------- E. root bound (Jensen) ----------------
Psi = {}
for k in range(2, 24):
    eta = etas[k - 1]
    ub, _ = bb_upper(lambda Y, k=k, eta=eta: iv.log(1 + Y) - k * H_iv(Y, eta), mpf(0), mpf(1), nmax=3000)
    Psi[k] = ub
print("E. Psi_k^eta upper bounds:", {k: round(float(v), 5) for k, v in Psi.items()})

# ---------------- F. comparison spiders ----------------
rows_t = parse()
PHI_LO = {}
for n, ch in rows_t.items():
    pz = pi_rooted(ch); L = log_encl(pz)
    PHI_LO[n] = float(L[0] - (n - 1) * LAM_HI) - 1e-12
BENCH_LO = float(BENCH.a)
def phis_lo(n):
    if n in PHI_LO: return PHI_LO[n]
    if n < 4: return -1e9
    assert n - 1 >= 90
    return BENCH_LO

# ---------------- G. thresholds ----------------
thr = {}
for k in range(2, 24):
    eta = float(etas[k - 1]); P = float(Psi[k])
    bad = [N for N in range(k, 20000) if P - eta * N >= phis_lo(N + 1)]
    thr[k] = (max(bad) + 2) if bad else k + 1
print("G. thresholds n0(k) (every tree of max degree k with n >= n0(k) vertices has Phi < Phi(best spider)):")
print("   " + ", ".join(f"k={k}:{v}" for k, v in thr.items()))
n0 = max(thr.values())
print(f"   => for n >= {n0}: every maximizer has max degree >= 24, hence (C, n-1>=90) is a spider centred at it.")
out['thresholds'] = thr; out['n0'] = n0
json.dump(out, open('certify_out.json', 'w'), indent=1, default=str)
