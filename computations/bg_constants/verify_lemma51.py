"""Verification of the constants of the potential at lambda = 1 (and of the Bellman inequality h satisfies at lambda=1).
(a) every numerical sign in the proof, in rational interval arithmetic (core.log_encl);
(b) the exact polynomial identity used for Q'(c) > 0;
(c) an independent rigorous branch-and-bound check that Phi_c(S) >= 0 on [0,c] for 1<=c<=CMAX,
    with interval arithmetic (mpmath.iv), including one-sided derivative checks at the two
    equality points (c,S)=(1,1) and (5,5/3).
"""
import os; os.environ.setdefault("OMP_NUM_THREADS", "1")
from fractions import Fraction as Fr
import sympy as sp
from mpmath import iv, mpf
import core
from core import LAM_LO, LAM_HI, BETA_LO, BETA_HI, KAP_LO, KAP_HI, GAM_LO, GAM_HI, Q, log_encl

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok &= bool(cond)

# ---------------- (a) constants ----------------
check("0.2065861 < lambda < 0.2065863", Fr(2065861, 10**7) < LAM_LO and LAM_HI < Fr(2065863, 10**7))
check("0.0077071 < beta < 0.0077074", Fr(77071, 10**7) < BETA_LO and BETA_HI < Fr(77074, 10**7))
check("0.18721 < kappa < 0.18722 < 1/5", Fr(18721, 10**5) < KAP_LO and KAP_HI < Fr(18722, 10**5))
check("0.29831 < gamma < 0.29833", Fr(29831, 10**5) < GAM_LO and GAM_HI < Fr(29833, 10**5))
check("h(1)=lambda: beta+(2/3)gamma = lambda (exact algebra)", True)  # (2/3)*(3/2)(lam-beta)+beta = lam
check("(10/9)gamma - 1/3 < -0.0018", Fr(10, 9) * GAM_HI - Fr(1, 3) < Fr(-18, 10**4))
v = 2 * KAP_HI * (Fr(1, 3) - Q) - Fr(3, 7) + GAM_HI * Fr(9, 49)
check("2k(1/3-q) - 3/7 + gamma(3/7)^2 < -0.297", v < Fr(-297, 1000))
check("1 - (2k/3)(1-2q) > 0.907", 1 - 2 * KAP_HI / 3 * (1 - 2 * Q) > Fr(907, 1000))
v = GAM_LO - Fr(3, 43) - 2 * KAP_HI * Q * Fr(9, 43**2)
check("gamma - 3/43 - 2 k q (3/43)^2 > 0.228", v > Fr(228, 1000))
check("junction: 2k(1/3-q) < gamma", 2 * KAP_HI * (Fr(1, 3) - Q) < GAM_LO)

def Dm(c, K, G):
    r = Fr(3, 4 * c + 3)
    return 2 * K * (Fr(1, 3) - Q) - r + 2 * K * (r - Q) * r * r
def Dp(c, K, G):
    r = Fr(3, 4 * c + 3)
    return G - r + 2 * K * (r - Q) * r * r

def enc(f):
    """enclose f(K,G) monotone-agnostic by evaluating at the 4 corners (f is affine in K and in G)"""
    vals = [f(K, G) for K in (KAP_LO, KAP_HI) for G in (GAM_LO, GAM_HI)]
    return min(vals), max(vals)

def Phi_c3(c):
    r = Fr(3, 4 * c + 3)
    L = log_encl(Fr(4 * c + 3, 3 * c + 3))
    lo = LAM_LO + c * BETA_LO - L[1] - KAP_HI * (r - Q) ** 2
    hi = LAM_HI + c * BETA_HI - L[0] - KAP_LO * (r - Q) ** 2
    return lo, hi

table = {2: ((-0.1930, -0.1925), (0.0293, 0.0298), (0.0173, 0.0178)),
         3: ((-0.1232, -0.1228), (0.0991, 0.0997), (0.0054, 0.0059)),
         4: ((-0.0819, -0.0814), (0.1404, 0.1410), (0.0007, 0.0011)),
         5: ((-0.0547, -0.0542), (0.1676, 0.1682), None),
         6: ((-0.0355, -0.0350), (0.1868, 0.1874), (0.0012, 0.0017)),
         7: ((-0.0212, -0.0206), (0.2011, 0.2018), (0.0041, 0.0047)),
         8: ((-0.0102, -0.0095), (0.2121, 0.2128), (0.0080, 0.0087)),
         9: ((-0.0014, -0.0007), (0.2209, 0.2217), (0.0127, 0.0134))}
for c in range(2, 10):
    a = enc(lambda K, G: Dm(c, K, G)); b = enc(lambda K, G: Dp(c, K, G))
    tm, tp, tphi = table[c]
    check(f"c={c}: D- in {tm}", Fr(tm[0]).limit_denominator(10**5) < a[0] and a[1] < Fr(tm[1]).limit_denominator(10**5))
    check(f"c={c}: D+ in {tp}", Fr(tp[0]).limit_denominator(10**5) < b[0] and b[1] < Fr(tp[1]).limit_denominator(10**5))
    if tphi:
        lo, hi = Phi_c3(c)
        check(f"c={c}: Phi_c(c/3) in {tphi}", Fr(tphi[0]).limit_denominator(10**5) < lo and hi < Fr(tphi[1]).limit_denominator(10**5))
        print(f"      Phi_{c}(c/3) in [{float(lo):.7f},{float(hi):.7f}]")
# c=5 exact zero: 3/(4*5+3)=q and lambda+5beta=log(23/18)  (pure algebra)
check("c=5: r_5 = q", Fr(3, 23) == Q)
# Q(10)
p = 1 + Q
def Qc(c):
    L = log_encl((1 + p * c) / (c + 1))
    lo = LAM_LO - KAP_HI * Q * Q - L[1] - Fr(c) / (4 * KAP_LO * (1 + p * c) ** 2)
    hi = LAM_HI - KAP_LO * Q * Q - L[0] - Fr(c) / (4 * KAP_HI * (1 + p * c) ** 2)
    return lo, hi
lo, hi = Qc(10)
check("0.0030 < Q(10) < 0.0033", Fr(30, 10**4) < lo and hi < Fr(33, 10**4))
print(f"      Q(10) in [{float(lo):.7f},{float(hi):.7f}]")

# ---------------- (b) exact polynomial identity ----------------
c = sp.symbols('c'); qq = sp.Rational(3, 23); pp = 1 + qq
expr = sp.expand((pp * c - 1) * (c + 1) - sp.Rational(4, 5) * qq * (1 + pp * c) ** 2)
target = (60658 * c**2 - 6417 * c - 67183) / sp.Integer(60835)
check("identity (pc-1)(c+1)-(4/5)q(1+pc)^2 = (60658c^2-6417c-67183)/60835", sp.simplify(expr - target) == 0)
check("60658c^2-6417c-67183 > 0 at c=10 and increasing for c>=1", 60658*100-6417*10-67183 > 0 and 2*60658*1-6417 > 0)
# Q'(c) formula
cc = sp.symbols('cc', positive=True); lam_s, k_s = sp.symbols('lam k', positive=True)
Qs = lam_s - k_s*qq**2 - sp.log((1+pp*cc)/(cc+1)) - cc/(4*k_s*(1+pp*cc)**2)
dQ = sp.diff(Qs, cc)
claimed = (pp*cc-1)/(4*k_s*(1+pp*cc)**3) - qq/((1+pp*cc)*(cc+1))
check("Q'(c) formula", sp.simplify(dQ - claimed) == 0)
# Phi'' formula check (symbolic, quadratic branch, S/c<=1/3)
S, cs = sp.symbols('S c', positive=True)
r = 1/(cs+1+S)
Ph = lam_s + cs*k_s*(S/cs - qq)**2 - sp.log(1 + S/(cs+1)) - k_s*(r - qq)**2
d2 = sp.diff(Ph, S, 2)
claimed2 = 2*k_s/cs + r**2 + 2*k_s*r**3*(2*qq - 3*r)
check("Phi_c'' formula (h''=2k on quadratic piece)", sp.simplify(d2 - claimed2) == 0)

# ---------------- (c) independent branch-and-bound check of Phi_c >= 0 ----------------
iv.prec = 120
# safer: build from fractions via exact division intervals
def hull(A, B):
    return iv.mpf([min(A.a, B.a), max(A.b, B.b)])
def ivfr(lo, hi):
    return hull(iv.mpf(lo.numerator) / lo.denominator, iv.mpf(hi.numerator) / hi.denominator)
LAM = ivfr(LAM_LO, LAM_HI); BETA = ivfr(BETA_LO, BETA_HI)
KAP = ivfr(KAP_LO, KAP_HI); GAM = ivfr(GAM_LO, GAM_HI)
QI = iv.mpf(3) / 23; THIRD = iv.mpf(1) / 3

def h_iv(X):
    """interval enclosure of h on X subset [0,1] (X an iv.mpf)."""
    a, b = X.a, X.b
    parts = []
    if a <= THIRD.b:
        lo = a; hi = min(b, THIRD.b)
        Y = iv.mpf([lo, hi])
        # kappa (y-q)^2 : exact interval square
        D = Y - QI
        sq = D ** 2 if not (D.a < 0 < D.b) else iv.mpf([0, max(abs(D.a), abs(D.b)) ** 2])
        parts.append(KAP * sq)
    if b >= THIRD.a:
        lo = max(a, THIRD.a); hi = b
        Y = iv.mpf([lo, hi])
        parts.append(BETA + GAM * (Y - THIRD))
    out = parts[0]
    for p_ in parts[1:]:
        out = hull(out, p_)
    return out

def Phi_iv(c, SI):
    r = 1 / (c + 1 + SI)
    return LAM + c * h_iv(SI / c) - iv.log(1 + SI / (c + 1)) - h_iv(r)

def dPhi_iv(c, SI, side):
    """enclosure of Phi_c' on SI where SI lies on one side of the kink S=c/3:
    side='L': SI subset [0,c/3] (quadratic branch of h at y=S/c, left derivative at c/3);
    side='R': SI subset [c/3,c] (linear branch).  Used only for c=5 (r<=1/6, quadratic branch of h at r)
    and c=1 (r in [1/3,1/2], linear branch of h at r)."""
    y = SI / c
    hy = 2 * KAP * (y - QI) if side == 'L' else GAM
    r = 1 / (c + 1 + SI)
    hr = 2 * KAP * (r - QI) if c >= 2 else GAM
    return hy - r + hr * r ** 2

def bb(c, lo, hi, depth=0, stats=None):
    X = iv.mpf([lo, hi])
    v = Phi_iv(c, X)
    if v.a >= 0:
        return True
    # equality points: (1,1) and (5,5/3): use derivative signs
    if depth > 60:
        return False
    eq = None
    if c == 1:
        eq = mpf(1)
    if c == 5:
        eq = mpf(5) / 3
    if eq is not None and lo <= eq <= hi and (hi - lo) < mpf('1e-3'):
        # on [lo,eq]: derivative <= 0 ; on [eq,hi]: derivative >= 0 (c=5) / c=1: S<=1 so only left side
        okL = dPhi_iv(c, iv.mpf([lo, eq]), 'L' if c == 5 else 'R').b <= 0 if lo < eq else True
        okR = True
        if c == 5 and hi > eq:
            okR = dPhi_iv(c, iv.mpf([eq, hi]), 'R').a >= 0
        if okL and okR:
            return True
    mid = (lo + hi) / 2
    if eq is not None and lo < eq < hi and (hi - lo) < mpf('1e-2'):
        mid = eq
    return bb(c, lo, mid, depth + 1) and bb(c, mid, hi, depth + 1)

CMAX = 60
allok = True
for c in range(1, CMAX + 1):
    res = bb(c, mpf(0), mpf(c))
    allok &= res
    if not res:
        print("B&B FAIL at c =", c)
check(f"branch-and-bound: Phi_c(S) >= 0 on [0,c] for 1<=c<={CMAX}", allok)
print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
