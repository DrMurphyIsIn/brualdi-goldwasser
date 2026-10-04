"""Exact polynomial certificates for the kinked witness W2 on (0, lam_K], lam_K = 3/20 (t_K = 3/43).

On (0, lam_K] the best arm is A3 (lam_K < lam_3), so F = f_3 exactly. Every transcendental quantity is enclosed between
polynomials in t valid on [0, t_K] (Taylor with remainder), derived quantities get polynomial lower/upper bounds by
monotone combination, and each scalar condition is reduced to "a polynomial is > 0 on (0, t_K]", certified by exact
Sturm root counting after dividing out the power of t at 0.
Witness (theta2 = 4/5, Mcap = 14):
   h = max(0, sa (y - ydag), h2 + sb (y - y2), eps + kappa (y - yC)),  h2 = theta2 g(A2).
"""
import sys
import sympy as sp

t = sp.symbols('t', nonnegative=True)
tK = sp.Rational(3, 43)            # lam_K = 2 tK/(1 - tK) = 3/20
TH2 = sp.Rational(4, 5)
MCAP = 14
NT = int(sys.argv[1]) if len(sys.argv) > 1 else 5   # Taylor order
inv1mtK = 1 / (1 - tK)                                # bound for 1/(1-t) on [0,tK]


def log1p_lo(x, n=NT):
    n2 = n if n % 2 == 0 else n + 1
    return sum((-1) ** (k + 1) * x ** k / k for k in range(1, n2 + 1))


def log1p_hi(x, n=NT):
    n2 = n if n % 2 == 1 else n + 1
    return sum((-1) ** (k + 1) * x ** k / k for k in range(1, n2 + 1))


def mlog1m(x, n=NT):
    lo = sum(x ** k / k for k in range(1, n + 1))
    hi = lo + inv1mtK * x ** (n + 1) / (n + 1)
    return lo, hi


def exp_bounds(xlo, xhi, K=NT):
    # valid for 0 <= xlo <= x <= xhi <= 0.5 : e^x <= sum_{k<=K} x^k/k! + 2 x^{K+1}/(K+1)!
    lo = sum(xlo ** k / sp.factorial(k) for k in range(K + 1))
    hi = sum(xhi ** k / sp.factorial(k) for k in range(K + 1)) + 2 * xhi ** (K + 1) / sp.factorial(K + 1)
    return lo, hi


ell = mlog1m(t)
a3 = (log1p_lo(3 * t / 4), log1p_hi(3 * t / 4))
a2 = (log1p_lo(2 * t / 3), log1p_hi(2 * t / 3))
a45 = (log1p_lo(4 * t / 5), log1p_hi(4 * t / 5))

F = ((3 * ell[0] + a3[0]) / 7, (3 * ell[1] + a3[1]) / 7)          # f_3
eps = ((2 * a3[0] - ell[1]) / 7, (2 * a3[1] - ell[0]) / 7)          # 2 f_3 - ell
g2 = ((ell[0] + 5 * a3[0]) / 7 - a2[1], (ell[1] + 5 * a3[1]) / 7 - a2[0])   # 5 (f_3 - f_2)
h2 = (TH2 * g2[0], TH2 * g2[1])
E = exp_bounds(F[0], F[1])
kap = 2 * t / ((1 - t) * (3 + 2 * t))
y4 = 1 / (5 + 4 * t)


import cert


def certify(expr, name):
    return cert.certify(expr, t, 0, tK, name)


allok = True
# lam_K < lam_3 : G_3(tK) < 0, G_3 = 7 log(1+4t/5) - 9 log(1+3t/4) - log(1-t)
G3hi = 7 * a45[1] - 9 * a3[0] + ell[1]
v = G3hi.subs(t, tK)
print("G_3(t_K) <=", float(v), "-> lam_K < lam_3:", v < 0)
allok &= bool(v < 0)
# sanity: positivity of factors used in products
allok &= certify(eps[0] - h2[1], "aux: eps - h2 > 0")
allok &= certify(t - kap, "aux: t - kappa > 0 (y2 < yC)")
allok &= certify(F[0], "aux: F > 0")
allok &= certify(sp.Rational(1, 2) - F[1], "aux: F <= 1/2 (exp remainder)")
allok &= certify(g2[0], "aux: g(A2) > 0")
# T1: ydag < y2   <=>  kappa - (E - 1) > 0
allok &= certify(kap - (E[1] - 1), "T1: ydag < y(A2)")
# T2: convexity sa <= sb  <=> (eps-h2)(kappa-E+1) - h2 (t-kappa) >= 0
allok &= certify((eps[0] - h2[1]) * (kap - E[1] + 1) - h2[1] * (t - kap), "T2: sa <= sb")
# T4: sb <= lam y4 (1 - kappa y4)  <=>  (t-kappa) y4 (1-kappa y4) - (eps - h2) >= 0   (implies sb <= kappa)
allok &= certify((t - kap) * y4 * (1 - kap * y4) - (eps[1] - h2[0]), "T4: sb <= lam y4 (1 - kappa y4)")
# T5: M_a <= MCAP  <=>  h2 (1 + MCAP E) - (kappa - E + 1) >= 0
allok &= certify(h2[0] * (1 + MCAP * E[0]) - (kap - E[0] + 1), f"T5: M_a <= {MCAP}")
# T6: Ndag(m) for m <= MCAP-1 (binding at m = MCAP-1):  MCAP F - (MCAP-1)(E-1) >= 0
allok &= certify(MCAP * F[0] - (MCAP - 1) * (E[1] - 1), f"T6: Ndag(m), m <= {MCAP-1}")
for m in range(5, MCAP):
    allok &= certify(F[0] + m * h2[0] - kap * sp.Rational(m, m + 1), f"T7: N2(m={m})")
for m in range(5, MCAP):
    allok &= certify(F[0] + m * eps[0] - t * sp.Rational(m, m + 1), f"T8: NC(m={m})")
print("RESULT:", "ALL CERTIFIED" if allok else "SOME FAILED", f"(Taylor order {NT}, lam_K = 3/20, theta2 = 4/5)")
