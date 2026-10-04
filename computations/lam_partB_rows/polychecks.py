"""Exact polynomial checks used in the hand proofs (sympy, exact rationals, Sturm root counting).
Each check: a polynomial P with rational coefficients must be > 0 on a closed interval [a,b] with rational ends
(or on the half-open interval as stated). We certify: P(a) > 0 (or P(a) = 0 with P(t)/t > 0 handled by dividing),
and P has no real root in [a,b] (sympy count_roots, which is exact for rational polynomials).
t-interval: 0 <= t <= 1/phi < 0.6181 = TMAX; we use TMAX = 6181/10000 (> 1/phi).
"""
import sympy as sp

t, s, lam = sp.symbols('t s lam', real=True)
TMAX = sp.Rational(6181, 10000)
assert TMAX > (sp.sqrt(5) - 1) / 2


from cert import certify


def positive_on(P, var, a, b, name, open_left=False):
    ok = certify(P, var, a, b, name)
    assert ok, name
    return ok


# (S2) y(A3) <= ydag from F >= f_3:   (4+3t)^8 (1-t)^4 - 4 (4+t-3t^2)^7 > 0 on (0, 1/phi]
P2 = (4 + 3 * t) ** 8 * (1 - t) ** 4 - 4 * (4 + t - 3 * t ** 2) ** 7
positive_on(P2, t, 0, TMAX, "S2: A3 message in the flat part", open_left=True)

# (F5) rho <= 1/2 is by calculus (derivative t(1+3t)/(2(1+t)^2(1-t)) >= 0); nothing to check.

# (S3) left-derivative condition at m = 4 with rho <= 1/2:
#   121((1-t)(3+2t)(5+4t) - 2t)^2 - 4(1-t)^3 (3+2t)^2 (5+4t)^4 > 0 on [0, 1/phi]
P3 = 121 * ((1 - t) * (3 + 2 * t) * (5 + 4 * t) - 2 * t) ** 2 - 4 * (1 - t) ** 3 * (3 + 2 * t) ** 2 * (5 + 4 * t) ** 4
positive_on(P3, t, 0, TMAX, "S3: s1 <= lam y4 (1 - kappa y4)")
# also the unsquared left side is positive: (1-t)(3+2t)(5+4t) - 2t > 0
positive_on((1 - t) * (3 + 2 * t) * (5 + 4 * t) - 2 * t, t, 0, TMAX, "S3 aux: 1 - kappa y4 > 0")

# (S4) with rho <= rhohat(t) = 1/2 - t/4 - 7t^2/12 + t^3/6, e^{3D} <= 1291/1000, t = 1 - s^2, sqrt(c) = 1/s:
#   (1291/1000) g(rhohat) t (1 + 1/s) <= (1+t)^2,  g(r) = r (1 - r/(8+6r))^3 (4+3r)
rh = sp.Rational(1, 2) - t / 4 - sp.Rational(7, 12) * t ** 2 + t ** 3 / 6
# rhohat in [0, 1/2] on [0, TMAX]
positive_on(rh, t, 0, TMAX, "S4 aux: rhohat > 0")
positive_on(sp.Rational(1, 2) - rh, t, 0, TMAX, "S4 aux: rhohat <= 1/2", open_left=True)
r = sp.symbols('r', positive=True)
g = r * (1 - r / (8 + 6 * r)) ** 3 * (4 + 3 * r)
gp = sp.together(sp.diff(g, r))
num, den = sp.fraction(gp)
positive_on(num, r, 0, sp.Rational(1, 2), "S4 aux: g increasing on [0,1/2]")
expr = (1 + t) ** 2 - sp.Rational(1291, 1000) * g.subs(r, rh) * t * (1 + 1 / s)
expr = expr.subs(t, 1 - s ** 2)
smin = sp.Rational(618, 1000)   # s = sqrt(1-t) >= sqrt(1 - 1/phi) = 1/phi > 0.618
positive_on(expr, s, smin, 1, "S4: u^2(u-eps) <= eps E (E-1)  [t = 1 - s^2]")

# exp bound: e^{3 Dmax} <= 1.291 with Dmax = log(4/3) + log(2/3)/2  (checked in high precision; and by hand:
# 3 Dmax = log((4/3)^3 (2/3)^{3/2}), so e^{6 Dmax} = (4/3)^6 (2/3)^3, checked exactly below)
import mpmath as mp
mp.mp.dps = 40
Dmax = mp.log(mp.mpf(4) / 3) + mp.log(mp.mpf(2) / 3) / 2
print("e^{3Dmax} =", mp.e ** (3 * Dmax), "<= 1.291:", mp.e ** (3 * Dmax) <= mp.mpf('1.291'))
# exact: e^{6 Dmax} = (4/3)^6 (2/3)^3 = 4096*8/(729*27) = 32768/19683; need <= 1.291^2
print("e^{6Dmax} = 32768/19683 =", sp.Rational(32768, 19683), "<= 1.291^2 =", sp.Rational(1291, 1000) ** 2,
      sp.Rational(32768, 19683) <= sp.Rational(1291, 1000) ** 2)

# (S5) m = 1:   8 + 6 lam + 3 lam^2 > 0 (trivial) and  -5 lam^3 - 14 lam^2 + 128 lam + 160 > 0 on [0, 3.2361]
LMAX = sp.Rational(32361, 10000)
assert LMAX > 1 + sp.sqrt(5)
positive_on(8 + 6 * lam + 3 * lam ** 2, lam, 0, LMAX, "S5: Phi(D1) lower bound > 0")
positive_on(-5 * lam ** 3 - 14 * lam ** 2 + 128 * lam + 160, lam, 0, LMAX, "S5: interior-minimum case")
# the case split cubic lam^3 + 4 lam^2 - 12 lam - 16 (sign of Phi'(D1)); report its root
print("root of lam^3+4lam^2-12lam-16:", [sp.N(x, 8) for x in sp.real_roots(lam ** 3 + 4 * lam ** 2 - 12 * lam - 16)])
# lam <= (1+t)(2+t) (B_{0,1} decreasing on [0,yC]):  2 - t - 2t^2 - t^3 > 0
positive_on(2 - t - 2 * t ** 2 - t ** 3, t, 0, TMAX, "m=1 monotonicity: 2 - t - 2t^2 - t^3 > 0")

# (S6) lam >= 2 (t in [1/2, 1/phi]):  (1/2)(-t/3 + 8t^2/9 + 4t^3/9) - t(2t-1)(1+t)/((1-t)(3+2t)^2) > 0
e6 = sp.Rational(1, 2) * (-t / 3 + sp.Rational(8, 9) * t ** 2 + sp.Rational(4, 9) * t ** 3) * (1 - t) * (3 + 2 * t) ** 2 \
     - t * (2 * t - 1) * (1 + t)
positive_on(e6, t, sp.Rational(1, 2), TMAX, "S6 (lam >= 2): -D(2) >= kappa (y2 - yC)")
# D(2) <= 0 for t >= (sqrt7-2)/2 :  (1-t)(1+2t/3)^2 <= 1  <=>  4t^2 + 8t - 3 >= 0
print("t_D2 = (sqrt7-2)/2 =", sp.N((sp.sqrt(7) - 2) / 2, 12), " lam_D2 =", sp.N(2 * ((sp.sqrt(7) - 2) / 2) / (1 - (sp.sqrt(7) - 2) / 2), 12))
print("ALL POLYNOMIAL CHECKS PASSED")
