"""Hand-checkable positivity of a low-degree polynomial on [a,b]: split into pieces on which all Bernstein
coefficients are positive (exact rationals). Prints the pieces and the smallest Bernstein coefficient."""
import sympy as sp
from fractions import Fraction as Fr
t = sp.symbols('t')
def bern(P, a, b):
    n = sp.Poly(P, t).degree()
    u = sp.symbols('u')
    Q = sp.Poly(sp.expand(P.subs(t, a + (b - a)*u)), u)
    c = [Q.coeff_monomial(u**k) for k in range(n + 1)]
    return [sum(sp.binomial(i, k)/sp.binomial(n, k)*c[k] for k in range(i + 1)) for i in range(n + 1)]
def split(P, a, b, depth=0):
    B = bern(P, a, b)
    if min(B) > 0: return [(a, b, min(B))]
    if depth > 12: raise RuntimeError
    m = (a + b)/2
    return split(P, a, m, depth + 1) + split(P, m, b, depth + 1)
if __name__ == "__main__":
    TM = sp.Rational(6181, 10000)
    P = 11*(1+t/2+sp.Rational(3,8)*t**2+sp.Rational(5,16)*t**3)*((1-t)*(3+2*t)*(5+4*t)-2*t) - 2*(5+4*t)**2*(1-t)*(3+2*t)
    print("C2' (S3) degree", sp.Poly(sp.expand(P), t).degree(), sp.Poly(sp.expand(P), t).all_coeffs())
    for a, b, m in split(sp.expand(P), sp.Integer(0), TM): print("   piece", a, b, "min Bernstein coeff", float(m))
    for name, P, a, b in [("C5 cubic", -5*t**3-14*t**2+128*t+160, 0, sp.Rational(32361,10000)),
                          ("C6 cubic", 2-t-2*t**2-t**3, 0, TM), ("C4", 8+6*t+3*t**2, 0, sp.Rational(32361,10000))]:
        print(name, [(str(x), str(y), float(m)) for x, y, m in split(sp.expand(P), sp.Integer(a), sp.Rational(b))])
