"""Shared exact positivity certificate for a rational function of one variable on an interval.

certify(expr, var, a, b, name): expr is a sympy rational expression in var with rational coefficients.
 1. Write expr = P/Q (exact), strip the common power of var at var = 0 if a == 0 (records the order k).
 2. Check  sign(P(a) Q(a)) > 0  (after stripping) and that P and Q have no real root in [a, b]:
      (i) sympy Poly.count_roots (exact Sturm/real-root isolation over QQ),
     (ii) python-flint: integer polynomial, certified complex root enclosures (fmpz_poly.complex_roots);
          a root is counted in [a,b] if its enclosure meets [a,b] x {0}; any such root is a failure.
 3. A dense numeric sample (mpmath, 2001 points) as a sanity check.
Both (i) and (ii) must pass.
"""
import sympy as sp
import flint
import mpmath as mp


def _flint_no_root(P, var, a, b):
    # P: sympy Poly over QQ; return True if no root of P lies in [a,b] (certified enclosures)
    den = 1
    for c in P.all_coeffs():
        den = sp.ilcm(den, sp.Rational(c).q)
    coeffs = [int(sp.Rational(c) * den) for c in reversed(P.all_coeffs())]
    fp = flint.fmpz_poly(coeffs)
    if fp.degree() <= 0:
        return True
    fa = flint.arb(int(sp.Rational(a).p)) / int(sp.Rational(a).q)
    fb = flint.arb(int(sp.Rational(b).p)) / int(sp.Rational(b).q)
    for r, mult in fp.complex_roots():
        re, im = r.real, r.imag
        if im.contains(0) and (re.upper() >= fa.lower()) and (re.lower() <= fb.upper()):
            return False
    return True


def certify(expr, var, a, b, name, verbose=True):
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    P = sp.Poly(sp.expand(num), var)
    Q = sp.Poly(sp.expand(den), var)
    k = 0
    if a == 0:
        while P.eval(0) == 0 and not P.is_zero:
            P = sp.Poly(sp.cancel(P.as_expr() / var), var)
            k += 1
        while Q.eval(0) == 0:
            Q = sp.Poly(sp.cancel(Q.as_expr() / var), var)
            k -= 1
    s = (1 if P.eval(a) > 0 else -1) * (1 if Q.eval(a) > 0 else -1)
    ok1 = s > 0 and P.count_roots(a, b) == 0 and Q.count_roots(a, b) == 0
    ok2 = s > 0 and _flint_no_root(P, var, a, b) and _flint_no_root(Q, var, a, b)
    # numeric sanity
    mp.mp.dps = 30
    f = sp.lambdify(var, P.as_expr() / Q.as_expr(), 'mpmath')
    xs = [mp.mpf(a) + (mp.mpf(b) - mp.mpf(a)) * i / 2000 for i in range(2001)]
    mn = min(f(x) for x in xs)
    ok3 = mn > 0
    ok = ok1 and ok2 and ok3
    if verbose:
        print(f"{name:46s} deg(P)={P.degree():3d} ord_0={k:2d} min_sample={float(mn):+.3e}  sturm={ok1} flint={ok2} -> {'OK' if ok else 'FAIL'}")
    return ok
