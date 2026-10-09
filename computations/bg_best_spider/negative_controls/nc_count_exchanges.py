"""Negative control for the count exchanges: xi = Xi + 10^-3 must be rejected.

For each of the twelve exchanges of the table, the check of ../tab.py (function `row`, imported unchanged)
computes the exact ratio Xi, asserts xi <= Xi in exact arithmetic, and expands the two quadratics
Delta_xi(X, y_lo X) and Delta_xi(X, y_hi X). The statement then needs their sign statements: positive for all
X >= 0 in the first ten rows, and for X >= 15 resp. X >= 16 in the last two (exchanges 11 A_4 -> 9 A_5 and
9 P -> 2 A_4). The check of a row passes iff both hold.

Positive control: xi = the exact decimal of the table (passes in every row).
Negative control: xi = Xi + 1/1000 (exact rational; must fail in every row).

Note. Delta_xi is increasing in xi (its xi-term has the positive factor (m_N + D_0 + R_N + R_0)(m_O + D_0)),
so the sign statements remain true for xi > Xi; the perturbation is caught by the exact comparison
xi <= Xi alone. This script reports the sign statements for the perturbed xi as well, to make that visible.

Usage: python3 nc_count_exchanges.py
"""
import contextlib
import io
import os
import sys
import time
from pathlib import Path

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

with contextlib.redirect_stdout(io.StringIO()):   # tab.py prints the table body when imported
    import tab
from sympy import Rational, Poly, symbols, prod

X = symbols('X')

# the twelve rows of the table: (name, old, new, y_lo, y_hi, xi, X0 for the sign statement); as in ../tab.py
ROWS = [(f"11A{j}->{2 * j + 1}A5", [j] * 11, [5] * (2 * j + 1), 0, 1, xi, 0)
        for j, xi in [(1, '1937/1000'), (2, '158/125'), (3, '537/500'), (7, '1051/1000'), (8, '11/10'),
                      (9, '1161/1000'), (10, '1231/1000'), (11, '164/125'), (12, '1403/1000')]]
ROWS += [("11A6->13A5", [6] * 11, [5] * 13, 0, Rational(1, 3), '1271/1250', 0),
         ("11A4->9A5", [4] * 11, [5] * 9, Rational(1, 9), 1, '10113/10000', 15),
         ("9P->2A4", ['P'] * 9, [4] * 2, Rational(1, 9), 1, '1069/1000', 16)]


def Xi(old, new):
    return prod([tab.g(c) for c in new]) / prod([tab.g(c) for c in old])


def positive_from(coeffs, X0):
    """the quadratic with integer coefficients `coeffs` is > 0 for every real X >= X0"""
    p = Poly(coeffs, X)
    if p.eval(X0) <= 0:
        return False
    return all(r < X0 for r in p.real_roots()) and p.LC() > 0


def check_row(name, old, new, lo, hi, xi, X0):
    """returns (xi <= Xi, sign statements hold); the first via tab.row's exact assertion"""
    try:
        _, _, _, qs = tab.row(name, old, new, lo, hi, xi)
        cmp_ok = True
    except AssertionError:
        cmp_ok = False
        # same expansion as tab.row, without its assertion, for the sign report
        gam = Rational(xi)
        a, b = len(old), len(new)
        RO = sum(tab.r(c) for c in old)
        RN = sum(tab.r(c) for c in new)
        qs = []
        for lam in (lo, hi):
            D = (gam * (b + X + RN + lam * X) * (a + X) - (a + X + RO + lam * X) * (b + X)).expand()
            qs.append(Poly(D, X).all_coeffs())
    sign_ok = all(positive_from(c, X0) for c in qs)
    return cmp_ok, sign_ok


if __name__ == "__main__":
    t0 = time.time()
    ok = True
    print("[control 5] count exchanges: xi from the table (PASS expected) and xi = Xi + 1/1000 (FAIL expected)")
    print("   exchange      Xi          xi (table)  xi<=Xi signs  row     | xi=Xi+1e-3  xi<=Xi signs  row")
    for name, old, new, lo, hi, xi, X0 in ROWS:
        XI = Xi(old, new)
        c0, s0 = check_row(name, old, new, lo, hi, xi, X0)
        xp = XI + Rational(1, 1000)
        c1, s1 = check_row(name, old, new, lo, hi, xp, X0)
        r0 = c0 and s0
        r1 = c1 and s1
        ok &= r0 and not r1 and not c1
        print(f"   {name:12s}  {float(XI):.6f}  {xi:>11s} {str(c0):6s} {str(s0):6s} {'PASS' if r0 else 'FAIL'}    "
              f"| {float(xp):.6f}    {str(c1):6s} {str(s1):6s} {'PASS' if r1 else 'FAIL'}")
    print(f"\nruntime {time.time() - t0:.1f} s")
    print("ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED" if ok else "SOME NEGATIVE CONTROL DID NOT BEHAVE AS EXPECTED")
    sys.exit(0 if ok else 1)
