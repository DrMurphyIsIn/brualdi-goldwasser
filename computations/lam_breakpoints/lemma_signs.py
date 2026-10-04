"""Sign check of the breakpoint lemma (lem:lam-bp) at its exact rational endpoints, in Arb ball arithmetic.

For (j, p, q) in {(3, 0.43050, 0.43051), (4, 0.87247, 0.87248), (5, 1.19239, 1.19240), (6, 1.43559, 1.43560)}
it checks f_{j+1}(p) < f_j(p) and f_{j+1}(q) > f_j(q), where
    f_j(lam) = [ j log(1 + lam/2) + log(1 + lam j y_c/(j+1)) ] / (2j+1),   y_c = 1/(2+lam),
the per-vertex log-weight of the arm A_j.  The endpoints are exact rationals; python-flint arb at 256 bits.
Usage: python3 lemma_signs.py
"""
from fractions import Fraction
from flint import arb, fmpq, ctx

ctx.prec = 256


def f(j, lam):
    yc = 1 / (2 + lam)
    return (j * (1 + lam / 2).log() + (1 + lam * j * yc / (j + 1)).log()) / (2 * j + 1)


ROWS = [(3, "0.43050", "0.43051"), (4, "0.87247", "0.87248"), (5, "1.19239", "1.19240"), (6, "1.43559", "1.43560")]
smallest = None
ok_all = True
for j, p, q in ROWS:
    for side, s in (("p", p), ("q", q)):
        fr = Fraction(s)
        lam = arb(fmpq(fr.numerator, fr.denominator))
        d = f(j + 1, lam) - f(j, lam)          # must be < 0 at p and > 0 at q
        ok = (d < 0) if side == "p" else (d > 0)
        ok_all = ok_all and ok
        mod = abs(d.mid())
        smallest = mod if smallest is None or mod < smallest else smallest
        print("j=%d  %s=%s  f_{j+1}-f_j = %s  %s" % (j, side, s, d.str(6, radius=False), "OK" if ok else "FAIL"))
print("smallest |f_{j+1}-f_j| at the endpoints: %s" % arb(smallest).str(3, radius=False))
print("ALL SIGNS VERIFIED" if ok_all else "SIGN CHECK FAILED")
