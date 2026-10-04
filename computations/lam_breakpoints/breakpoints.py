"""Rigorous enclosures of the breakpoints lam_j (A_j and A_{j+1} tie), j = 3..30.
By the single-crossing lemma G_j has exactly one zero in t in (0,1), so a sign change of
f_j - f_{j+1} between two rationals (checked in interval arithmetic) encloses lam_j."""
import mpmath as mp
from mpmath import iv
from rates import breakpoint
iv.dps = 50; mp.mp.dps = 50
def g(j, lam):  # f_j - f_{j+1} in interval arithmetic, lam an iv number
    c = 1 + lam / 2; yc = 1 / (2 + lam)
    fj = (j * iv.log(c) + iv.log(1 + lam * j * yc / (j + 1))) / (2 * j + 1)
    k = j + 1
    fk = (k * iv.log(c) + iv.log(1 + lam * k * yc / (k + 1))) / (2 * k + 1)
    return fj - fk
print("j   lam_j enclosure (width 1e-18)")
for j in range(3, 31):
    b = breakpoint(j)
    lo = iv.mpf(mp.nstr(b - mp.mpf('1e-18'), 30)); hi = iv.mpf(mp.nstr(b + mp.mpf('1e-18'), 30))
    glo, ghi = g(j, lo), g(j, hi)
    ok = glo.a > 0 and ghi.b < 0      # A_j better just below, A_{j+1} better just above
    print("%2d  [%s, %s]  %s" % (j, mp.nstr(lo.a, 20), mp.nstr(hi.b, 20), "VERIFIED" if ok else "FAIL"))
