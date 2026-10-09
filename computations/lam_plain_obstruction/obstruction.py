"""Two-point obstruction for the PLAIN form of the convex-potential method (no plain witness for lam in [79/20, 10^6]).

If h is a plain witness then h >= 0, h(1) <= F, and Bellman at m = 1 gives, for 0 < x <= 1,
    h(x) - h(y2(x)) >= L_x - F,   y2(x) = 1/(2 + lam x),   L_x = log(1 + lam x/2).
For y2(a) < a < b < 1, convexity (slope from y2(a) to a <= slope from b to 1), h(1) <= F and
h(b) >= L_b - F + h(y2(b)) >= L_b - F give (L_a - F)/(a - y2(a)) <= (2F - L_b)/(1 - b). Hence NO plain witness
exists if
    margin(lam; a, b) = L_b + ((1 - b)/(a - y2(a))) (L_a - F) - 2F > 0.
In the cherry regime (lam >= 1+sqrt5) F = (1/2) log(1 + lam/2).

Part 1: six sample activities and lam = 79/20, at fixed rational (a, b).
Part 2: all lam in [79/20, 10^6] by adaptive bisection with lam an interval (mpmath.iv, outward rounding),
        (a, b) chosen per subinterval from a fixed menu of rationals, all with a > 1/2; all lam >= 10^6 analytically
        (by hand, not in this program).
Usage: python3 obstruction.py"""
from fractions import Fraction as Fr
from mpmath import iv, mpf
iv.dps = 40


def I(q):
    q = Fr(q)
    return iv.mpf(q.numerator) / q.denominator


def margin(lam, a, b):
    """lam: iv interval (or rational); a, b rationals. Returns an interval enclosure of the margin."""
    lam = lam if isinstance(lam, type(iv.mpf(1))) else I(lam)
    a, b = I(a), I(b)
    F = iv.log(1 + lam / 2) / 2
    y2 = 1 / (2 + lam * a)
    assert (a - y2).a > 0 and b.a < 1 and (b - a).a > 0
    La = iv.log(1 + lam * a / 2)
    Lb = iv.log(1 + lam * b / 2)
    return Lb + ((1 - b) / (a - y2)) * (La - F) - 2 * F


POINTS = [("41/10", "4/5", "59/60"), ("17/4", "4/5", "59/60"), ("43/10", "4/5", "59/60"),
          ("9/2", "47/60", "29/30"), ("5", "23/30", "14/15"), ("6", "11/15", "9/10"), ("79/20", "161/200", "999/1000")]

MENU = [(Fr(161, 200), Fr(999, 1000)), (Fr(4, 5), Fr(99, 100)), (Fr(4, 5), Fr(59, 60)), (Fr(3, 4), Fr(19, 20)),
        (Fr(7, 10), Fr(9, 10)), (Fr(13, 20), Fr(7, 8)), (Fr(3, 5), Fr(17, 20)), (Fr(11, 20), Fr(4, 5)),
        (Fr(51, 100), Fr(3, 4)), (Fr(51, 100), Fr(7, 10))]   # every a > 1/2: unrealisable single-child messages


def cover(lo, hi, maxn=200000):
    stack = [(Fr(lo), Fr(hi))]
    done = 0; worst = None
    while stack:
        p, q = stack.pop()
        lam = iv.mpf([I(p).a, I(q).b])   # outward enclosure of the exact rational interval [p, q]
        ok = False
        for a, b in MENU:
            assert a > Fr(1, 2)
            try:
                m = margin(lam, a, b)
            except AssertionError:
                continue
            if m.a > 0:
                ok = True
                if worst is None or m.a < worst[0]:
                    worst = (m.a, float(p), float(q), a, b)
                break
        if ok:
            done += 1
        else:
            assert q - p > Fr(1, 10 ** 12), ("cannot certify near", float(p))
            mid = (p + q) / 2
            stack += [(p, mid), (mid, q)]
        assert done < maxn
    return done, worst


if __name__ == "__main__":
    for lam, a, b in POINTS:
        m = margin(Fr(lam), Fr(a), Fr(b))
        print("lam=%-6s a=%-7s b=%-8s margin in [%s, %s]  %s" % (lam, a, b, iv.nstr(m.a, 8), iv.nstr(m.b, 8),
              "NO PLAIN WITNESS" if m.a > 0 else "not certified"))
    n, worst = cover(Fr(79, 20), Fr(10 ** 6))
    print("lam in [79/20, 10^6]: covered by %d interval certificates; smallest lower bound %s on [%.9g, %.9g] "
          "with (a,b)=(%s,%s)" % (n, iv.nstr(worst[0], 5), worst[1], worst[2], worst[3], worst[4]))
