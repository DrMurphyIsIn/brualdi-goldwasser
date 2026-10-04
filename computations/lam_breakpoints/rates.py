"""Arm rates f_j(lam) = log T(A_j) / (2j+1) and the breakpoints lam_j where A_j and A_{j+1} tie.
T(A_j) = c^j ((j+1) c + u j) / ((j+1) c),  u = lam/2, c = 1 + u.   Cherry rate: (1/2) log c.
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
import mpmath as mp
mp.mp.dps = 50


def logT(j, lam):
    u = mp.mpf(lam) / 2; c = 1 + u
    return j * mp.log(c) + mp.log(((j + 1) * c + u * j) / ((j + 1) * c))


def f(j, lam):
    return logT(j, lam) / (2 * j + 1)


def cherry_rate(lam):
    return mp.log(1 + mp.mpf(lam) / 2) / 2


def best_j(lam, jmax=400):
    vals = [(f(j, lam), j) for j in range(1, jmax + 1)]
    return max(vals)


def breakpoint(j):
    """lam with f_j = f_{j+1}."""
    g = lambda L: f(j, L) - f(j + 1, L)
    # bracket
    lo, hi = mp.mpf('1e-6'), mp.mpf(1) + mp.sqrt(5) - mp.mpf('1e-12')
    # scan for sign change
    xs = [lo + (hi - lo) * k / 4000 for k in range(4001)]
    prev = g(xs[0])
    for a, b in zip(xs, xs[1:]):
        gb = g(b)
        if prev * gb < 0:
            return mp.findroot(g, (a, b), solver='anderson')
        prev = gb
    return None


if __name__ == "__main__":
    print("Randic limit: f_j/lam -> j(j+2)/(2(j+1)(2j+1)):")
    for j in range(1, 8):
        print("  j=%d  %s" % (j, mp.nstr(mp.mpf(j * (j + 2)) / (2 * (j + 1) * (2 * j + 1)), 12)))
    print("breakpoints lam_j (A_j = A_{j+1}):")
    bps = []
    for j in range(1, 40):
        b = breakpoint(j)
        bps.append((j, b))
        print("  j=%2d  lam=%s" % (j, mp.nstr(b, 20) if b is not None else None))
    print("1+sqrt5 =", mp.nstr(1 + mp.sqrt(5), 20))
    print("best arm on a grid:")
    for lam in [mp.mpf(x) / 100 for x in [1, 10, 25, 50, 75, 100, 150, 200, 250, 300, 320]]:
        v, j = best_j(lam)
        print("  lam=%s best j=%d f=%s cherry=%s rho=%s" % (mp.nstr(lam, 4), j, mp.nstr(v, 12),
              mp.nstr(cherry_rate(lam), 12), mp.nstr(mp.e ** v, 12)))
