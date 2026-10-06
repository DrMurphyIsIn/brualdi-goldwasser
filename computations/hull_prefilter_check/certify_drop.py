"""Certify that a floating-point prefilter discarded no point of Ext(C).

Setting. C is the finite set of candidate points (exact positive rationals (x, y), x >= 1, y > 0) of one
class of a hull computation; a prefilter keeps a subset C' (the survivors) and the program then
computes Ext(C') exactly. Ext(C) = Ext(C') holds as soon as every discarded point p satisfies

    (*)  a . p  <  max_{v in C'} a . v     for every a in R^2 with a > 0,

because then, for every a > 0, the maximum of a . x over C is attained only in C'. This module checks
(*) for every discarded point, in one of two ways:

1. Float certificate. Let V be the exact upper-right hull chain of C' (x increasing, y decreasing).
   For p with float coordinates (X, Y) we pick a float lam in [0, 1] and two consecutive chain
   points v_a, v_b (or a single chain point), and test in IEEE-754 double precision
        fl(lam * fl(v_a.x) + fl(1 - lam) * fl(v_b.x)) >= fl(c * X)   and the same for y,
   with c = fl(1 + 2 eps), eps = 1e-12. Error bound (standard model, |delta| <= u = 2^-53 for each
   basic operation, gamma_k = k u/(1 - k u); all quantities are positive, so there is no cancellation):
     - the candidate coordinates are X = x (1 + t), |t| <= gamma_3 (a product of two correctly
       rounded exact values) and Y = y (1 + t'), |t'| <= gamma_4 (a sum of two such products);
     - the left side is at most (lam v_a.x + (1 - lam) v_b.x)(1 + gamma_4), and the true point
       w = lam v_a + (1 - lam) v_b lies in conv(C');
     - the right side is at least (1 + 2 eps - u)(1 - u)(1 - gamma_4) times the true coordinate.
   Hence w.x >= x (1 + 2 eps - u)(1 - u)(1 - gamma_4)/(1 + gamma_4) > x, as 2 eps > 10 u, and the same
   for y. So p < w strictly in both coordinates, and a . p < a . w <= max_{C'} a . v for every a > 0.
   A NaN or an infinite value fails the test and sends the point to the exact check.
2. Exact check (for every point the float certificate does not settle). With p exact and V exact,
   g(t) = max_{v in V} [(v.x - p.x) + t (v.y - p.y)] is convex and piecewise linear in t > 0, with
   breakpoints at the slopes of the chain; (*) for a = (1, t) is g(t) > 0. It holds for all t > 0 iff
   g > 0 at every breakpoint and in the two limits t -> 0+ (the chain point of largest x) and
   t -> infinity (the chain point of largest y). All of this is exact rational arithmetic.
"""
import numpy as np
from fractions import Fraction as Fr

EPS = 1e-12


def chain_of(points):
    """exact upper-right chain (x strictly increasing, y strictly decreasing) of a list of (x, y)"""
    pts = sorted(set(points))
    par = []
    for x, y in reversed(pts):                 # x descending
        if par and y <= par[-1][1]:
            continue
        par.append((x, y))
    par.reverse()                               # x ascending, y strictly descending
    out = []
    for p in par:
        while len(out) >= 2:
            a, b = out[-2], out[-1]
            cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
            if cross >= 0:                      # b on or below the chord a-p: not a strict vertex
                out.pop()
            else:
                break
        out.append(p)
    return out


def float_certified(X, Y, chain):
    """boolean array: (*) certified by the float test of the module docstring"""
    m = len(X)
    ok = np.zeros(m, dtype=bool)
    if m == 0 or not chain:
        return ok
    cx = np.array([float(v[0]) for v in chain])
    cy = np.array([float(v[1]) for v in chain])
    c = 1.0 + 2 * EPS
    k = len(cx)
    tx = (1.0 + 3 * EPS) * X
    idx = np.searchsorted(cx, tx, side="left")
    with np.errstate(all="ignore"):
        s0 = idx == 0
        ok[s0] = (cx[0] >= c * X[s0]) & (cy[0] >= c * Y[s0])
        s1 = (idx > 0) & (idx < k)
        j = np.nonzero(s1)[0]
        if len(j):
            b = idx[j]
            a = b - 1
            lam = (cx[b] - tx[j]) / (cx[b] - cx[a])
            lam = np.clip(lam, 0.0, 1.0)
            mu = 1.0 - lam
            wx = lam * cx[a] + mu * cx[b]
            wy = lam * cy[a] + mu * cy[b]
            good = (wx >= c * X[j]) & (wy >= c * Y[j]) & np.isfinite(wx) & np.isfinite(wy) & np.isfinite(lam)
            ok[j] = good
    ok &= np.isfinite(X) & np.isfinite(Y) & (X > 0) & (Y > 0)
    return ok


def exact_not_in_ext(p, chain):
    """exact test of (*) for one point p = (x, y) against the exact chain"""
    px, py = p
    k = len(chain)
    # t -> 0+: the chain point of largest x is the last one
    lx, ly = chain[-1]
    if not (lx > px or (lx == px and ly > py)):
        return False
    # t -> infinity: the chain point of largest y is the first one
    fx, fy = chain[0]
    if not (fy > py or (fy == py and fx > px)):
        return False
    # breakpoints t_i where chain[i] and chain[i+1] are both optimal
    for i in range(k - 1):
        (x0, y0), (x1, y1) = chain[i], chain[i + 1]
        t = Fr(x1 - x0) / Fr(y0 - y1)           # > 0
        g = (x0 - px) + t * (y0 - py)
        if g <= 0:
            return False
    return True


class Tally:
    def __init__(self):
        self.candidates = 0
        self.dropped = 0
        self.float_ok = 0
        self.exact_ok = 0
        self.failed = []

    def line(self):
        return ("candidates %d, discarded by the prefilter %d: certified by the float test %d, by the exact "
                "test %d, NOT certified %d" % (self.candidates, self.dropped, self.float_ok, self.exact_ok,
                                               len(self.failed)))


def certify_class(X, Y, keep, survivors_exact, exact_of, tally, label):
    """X, Y: float arrays of all candidates of a class; keep: indices kept by the prefilter;
    survivors_exact: exact (x, y) of the survivors; exact_of(i): exact (x, y) of candidate i."""
    m = len(X)
    tally.candidates += m
    mask = np.ones(m, dtype=bool)
    mask[np.asarray(keep, dtype=int)] = False
    drop = np.nonzero(mask)[0]
    if len(drop) == 0:
        return
    tally.dropped += len(drop)
    chain = chain_of(survivors_exact)
    okf = float_certified(X[drop], Y[drop], chain)
    tally.float_ok += int(okf.sum())
    for i in drop[~okf]:
        p = exact_of(int(i))
        if exact_not_in_ext(p, chain):
            tally.exact_ok += 1
        else:
            tally.failed.append((label, int(i), p))
