"""Bellman potential for the degree-capped Laplacian ratio (upper bound on the growth rate).

Setting.  Planted branch R (root joined to an external parent; degree cap Delta, so the root has
c <= Delta-1 children).  Z(R), message x(R) as in the paper.  Deficit g(R) = lam*|R| - log Z(R).

Ansatz.   h(x) = +log(1 + b*x) + k[type],  types = finitely many x-classes
          (singletons for leaf / cherry / the side branches of the optimal spine, and intervals).
Bellman.  For every c in 0..Delta-1 and child types t_1..t_c and every target type t whose class
          meets the possible parent messages:
              lam + sum k[t_i] - k[t] >= sup_{x_i in class t_i} G_c(x),
              G_c(x) = log((c+1+b+S)/(c+1)) - sum log(1+b x_i),   S = sum x_i.
          (since Z_par(1+b x_par) = prod Z_i * (c+1+b+S)/(c+1)).
          G_c is monotone in each coordinate (sign of 1 - b(c+1+b+S_{-i})), so the sup over a box is
          attained at a corner; corners of a group of equal boxes only depend on how many are 'hi'.
Then induction gives g(R) >= h(x(R)) >= min h, i.e. Z(R) <= C rho^|R|.

Modes:  python3 potential.py Delta K          (float least fixed point; feasibility)
        python3 potential.py Delta K --verify (rigorous: mpmath interval arithmetic + exact identities)
"""
import sys, math, itertools
from fractions import Fraction as Fr
from collections import Counter

# ---------------------------------------------------------------- side branches of optimal spine
CHERRY = ('K', Fr(1, 3), 2, Fr(3, 2))             # name, x, size, Z
C5 = ('C5', Fr(3, 23), 11, Fr(621, 64))
LEAF = ('L', Fr(1), 1, Fr(1))

# optimal spine side multisets found by chain_opt.py (numbers of cherries, C5's)
SIDES = {3: (1, 0), 4: (2, 0), 5: (3, 0), 6: (4, 0), 7: (5, 0), 8: (4, 2), 9: (3, 4), 10: (1, 7),
         11: (0, 9), 12: (0, 10)}


def spine_constants(D, nK, nC):
    """exact data of the spine: d = Delta, P = prod Z_side, S = sum x_side (rationals);
    t = root of t^2 - (1+S/d) t - 1/d^2; mu = P t; lam = log(mu)/size; b = 1/(d t)."""
    d = D
    P = CHERRY[3] ** nK * C5[3] ** nC
    S = nK * CHERRY[1] + nC * C5[1]
    size = 1 + nK * CHERRY[2] + nC * C5[2]
    A = 1 + S / d
    # t = (A + sqrt(A^2 + 4/d^2))/2
    return dict(d=d, P=P, S=S, size=size, A=A, disc=A * A + Fr(4, d * d))


def floats(sc):
    t = (float(sc['A']) + math.sqrt(float(sc['disc']))) / 2
    mu = float(sc['P']) * t
    return math.log(mu) / sc['size'], 1 / (sc['d'] * t), mu


# ---------------------------------------------------------------- types
REFINE = {}   # Delta -> list of (lo, hi, pieces) refinement windows inside the B window


def make_types(D, K, nC):
    """returns list of (name, lo, hi) with Fractions.  Singletons first.
    B window: K uniform pieces, except that windows in REFINE[D] are cut into finer pieces."""
    if D in REFINE:
        return make_types_refined(D, K, nC, REFINE[D])
    ty = [('L', Fr(1), Fr(1)), ('K', Fr(1, 3), Fr(1, 3))]
    if nC > 0 or D >= 6:
        ty.append(('C5', Fr(3, 23), Fr(3, 23)))
    lo = Fr(1, 2 * D - 1)
    Bhi = Fr(2 * D - 1, 6 * D - 1)       # c >= 2  =>  x <= 1/(3 + 2/(2D-1))
    Alo, Ahi = Fr(2, 5), Fr(2 * D - 1, 4 * D - 1)   # c = 1, non-leaf child
    for i in range(K):
        ty.append(('B%d' % i, lo + (Bhi - lo) * i / K, lo + (Bhi - lo) * (i + 1) / K))
    for i in range(K):
        ty.append(('A%d' % i, Alo + (Ahi - Alo) * i / K, Alo + (Ahi - Alo) * (i + 1) / K))
    return ty


def make_types_refined(D, K, nC, windows):
    ty = [('L', Fr(1), Fr(1)), ('K', Fr(1, 3), Fr(1, 3))]
    if nC > 0 or D >= 6:
        ty.append(('C5', Fr(3, 23), Fr(3, 23)))
    lo = Fr(1, 2 * D - 1)
    Bhi = Fr(2 * D - 1, 6 * D - 1)
    Alo, Ahi = Fr(2, 5), Fr(2 * D - 1, 4 * D - 1)
    pts = set(lo + (Bhi - lo) * i / K for i in range(K + 1))
    for (a, b, m) in windows:
        a, b = max(Fr(a), lo), min(Fr(b), Bhi)
        pts |= set(a + (b - a) * i / m for i in range(m + 1))
    pts = sorted(pts)
    for i in range(len(pts) - 1):
        ty.append(('B%d' % i, pts[i], pts[i + 1]))
    for i in range(K):
        ty.append(('A%d' % i, Alo + (Ahi - Alo) * i / K, Alo + (Ahi - Alo) * (i + 1) / K))
    return ty


def G_float(xs, b):
    d = len(xs) + 1
    S = sum(xs)
    return math.log((d + S + b) / d) - sum(math.log(1 + b * x) for x in xs)


def corner_sets(combo, types):
    """yield lists of x-values (Fractions) = corners of the child box, up to symmetry in groups"""
    groups = sorted(Counter(combo).items())
    choices = []
    for t, m in groups:
        lo, hi = types[t][1], types[t][2]
        if lo == hi:
            choices.append([[lo] * m])
        else:
            choices.append([[lo] * (m - j) + [hi] * j for j in range(m + 1)])
    for pick in itertools.product(*choices):
        yield [x for part in pick for x in part]


def rules(D, types, live):
    """enumerate (combo, targets) for c = 1..D-1 over live child types"""
    for c in range(1, D):
        for combo in itertools.combinations_with_replacement(live, c):
            if c >= 1 and any(types[t][0] == 'L' for t in combo) and False:
                pass
            d = c + 1
            Slo = sum(types[t][1] for t in combo)
            Shi = sum(types[t][2] for t in combo)
            plo, phi = 1 / (d + Shi), 1 / (d + Slo)
            targets = [u for u in range(len(types)) if types[u][0] != 'L'
                       and types[u][1] <= phi and types[u][2] >= plo]
            # a point range equal to a singleton class: that class alone covers the parent
            if plo == phi:
                single = [u for u in targets if types[u][1] == types[u][2] == plo]
                if single:
                    targets = single
            if not targets:
                raise RuntimeError('coverage gap for combo %s: [%s,%s]' % (combo, plo, phi))
            yield combo, targets


def least_fixed_point(D, types, lam, b, iters=200):
    INF = float('inf')
    K = len(types)
    k = [INF] * K
    k[0] = lam - math.log(1 + b)
    arg = [None] * K
    cache = {}
    for it in range(iters):
        changed = False
        live = [i for i in range(K) if k[i] < INF]
        for combo, targets in rules(D, types, live):
            if combo not in cache:
                cache[combo] = max(G_float([float(x) for x in xs], b) for xs in corner_sets(combo, types))
            val = lam + sum(k[i] for i in combo) - cache[combo]
            for t in targets:
                if val < k[t] - 1e-12:
                    k[t] = val
                    arg[t] = combo
                    changed = True
        if min(k) < -100:
            return None, it, cache
        if not changed:
            return k, it, cache
    return None, iters, cache


def main():
    D = int(sys.argv[1])
    K = int(sys.argv[2])
    nK, nC = SIDES[D]
    sc = spine_constants(D, nK, nC)
    lam, b, mu = floats(sc)
    types = make_types(D, K, nC)
    k, it, cache = least_fixed_point(D, types, lam, b)
    print('Delta=%d sides: %d cherries + %d C5; rho=%.12f b=%.10f  K=%d types=%d  -> %s (iter %d)'
          % (D, nK, nC, math.exp(lam), b, K, len(types), 'FEASIBLE' if k else 'INFEASIBLE', it))
    if k and '-v' in sys.argv:
        for ty, kv in zip(types, k):
            if kv < float('inf'):
                print('  %-4s [%.6f, %.6f]  k = %.9f' % (ty[0], float(ty[1]), float(ty[2]), kv))
    return D, K, sc, types, k, cache


if __name__ == '__main__':
    main()
