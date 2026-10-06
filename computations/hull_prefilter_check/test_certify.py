"""Tests of certify_drop.py, including negative controls.

On random sets of exact rational points (many exactly collinear, nearly collinear, and nearly
vertical or horizontal ties), Ext is computed from its definition by brute force over the weights at
which the optimum changes; then
  - (positive control) every point outside Ext, discarded, must be certified;
  - (negative control) every point of Ext, deliberately discarded, must NOT be certified.
Usage: python3 test_certify.py
"""
import os
import random
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from certify_drop import Tally, certify_class


def ext_bruteforce(pts):
    """points optimal for some a = (1, t), t > 0: test t at all critical values and between them"""
    crit = set()
    P = list(pts)
    for i in range(len(P)):
        for j in range(len(P)):
            (x0, y0), (x1, y1) = P[i], P[j]
            if y0 != y1:
                t = Fr(x1 - x0, 1) / (y0 - y1)
                if t > 0:
                    crit.add(t)
    crit = sorted(crit)
    tests = set(crit)
    if crit:
        tests.add(crit[0] / 2)
        tests.add(crit[-1] * 2)
        for a, b in zip(crit, crit[1:]):
            tests.add((a + b) / 2)
    else:
        tests.add(Fr(1))
    # limits t -> 0 and t -> infinity are represented by tiny and huge t
    tests.add(Fr(1, 10 ** 30))
    tests.add(Fr(10 ** 30))
    ext = set()
    for t in tests:
        best = max(x + t * y for x, y in P)
        for x, y in P:
            if x + t * y == best:
                ext.add((x, y))
    return ext


def random_set(rng):
    pts = set()
    base = [(Fr(rng.randint(1, 40)), Fr(rng.randint(1, 40))) for _ in range(rng.randint(2, 6))]
    for _ in range(rng.randint(3, 25)):
        kind = rng.random()
        a, b = rng.sample(base, 2) if len(base) > 1 else (base[0], base[0])
        if kind < 0.3:                                     # exactly on a segment
            lam = Fr(rng.randint(0, 8), 8)
            pts.add((lam * a[0] + (1 - lam) * b[0], lam * a[1] + (1 - lam) * b[1]))
        elif kind < 0.5:                                   # nearly on a segment
            lam = Fr(rng.randint(0, 8), 8)
            e = Fr(rng.choice([-1, 1]), 10 ** rng.randint(9, 16))
            pts.add((lam * a[0] + (1 - lam) * b[0] + e, lam * a[1] + (1 - lam) * b[1] - e))
        elif kind < 0.7:                                   # near-vertical / near-horizontal ties
            e = Fr(1, 10 ** rng.randint(12, 17))
            p = rng.choice(base)
            pts.add((p[0] + e, p[1] - Fr(rng.randint(1, 5), 10 ** rng.randint(6, 9))))
        else:
            pts.add((Fr(rng.randint(1, 40)), Fr(rng.randint(1, 40))))
    pts |= set(base)
    return [p for p in pts if p[0] > 0 and p[1] > 0]


def main():
    rng = random.Random(20261006)
    n_sets = 3000
    pos_ok = pos_n = neg_caught = neg_n = pos_exact = 0
    for _ in range(n_sets):
        pts = random_set(rng)
        ext = ext_bruteforce(pts)
        X = np.array([float(p[0]) for p in pts])
        Y = np.array([float(p[1]) for p in pts])
        # positive control: keep exactly Ext, discard the rest
        keep = [i for i, p in enumerate(pts) if p in ext]
        t = Tally()
        certify_class(X, Y, keep, [pts[i] for i in keep], lambda i: pts[i], t, "pos")
        pos_n += t.dropped
        pos_ok += t.float_ok + t.exact_ok
        pos_exact += t.exact_ok
        assert not t.failed, t.failed
        # negative control: additionally discard one point of Ext
        if len(ext) >= 2:
            victim = rng.choice(keep)
            keep2 = [i for i in keep if i != victim]
            t2 = Tally()
            certify_class(X, Y, keep2, [pts[i] for i in keep2], lambda i: pts[i], t2, "neg")
            neg_n += 1
            if any(f[1] == victim for f in t2.failed):
                neg_caught += 1
    print("positive control: %d discarded non-Ext points in %d random sets, %d certified (%d of them by the exact test)"
          % (pos_n, n_sets, pos_ok, pos_exact))
    print("negative control: %d sets with one Ext point wrongly discarded, %d caught" % (neg_n, neg_caught))
    ok = pos_ok == pos_n and neg_caught == neg_n
    print("TEST " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
