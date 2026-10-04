"""Randomised exact test of the two hull routines against the definition of K."""
import random
from fractions import Fraction as Fr
import dp, dp_check

def K_def(P):
    ts = set()
    for p in P:
        for q in P:
            if p != q and (p[1] - q[1]) != 0:
                t = -Fr(p[0] - q[0]) / (p[1] - q[1])
                if t > 0: ts.add(t)
    ts = sorted(ts)
    tests = ts + [(a + b) / 2 for a, b in zip(ts, ts[1:])]
    tests += [ts[0] / 2, ts[-1] * 2] if ts else [Fr(1)]
    out = set()
    for t in tests:
        m = max(p[0] + t * p[1] for p in P)
        out |= {p for p in P if p[0] + t * p[1] == m}
    return out

random.seed(1)
for it in range(20000):
    n = random.randint(1, 9); R = random.choice([3, 5, 8])
    P = {(Fr(random.randint(0, R)), Fr(random.randint(0, R))) for _ in range(n)}
    want = K_def(P)
    got1 = {(x, y) for x, y, _ in dp.exact_K({p: {0} for p in P})}
    got2 = set(dp_check.hull_K({p: None for p in P}).keys())
    assert got1 == want, (sorted(P), got1, want)
    assert got2 == want, (sorted(P), got2, want)
print("hull routines agree with the definition of K on 20000 random sets")
