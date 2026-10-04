"""Experiment 1b: does the sharp ceiling (best per-vertex rate = best arm) survive at each lambda?
Max over all planted rooted trees b with |b| <= NMAX of l(b) = log T_b - |b| F*(lam)."""
import math, itertools, sys
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15
def trees(n, memo={}):
    if n in memo: return memo[n]
    if n == 1: memo[1] = [()]; return memo[1]
    res = set()
    def parts(rem, mx):
        if rem == 0: yield []; return
        for s in range(min(rem, mx), 0, -1):
            for r in parts(rem - s, s): yield [s] + r
    for p in parts(n - 1, n - 1):
        for combo in itertools.product(*[trees(s) for s in p]):
            res.add(tuple(sorted(combo)))
    memo[n] = list(res); return memo[n]
def ev(t, lam, memo):
    if t in memo: return memo[t]
    if t == (): r = (0.0, 1.0)            # (log T, y)
    else:
        ch = [ev(c, lam, memo) for c in t]; d = len(t) + 1; R = sum(y for _, y in ch)
        r = (sum(l for l, _ in ch) + math.log1p(lam * R / d), 1.0 / (d + lam * R))
    memo[t] = r; return r
def arm_rate(j, lam):
    return (j*math.log1p(lam/2) + math.log1p(lam*j/((2+lam)*(j+1)))) / (2*j+1)
allt = [(n, t) for n in range(1, NMAX+1) for t in trees(n)]
print(f"{len(allt)} rooted trees with <= {NMAX} vertices")
for lam in [0.1, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.236, 3.5, 4.0, 6.0]:
    Fs = max(max(arm_rate(j, lam) for j in range(1, 5000)), math.log1p(lam/2)/2)
    memo = {}; best = (-9, None)
    for n, t in allt:
        l = ev(t, lam, memo)[0] - n * Fs
        if l > best[0]: best = (l, (n, t))
    jb = max(range(1, 5000), key=lambda j: arm_rate(j, lam))
    tag = "CEILING HOLDS (<=0)" if best[0] <= 1e-12 else "VIOLATED"
    print(f"lam={lam:5}: best arm A{jb if jb < 4999 else 'inf'}, max profit over small trees = {best[0]:+.3e} (n={best[1][0]}) {tag}")
