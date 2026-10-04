"""Brute-force check of the certify_band.py induction hypothesis on every planted branch with n <= NMAX, for one lam-box:
recompute the witness (J, G, GT) for the box, then for lam in {a, mid, b}: exact cavity (l, y, R) per branch, classify
(LEAF / P2 / spider / GEN(e, k) with R in bin k) and require l <= G[e, k] for every bin containing R; spiders l <= 0; y in the type's range."""
import sys, math
import certify_band as cb
_src = open('small_lambda_monotone.py').read(); exec(_src[:_src.index('worst = {}\nS =')])
a, b, DELTA = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]); NMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 14
J, G, GT = cb.witness(a, b, DELTA)
def Fst(lam): return cb.best_J(lam)[1]
def walk(t, lam, F):
    d = len(t) + 1; l = 0.0; R = 0.0
    for c in t:
        lc, yc, _ = walk(c, lam, F); l += lc; R += yc
    return l + math.log1p(lam*R/d) - F, 1/(d + lam*R), R
def cls(t):
    d = len(t) + 1
    if d == 1: return 'L'
    if d == 2 and t == ((),): return 'P2'
    if d >= 3 and all(c == ((),) for c in t): return 'S'
    return 'GEN'
worst = -9; cnt = 0; spid = -9
for lam in [a, 0.5*(a + b), b]:
    F = Fst(lam)
    for n in range(1, NMAX+1):
        for t in trees(n):
            c = cls(t); l, y, R = walk(t, lam, F); cnt += 1; e = len(t) + 1
            if c == 'S': spid = max(spid, l); continue
            if c != 'GEN': continue
            if e > cb.DT: worst = max(worst, l - GT); continue
            for k in range(cb.K):
                lo, hi = (e-1)*k/cb.K, (e-1)*(k+1)/cb.K
                if lo - 1e-12 <= R <= hi + 1e-12: worst = max(worst, l - G[(e, k)])
print(f"box [{a}, {b}], DELTA={DELTA}, J={J}: {cnt} branch-evaluations (n <= {NMAX}); max over GEN of (l - G) = {worst:+.3e} (must be < 0);"
      f" max spider l = {spid:+.2e} (must be <= 0)")
