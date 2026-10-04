"""Brute-force check of the certify_small.py induction hypothesis on every planted branch with n <= NMAX:
classify (LEAF / P2 / spider S_e / GEN_e) and verify l/lam <= g_e for GEN, l <= 0 for spiders, y <= 1/e."""
import sys, math
from mpmath import mpf
_src = open('small_lambda_monotone.py').read(); exec(_src[:_src.index('worst = {}\nS =')])
sys.argv = ['x', '0.1', '0.0005', '0.006']
exec(open('certify_small.py').read().split('if __name__')[0])
g = first_order_g(240); g = {e: float(v) for e, v in g.items()}
def cls(t):
    d = len(t) + 1
    if d == 1: return 'L'
    if d == 2 and t == ((),): return 'P2'
    if d >= 3 and all(c == ((),) for c in t): return ('S', d)
    return d
def ell(t, lam, F):
    """exact l and message y by the cavity recursion."""
    d = len(t) + 1; l = 0.0; R = 0.0
    for c in t:
        lc, yc = ell(c, lam, F); l += lc; R += yc
    return l + math.log1p(lam*R/d) - F, 1/(d + lam*R)
worst = {}
for lam in [0.001, 0.02, 0.05, 0.1]:
    F = r3(lam); cnt = 0; w = -9
    for n in range(1, 15):
        for t in trees(n):
            c = cls(t); l, y = ell(t, lam, F); cnt += 1
            if isinstance(c, int):
                w = max(w, l/lam - g[c]); assert y <= 1/c + 1e-15
            elif c[0] == 'S' if isinstance(c, tuple) else False:
                assert l <= 1e-13, (t, l)
    print(f"lam={lam}: {cnt} branches; max over GEN of (l/lam - g_e) = {w:+.5f}  (must be < 0)")
