"""Large lam: is T_b(lam)/(2+lam)^{n/2} nonincreasing in lam (for lam >= Lambda)?  Equivalent: elasticity
E_b(lam) := (2+lam) T_b'(lam)/T_b(lam) = sum_i (2+lam)/(rho_i+lam) <= n/2.  Test on all planted branches with <= NMAX vertices."""
import sys, math, itertools
exec(open('exp1_ceiling.py').read().split('allt = ')[0].replace('NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15','NMAX = 16'))
def poly(t):
    """planted weighted matching polynomial T_b(lam) = sum_k c_k lam^k, root degree = #children + 1. Returns (free, total) coeff lists."""
    d = len(t) + 1
    kids = [poly(c) for c in t]
    # cavity: T_b = prod T_c * (1 + lam R/d), with R = sum y_c, y_c = T_c^free/(d_c T_c)  -> polynomial form:
    # T_b = prod_c T_c + lam/d * sum_c (T_c^free/d_c) prod_{c' != c} T_c'
    from functools import reduce
    def mul(p, q):
        r = [0.0]*(len(p)+len(q)-1)
        for i, a in enumerate(p):
            for j, b in enumerate(q): r[i+j] += a*b
        return r
    def add(p, q):
        n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
    prodT = reduce(mul, [k[1] for k in kids], [1.0])
    total = prodT
    for i, (fr, to, dc) in enumerate(kids):
        rest = reduce(mul, [k[1] for j, k in enumerate(kids) if j != i], [1.0])
        term = mul([0.0, 1.0/(d*dc)], mul(fr, rest))
        total = add(total, term)
    return (prodT, total, d)
worst = {}
lams = [100, 300, 1000, 2000, 1e4, 1e5, 1e7]
for n in range(1, 17):
    for t in trees(n):
        _, T, _ = poly(t)
        for lam in lams:
            val = sum(c*lam**k for k, c in enumerate(T)); der = sum(k*c*lam**(k-1) for k, c in enumerate(T) if k)
            el = (2+lam)*der/val - n/2
            if el > worst.get(lam, (-9,))[0]: worst[lam] = (el, n, t)
for lam in lams:
    el, n, t = worst[lam]; print(f"lam={lam:g}: max over branches (n<=16) of elasticity - n/2 = {el:+.4e} (n={n})")
