"""Numerical sanity test and negative controls for part (B) (not a proof), written from the definitions in the text
separately from the programs of this folder. W* is the witness W_1 of the paper, W2 is W_2.
For random lambda in (0, lambda_c):
  * F = f* = max_j f_j; witness W2 if lambda <= 3/20, W* if lambda >= 3/20 (both on [0.1282, 0.15]);
  * Bellman margins B_{k,m}(ybar) >= 0 on a grid (k<=6, m<=400 plus m in a sparse set up to 20000), all kinks and preimages;
  * random planted branches (cavity recursion R = sum y_c, y = 1/(d + lam R), log T = sum log T_c + log(1 + lam R/d)):
    log T_b <= |b| F, and g(b) >= h(y_b) for every non-leaf b; equality only at best arms (and the cherry g = h = eps);
  * the unscaled W2 conditions (T1..T8, node conditions of lem:flat2 for 5<=m<=13) against the scaled atom forms;
  * sensitivity: W* below lambda_A2 must FAIL at the arm A2 (else the test is blind).
"""
import random
import mpmath as mp
mp.mp.dps = 30
random.seed(20261001)
LC = 1 + mp.sqrt(5)

def setup(lam, kind):
    lam = mp.mpf(lam); c = 1 + lam/2; t = lam/(2+lam); ell = mp.log(c)
    f = lambda j: (j*ell + mp.log(1 + t*j/(j+1)))/(2*j+1)
    # f_j is unimodal in j (thm:lam-ladder); locate the maximizer by doubling + integer ternary search
    hi = 2
    while f(hi) <= f(2*hi) or f(hi) <= f(hi+1):
        hi *= 2
        assert hi < 10**12
    lo_, hi_ = 1, 2*hi
    while hi_ - lo_ > 3:
        m1 = lo_ + (hi_ - lo_)//3; m2 = hi_ - (hi_ - lo_)//3
        if f(m1) < f(m2): lo_ = m1
        else: hi_ = m2
    jstar = max(range(lo_, hi_+1), key=f); F = f(jstar)
    assert F >= max(f(j) for j in range(max(1, jstar-50), jstar+51))
    if kind == 'W2':
        F = f(3); assert jstar == 3, (lam, jstar)
    E = mp.e**F; eps = 2*F - ell; yd = (E-1)/lam; yC = 1/(2+lam); y2 = 1/(3+2*t)
    kap = lam*y2; u = 1 + t - E
    if kind == 'W*':
        s1 = lam*eps/u
        pieces = [(mp.mpf(0), mp.mpf(0)), (s1, -s1*yd), (kap, eps - kap*yC)]
    else:
        gA2 = 5*(F - f(2)); h2 = mp.mpf(4)/5*gA2
        sa = h2/(y2 - yd); sb = (eps - h2)/(yC - y2)
        pieces = [(mp.mpf(0), mp.mpf(0)), (sa, -sa*yd), (sb, h2 - sb*y2), (kap, eps - kap*yC)]
    h = lambda y: max(a*y + b for a, b in pieces)
    return dict(lam=lam, t=t, F=F, jstar=jstar, h=h, eps=eps, yd=yd, yC=yC, y2=y2, kap=kap, E=E, f=f, pieces=pieces)

def bellman_min(W):
    lam, F, h = W['lam'], W['F'], W['h']
    kinks = [W['yd'], W['y2'], W['yC'], mp.mpf(0), mp.mpf(1)/2]
    grid = [mp.mpf(i)/400 for i in range(201)] + kinks
    worst = (mp.inf, None)
    ms = list(range(0, 401)) + [500, 800, 1000, 2000, 5000, 20000] + ([W['jstar']-1, W['jstar'], W['jstar']+1] if W['jstar'] > 400 else [])
    for k in range(0, 7):
        for m in ms:
            if k == 0 and m == 0: continue
            ys = [mp.mpf(0)] if m == 0 else grid
            # preimages of kinks under the parent message map
            if m > 0:
                for y in kinks[:3]:
                    yb = ((1/y) - (k+m+1) - lam*k)/(lam*m)
                    if 0 <= yb <= mp.mpf(1)/2: ys = ys + [yb]
            for yb in ys:
                d = k+m+1; R = k + m*yb
                B = (k+1)*F + m*h(yb) - mp.log(1 + lam*R/d) - h(1/(d + lam*R))
                designed = (k == 1 and m == 0) or (k == 0 and m == W['jstar'] and abs(yb - W['yC']) < mp.mpf('1e-25'))
                if designed:
                    assert B > -mp.mpf('1e-25'), (k, m, yb, B)
                    continue
                if B < worst[0]: worst = (B, (k, m, mp.nstr(yb, 6)))
            if k >= 2 and m > 60: break
    return worst

def rand_branch(maxn, depth=0):
    """random planted branch: returns (size, y, logT)"""
    if maxn <= 1 or depth > 6 or random.random() < 0.18:
        return (1, mp.mpf(1), mp.mpf(0))
    nch = random.choice([1, 1, 2, 2, 3, 3, 3, 4, 5, 6, 8])
    kids = []; budget = maxn - 1
    for _ in range(nch):
        if budget <= 0: break
        kind = random.random()
        if kind < 0.25: ch = (1, mp.mpf(1), mp.mpf(0))
        elif kind < 0.5: ch = cherry
        else: ch = rand_branch(max(1, budget//max(1, nch)), depth+1)
        if ch[0] > budget: ch = (1, mp.mpf(1), mp.mpf(0))
        kids.append(ch); budget -= ch[0]
    return combine(kids)

def combine(kids):
    d = len(kids) + 1; R = sum(k[1] for k in kids)
    return (1 + sum(k[0] for k in kids), 1/(d + LAM*R), sum(k[2] for k in kids) + mp.log(1 + LAM*R/d))

rep = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); rep.append(s)

lams = sorted([mp.mpf(random.uniform(0.001, 0.15)) for _ in range(6)] + [mp.mpf(random.uniform(0.15, float(LC) - 1e-4)) for _ in range(10)]
              + [mp.mpf(3)/20, mp.mpf('0.13'), mp.mpf('0.1282'), mp.mpf('0.4305018580584713'), mp.mpf(2), LC - mp.mpf('1e-6')])
for lam in lams:
    kinds = (['W2'] if lam <= mp.mpf(3)/20 else []) + (['W*'] if lam >= mp.mpf(3)/20 or lam >= mp.mpf('0.1282') else [])
    for kind in kinds:
        W = setup(lam, kind); LAM = W['lam']
        bm = bellman_min(W)
        # random branches
        leaf = (1, mp.mpf(1), mp.mpf(0)); globals()['LAM'] = LAM
        globals()['cherry'] = combine([leaf])
        worst_ceiling = -mp.inf; worst_gh = (mp.inf, None); n = 0
        arms = [combine([cherry]*j) for j in range(1, 9)]
        pool = arms + [combine([leaf, cherry]), combine([leaf]*2), combine([cherry, arms[2]]), combine([arms[2]]*3)]
        for _ in range(1500):
            pool.append(rand_branch(random.choice([5, 9, 15, 25, 40])))
        for b in pool:
            sz, y, LT = b; g = sz*W['F'] - LT
            worst_ceiling = max(worst_ceiling, LT - sz*W['F'])
            if sz >= 2:
                dlt = g - W['h'](y)
                is_cherry = (sz == 3 - 0 and False)
                if sz == 2:  # cherry: designed g = h = eps
                    continue
                if abs(g) < mp.mpf('1e-30'):  # best arm: designed equality
                    continue
                if dlt < worst_gh[0]: worst_gh = (dlt, (sz, mp.nstr(y, 6)))
            n += 1
        P(f"lam={mp.nstr(lam, 8):>12s} {kind:3s} j*={W['jstar']}  min Bellman (excl. designed zeros)={mp.nstr(bm[0], 4):>11s} at (k,m,ybar)={bm[1]}  "
          f"max(logT-|b|F)={mp.nstr(worst_ceiling, 3):>10s}  min(g-h) non-tight={mp.nstr(worst_gh[0], 4)} at (size,y)={worst_gh[1]}")

# unscaled W2 conditions vs scaled
P('\nW2 unscaled conditions on a grid of lambda in (0, 3/20]:')
worst = {}
for i in range(1, 61):
    lam = mp.mpf(3)/20*i/60
    W = setup(lam, 'W2'); t, F, E, eps, kap = W['t'], W['F'], W['E'], W['eps'], W['kap']
    gA2 = 5*(F - W['f'](2)); h2 = mp.mpf(4)/5*gA2
    sa, sb = W['pieces'][1][0], W['pieces'][2][0]
    y4 = 1/(5+4*t)
    Ma = (lam/sa - 1)/(1 + lam*W['yd'])
    cond = dict(T1=kap - (E-1), T2=sb - sa, T3=min(eps - h2, t - kap, gA2), T4=lam*y4*(1 - kap*y4) - sb,
                T5=14 - Ma, T6=14*F - 13*(E-1),
                T7=min(F + m*h2 - kap*m/(m+1) for m in range(5, 14)),
                T8=min(F + m*eps - t*m/(m+1) for m in range(5, 14)),
                Ndag=min((m+1)*F - m*(E-1) for m in range(5, 14)),
                S1=W['yd'] - mp.mpf(1)/6, S2=W['yd'] - 1/(4+3*t))
    for k, v in cond.items():
        v = v/t
        if k not in worst or v < worst[k][0]: worst[k] = (v, mp.nstr(lam, 4))
P('  min over grid of (condition)/t:', {k: (mp.nstr(v, 4), l) for k, (v, l) in worst.items()})

# sensitivity: W* below lambda_A2
for lam in ['0.10', '0.12', '0.128']:
    W = setup(lam, 'W*'); LAM = W['lam']; leaf = (1, mp.mpf(1), mp.mpf(0)); globals()['LAM'] = LAM
    cherry = combine([leaf]); A2 = combine([cherry, cherry])
    P(f'sensitivity: W* at lam={lam}: g(A2)-h(y2) = {mp.nstr(2*0 + 5*W["F"] - A2[2] - W["h"](A2[1]), 4)} (negative expected below 0.12813)')
