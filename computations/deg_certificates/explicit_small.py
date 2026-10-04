"""Explicit, human-readable potentials for Delta = 3 and 4 (one interval for each message window):
   h(x) = +log(1+b x) + k(x),  k = lam - log(1+b) at x = 1,
                               k = k_K := 2 lam - log(3/2) - log(1 + b/3)  on {1/3} u B_Delta,
                               k = kA (a short decimal)                      on A_Delta.
All Bellman inequalities are checked: identity (exact), chain (exact, k_I >= k_t), generic (interval)."""
import sys
from fractions import Fraction as Fr
import verify as V
from mpmath import iv
KA = {3: Fr(-813, 10000), 4: Fr(-391, 10000)}
for D in (3, 4):
    st = V.setup(D, 1); rules = V.build_rules(st)
    kiv = dict(st['kex_iv'])
    iK, iB, iA = st['names'].index('K'), st['names'].index('B0'), st['names'].index('A0')
    kiv[iB] = kiv[iK]; kiv[iA] = V.ivq(KA[D])
    worst = None; fails = 0
    for r in rules:
        if r['kind'] == 'identity': continue
        if r['kind'] == 'chain':
            I, t = r['port'], r['t']
            same = (I == t) or ({I, t} == {iK, iB})
            d = kiv[I] - kiv[t]
            if not (same or d.a > 0): fails += 1; print('chain fail', r)
            continue
        g = None
        for xs in r['corners']:
            v = V.G_iv(xs, st['b_iv']); g = v.b if g is None or v.b > g else g
        sl = st['lam_iv'] + sum((kiv[c] for c in r['combo']), iv.mpf(0)) - kiv[r['t']] - g
        if not sl.a > 0: fails += 1; print('fail', [st['names'][c] for c in r['combo']], st['names'][r['t']])
        if worst is None or sl.a < worst[0]: worst = (sl.a, [st['names'][c] for c in r['combo']], st['names'][r['t']])
    print('Delta=%d: rules %d, failures %d, min generic slack %.3e at %s -> %s' % (D, len(rules), fails, float(worst[0]), worst[1], worst[2]))
