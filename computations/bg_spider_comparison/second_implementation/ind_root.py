"""Independent recomputation of V_k(n) and failing n. Enumerates ALL arm lengths that fit (no tail bound needed).
Variant 'paper': root atoms C^c A_s^m1 A_{s+1}^m2 with any s (plus L for k=2).
Variant 'deg': additionally arm vertices have <= k-1 children (max degree)."""
from ind_common import *
import sys, json
NMAX = 315
sp = json.load(open('ind_spider.json'))
PHI = {int(n): v[0] for n, v in sp.items()}
def hub(c, s, m1, m2):
    return branch([CH] * c + [arm(s)] * m1 + [arm(s + 1)] * m2)
def gamma_lb(C):
    eta = ETA[C]; best = None
    shapes = [branch([arm(j)]) for j in range(1, 5)]
    for s in range(1, 41):
        for tot in range(2, C + 1):
            for m1 in range(0, tot + 1):
                for m2 in range(0, tot - m1 + 1):
                    if m1 + m2: shapes.append(hub(tot - m1 - m2, s, m1, m2))
    v = min(float(dHslack(b, eta).lower()) for b in shapes)
    tl = 41 * (BETA - 2 * A(eta)) + LAM - A(Fr(4, 3)).log() - KAP * A(Q) ** 2 + 10 * A(eta)
    assert float(tl.lower()) > v and (BETA - 2 * A(eta)) > 0
    return arb(v)  # float lower endpoint of an arb lower bound, exact binary number -> still a valid lower bound
kr = range(int(sys.argv[1]), int(sys.argv[2]) + 1)
res = {}
for k in kr:
    C = k - 1; eta = ETA[C]; gam = gamma_lb(C)
    cost = {}
    def acost(a):  # g(a) - eta|a|
        key = a
        if key not in cost:
            b = LEAF if a == 'L' else (CH if a == 'C' else arm(a))
            cost[key] = (g(b) - A(eta * b[2]), b[1], b[2])
        return cost[key]
    fcache = {}
    recs = {'paper': [], 'deg': []}   # (min n, value upper bound, cfg)
    for j in range(1, k + 1):
        m = k - j
        cfgs = []
        if m == 0: cfgs.append(())
        else:
            cfgs.append((('C', m),))
            for s in range(1, NMAX):
                if 2 * s + 1 + 4 * j > NMAX - 1: break
                for m1 in range(1, m + 1):
                    for m2 in range(0, m - m1 + 1):
                        cfgs.append((('C', m - m1 - m2), (s, m1), (s + 1, m2)))
            if k == 2 and m == 1:
                cfgs.append((('L', 1),))
        for cf in cfgs:
            size = 0; S = Fr(0); K = arb(0); maxarm = 0
            for a, cnt in cf:
                if cnt == 0: continue
                cc, x, sz = acost(a)
                size += cnt * sz; S += cnt * x; K += cnt * cc
                if a not in ('C', 'L'): maxarm = max(maxarm, a)
            nmin = size + 4 * j + 1
            if nmin > NMAX: continue
            key = (j, S)
            if key not in fcache:
                fcache[key] = fmax_upper(S, j, k, eta, Fr(1, 2))
            val = (fcache[key] - K - j * gam).upper()
            recs['paper'].append((nmin, val, cf))
            if maxarm <= k - 1:
                recs['deg'].append((nmin, val, cf))
    out = {}
    for var, R in recs.items():
        R.sort(key=lambda t: t[0])
        bad = []; worst = {}
        i = 0; cur = None; curcf = None
        for n in range(7, NMAX + 1):
            while i < len(R) and R[i][0] <= n:
                if cur is None or R[i][1] > cur: cur, curcf = R[i][1], R[i][2]
                i += 1
            if cur is None: continue
            bound = (cur - A(eta * (n - 1))).upper()
            if not (float(bound) < PHI[n]):   # float(bound) is upper endpoint; PHI lower endpoint
                bad.append(n)
            worst[n] = (float(bound) - PHI[n], str(curcf))
        n0 = max(bad) + 1 if bad else 7
        margin108 = min(-worst[n][0] for n in range(108, NMAX + 1) if n in worst)
        out[var] = dict(bad=bad, n0=n0, Vmax=float(max(r[1] for r in R)), margin_ge108=margin108)
    res[k] = dict(gamma=float(gam), out=out)
    print(k, "gamma>=%.6f" % float(gam), "paper n0=%d Vmax=%.5f margin(n>=108)=%.2e #bad=%d" % (out['paper']['n0'], out['paper']['Vmax'], out['paper']['margin_ge108'], len(out['paper']['bad'])),
          "| deg n0=%d #bad=%d" % (out['deg']['n0'], len(out['deg']['bad'])), flush=True)
json.dump(res, open('ind_root_%s_%s.json' % (sys.argv[1], sys.argv[2]), 'w'), indent=0)
