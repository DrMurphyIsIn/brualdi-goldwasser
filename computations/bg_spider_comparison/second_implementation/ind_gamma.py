from ind_common import *
import sys, json
# gamma_C: min delta^H over (M)-shapes with at most C children; enumerate s <= SMAX exactly, then tail
def hub(c, s, m1, m2):
    return branch([CH] * c + [arm(s)] * m1 + [arm(s + 1)] * m2)
def tail_lb(j, eta):  # independent derivation of the displayed bound, recomputed
    return j * (BETA - 2 * A(eta)) + LAM - A(Fr(4, 3)).log() - KAP * A(Q) ** 2 + 10 * A(eta)
res = {}
for C in range(1, 23):
    eta = ETA[C]
    best = None
    shapes = [('stalk', j) for j in range(1, 5)]
    SMAX = 40
    for s in range(1, SMAX + 1):
        for tot in range(2, C + 1):
            for m1 in range(0, tot + 1):
                for m2 in range(0, tot - m1 + 1):
                    if m1 + m2 == 0: continue
                    shapes.append(('hub', (tot - m1 - m2, s, m1, m2)))
    vals = []
    for sh in shapes:
        b = branch([arm(sh[1])]) if sh[0] == 'stalk' else hub(*sh[1])
        v = dHslack(b, eta)
        vals.append((float(v.lower()), sh, v))
    vals.sort(key=lambda t: t[0])
    # the degree-respecting minimum: arms with j children need j <= C
    def degok(sh):
        if sh[0] == 'stalk': return sh[1] <= C
        c, s, m1, m2 = sh[1]
        return (s + (1 if m2 else 0)) <= C
    vd = [t for t in vals if degok(t[1])]
    tl = tail_lb(SMAX + 1, eta)
    # is tail monotone increasing in j and above the min at SMAX+1?
    ok_tail = (BETA - 2 * A(eta)) > 0 and tl > vals[0][2]
    # smallest j with tail above min:
    jt = next(j for j in range(1, 200) if tail_lb(j, eta) > vals[0][2])
    res[C] = (vals[0][0], vals[0][1], vd[0][0] if vd else None, vd[0][1] if vd else None, jt, bool(ok_tail), vals[1][0], vals[1][1])
    print(C, "gamma>=%.6f %s | deg-respecting %.6f %s | tail beats min from j=%d ok=%s | 2nd %.6f %s" % res[C], flush=True)
json.dump({C: [r[0], str(r[1])] for C, r in res.items()}, open('ind_gamma.json', 'w'))
