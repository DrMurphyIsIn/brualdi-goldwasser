from ind_common import *
import json, math
# best balanced spider per n (exact rational pi), any spider is a valid lower bound
def spider_pi(atoms):
    Z = Fr(1); S = Fr(0)
    for a in atoms: Z *= a[0]; S += a[1]
    return Z * (1 + S / len(atoms))
out = {}
lz = {}
def fl(b): return (math.log(b[0].numerator) - math.log(b[0].denominator), float(b[1]))
for n in range(7, 492):
    N = n - 1; best = None
    # all cherries / cherries + balanced arms A_s^m1 A_{s+1}^m2 (m1>=1), also L C^c (N odd)
    cands = []
    for s in range(1, N // 2 + 1):
        a1 = 2 * s + 1; a2 = 2 * s + 3
        for m1 in range(1, N // a1 + 1):
            for m2 in range(0, (N - m1 * a1) // a2 + 1):
                r = N - m1 * a1 - m2 * a2
                if r % 2: continue
                c = r // 2
                if c + m1 + m2 < 2: continue
                cands.append((c, s, m1, m2))
    if N % 2 == 0: cands.append((N // 2, 1, 0, 0))
    def fval(cf):
        c, s, m1, m2 = cf
        lC, xC = fl(CH); l1, x1 = fl(arm(s)); l2, x2 = fl(arm(s + 1))
        d = c + m1 + m2
        return c * lC + m1 * l1 + m2 * l2 + math.log(1 + (c * xC + m1 * x1 + m2 * x2) / d)
    cands.sort(key=fval, reverse=True)
    top = cands[:5]
    exact = []
    for cf in top:
        c, s, m1, m2 = cf
        atoms = [CH] * c + [arm(s)] * m1 + [arm(s + 1)] * m2
        p = spider_pi(atoms)
        exact.append((p, cf))
    p, cf = max(exact, key=lambda t: t[0])
    phi = A(p).log() - (n - 1) * LAM
    out[n] = (float(phi.lower()), cf, str(p))
json.dump(out, open('ind_spider.json', 'w'))
print("done", out[108], out[315])
