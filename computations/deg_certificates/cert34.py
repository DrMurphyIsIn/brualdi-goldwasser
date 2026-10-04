"""Independent interval-arithmetic check of the Delta=3,4 hand certificates of lem:deg-cert34."""
import os, itertools
os.environ["OMP_NUM_THREADS"] = "1"
from mpmath import iv, mpf
iv.dps = 60

def check(D, thI):
    t = ((2*D-1) + iv.sqrt(iv.mpf((2*D-1)**2 + 9)))/(3*D)
    mu = iv.mpf(1.5)**(D-2)*t
    F = iv.log(mu)/(2*D-3)
    eta = 1/(D*t)
    thL = F - iv.log(1+eta)
    thC = 2*F - iv.log(iv.mpf(1.5)) - iv.log(1+eta/3)
    thJ = thC
    thI = iv.mpf(thI)
    I = (iv.mpf(2)/5, iv.mpf(2*D-1)/(4*D-1)); J = (iv.mpf(1)/(2*D-1), iv.mpf(2*D-1)/(6*D-1))
    types = {'L': ((iv.mpf(1),), thL), 'C': ((iv.mpf(1)/3,), thC), 'I': (I, thI), 'J': (J, thJ)}
    print(f"Delta={D}: F={F.mid} eta={eta.mid} thL={float(thL.mid):.4f} thC={float(thC.mid):.4f} thI={thI.mid}")
    rules = []
    for m in range(1, D):
        for ms in itertools.combinations_with_replacement('LCIJ', m):
            if m == 1:
                tgt = 'C' if ms == ('L',) else 'I'
            else:
                tgt = 'J'
            rules.append((ms, tgt))
    out = []
    for ms, tgt in rules:
        corners = itertools.product(*[types[x][0] for x in ms])
        best = None
        for c in corners:
            R = sum(c, iv.mpf(0))
            G = iv.log((m1 := len(ms)) + 1 + eta + R) - iv.log(m1 + 1)
            for y in c: G -= iv.log(1 + eta*y)
            best = G if best is None else iv.mpf([max(best.a, G.a), max(best.b, G.b)])
        slack = F + sum((types[x][1] for x in ms), iv.mpf(0)) - types[tgt][1] - best
        kind = 'identity' if (ms, tgt) == (('L',), 'C') else ('spine' if (len(ms) == D-1 and ms.count('C') >= D-2) else 'generic')
        out.append((kind, ''.join(ms)+'->'+tgt, slack))
    # spine rules: exactly D-2 cherries plus one more type; count
    for kind, name, sl in sorted(out, key=lambda r: float(r[2].a)):
        print(f"  {kind:8s} {name:8s} slack in [{float(sl.a):.3e}, {float(sl.b):.3e}]")
    kinds = [k for k, _, _ in out]
    print("  counts:", len(out), {k: kinds.count(k) for k in set(kinds)},
          " generic all >0:", all(sl.a > 0 for k, _, sl in out if k == 'generic'),
          " spine/identity >= 0 (up to 1e-50):", all(sl.a > -1e-50 for k, _, sl in out if k != 'generic'))

check(3, -0.0813)
check(4, -0.0391)
