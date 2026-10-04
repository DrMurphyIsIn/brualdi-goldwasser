"""Rigorous verification of the Bellman potential for the degree-capped problem.

usage: python3 verify.py Delta K [--save]

1. Types: singletons L (x=1), K (cherry, x=1/3), C5 (x=3/23, only if Delta>=6) and K intervals in each
   of the two message windows  B = [1/(2D-1), (2D-1)/(6D-1)]  (root has >= 2 children) and
   A = [2/5, (2D-1)/(4D-1)]  (root has 1 non-leaf child).  Every planted branch with max degree <= D
   has its message in {1, 1/3} or in A or in B (proved in the paper), so the types cover everything.
2. Singleton potentials are EXACT:  k_s = |s| lam - log Z_s - log(1 + b x_s).
3. Rules: every multiset of 1..D-1 child types and every target type meeting the parent's message range.
   Three kinds:
     identity  : children = the defining children of a singleton target (L->K, 5K->C5); slack == 0 exactly.
     chain     : children = spine sides + one port type I.  Exact algebra (b(d+b+S_side)=1 and
                 size*lam = log(P t)) gives slack == k_I - k_target exactly.
     generic   : slack = lam + sum k_i - k_t - sup_box G  must be > 0 (checked in interval arithmetic).
4. Interval-type potentials k_t are found by an LP (maximise the minimum generic slack), rounded to
   rationals, then chain constraints are re-imposed exactly by downward propagation.
5. Verification in mpmath interval arithmetic (outward rounding) at 256 bits.
"""
import sys, math, itertools, json
from fractions import Fraction as Fr
from collections import Counter
import numpy as np
from scipy.optimize import linprog
from mpmath import iv, mp
import potential as P

iv.prec = 256


def ivq(fr):
    fr = Fr(fr)
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def setup(D, K):
    nK, nC = P.SIDES[D]
    sc = P.spine_constants(D, nK, nC)
    types = P.make_types(D, K, nC)
    names = [t[0] for t in types]
    # exact constants as intervals
    t_iv = (ivq(sc['A']) + iv.sqrt(ivq(sc['disc']))) / 2
    mu_iv = ivq(sc['P']) * t_iv
    lam_iv = iv.log(mu_iv) / sc['size']
    b_iv = 1 / (sc['d'] * t_iv)
    lam, b, mu = P.floats(sc)
    struct = {'L': LEAFS, 'K': KS, 'C5': C5S}
    kex_iv, kex_f = {}, {}
    for i, nm in enumerate(names):
        if nm in struct:
            size, Z, x = struct[nm]
            kex_iv[i] = size * lam_iv - iv.log(ivq(Z)) - iv.log(1 + b_iv * ivq(x))
            kex_f[i] = size * lam - math.log(Z) - math.log(1 + b * float(x))
    sides = Counter()
    sides[names.index('K')] += nK
    if nC:
        sides[names.index('C5')] += nC
    return dict(D=D, K=K, sc=sc, types=types, names=names, lam=lam, b=b, mu=mu,
                lam_iv=lam_iv, b_iv=b_iv, kex_iv=kex_iv, kex_f=kex_f, sides=sides)


LEAFS = (1, Fr(1), Fr(1))
KS = (2, Fr(3, 2), Fr(1, 3))
C5S = (11, Fr(621, 64), Fr(3, 23))
IDENT = {'K': ('L',), 'C5': ('K',) * 5}


def G_iv(xs, b_iv):
    d = len(xs) + 1
    S = sum((ivq(x) for x in xs), iv.mpf(0))
    val = iv.log((d + S + b_iv) / d)
    for x in xs:
        val -= iv.log(1 + b_iv * ivq(x))
    return val


def classify(st, combo, t):
    names = st['names']
    tn = names[t]
    if tn in IDENT and tuple(sorted(names[c] for c in combo)) == tuple(sorted(IDENT[tn])):
        return ('identity', None)
    rest = Counter(combo) - st['sides']
    if sum(st['sides'].values()) + 1 == len(combo) and sum(rest.values()) == 1 \
            and not (st['sides'] - Counter(combo)):
        return ('chain', next(iter(rest)))
    return ('generic', None)


def build_rules(st):
    D, types = st['D'], st['types']
    live = list(range(len(types)))
    out = []
    for combo, targets in P.rules(D, types, live):
        corners = list(P.corner_sets(combo, types))
        gf = max(P.G_float([float(x) for x in xs], st['b']) for xs in corners)
        for t in targets:
            kind, port = classify(st, combo, t)
            out.append(dict(combo=combo, t=t, kind=kind, port=port, gf=gf, corners=corners))
    return out


def solve_lp(st, rules, eps_chain=1e-9):
    types, kex = st['types'], st['kex_f']
    var = [i for i in range(len(types)) if i not in kex]
    vidx = {v: j for j, v in enumerate(var)}
    n = len(var) + 1  # last = s
    A, ub = [], []
    for r in rules:
        row = np.zeros(n)
        if r['kind'] == 'identity':
            continue
        if r['kind'] == 'chain':
            # k_port - k_t >= eps  ->  -k_port + k_t <= -eps
            const = 0.0
            I, t = r['port'], r['t']
            if I in vidx: row[vidx[I]] -= 1
            else: const += kex[I]
            if t in vidx: row[vidx[t]] += 1
            else: const -= kex[t]
            eps = 0.0 if (I in vidx and t in vidx) else eps_chain
            A.append(row); ub.append(const - eps)
            continue
        # lam + sum k_i - k_t - gf >= s  ->  -sum k_i + k_t + s <= lam - gf + (exact parts)
        const = st['lam'] - r['gf']
        for c in r['combo']:
            if c in vidx: row[vidx[c]] -= 1
            else: const += kex[c]
        if r['t'] in vidx: row[vidx[r['t']]] += 1
        else: const -= kex[r['t']]
        row[-1] = 1
        A.append(row); ub.append(const)
    cobj = np.zeros(n); cobj[-1] = -1
    bounds = [(-5, 5)] * len(var) + [(None, 1)]
    res = linprog(cobj, A_ub=np.array(A), b_ub=np.array(ub), bounds=bounds, method='highs')
    if res.status != 0:
        raise RuntimeError(res.message)
    k = dict(kex)
    for v in var:
        k[v] = res.x[vidx[v]]
    return k, res.x[-1], var


def rationalize(st, rules, kf, var, s):
    """round interval-type k to rationals (denominator 2^40) a bit below, then enforce chain rules."""
    q = {}
    shift = min(abs(s) / 10, 1e-7)
    for v in var:
        q[v] = Fr(math.floor((kf[v] - shift) * 2**40), 2**40)
    changed = True
    while changed:
        changed = False
        for r in rules:
            if r['kind'] == 'chain' and r['port'] in q and r['t'] in q and q[r['t']] > q[r['port']]:
                q[r['t']] = q[r['port']]; changed = True
    return q


def verify(st, rules, q):
    kiv = dict(st['kex_iv'])
    for v, fr in q.items():
        kiv[v] = ivq(fr)
    lam_iv, b_iv = st['lam_iv'], st['b_iv']
    worst = None
    fails = 0
    counts = Counter()
    gcache = {}
    for r in rules:
        counts[r['kind']] += 1
        if r['kind'] == 'identity':
            continue
        if r['kind'] == 'chain':
            I, t = r['port'], r['t']
            if I in q and t in q:
                ok = q[I] >= q[t]
                sl = float(q[I] - q[t])
            else:
                d = kiv[I] - kiv[t]
                ok = d.a > 0 or (I == t)
                sl = float(d.a)
            if not ok:
                fails += 1
                print('CHAIN FAIL', r['combo'], r['t'])
            continue
        key = r['combo']
        if key not in gcache:
            g = None
            for xs in r['corners']:
                v = G_iv(xs, b_iv)
                g = v if g is None else iv.mpf([max(g.a, v.a), max(g.b, v.b)])
            gcache[key] = g
        slack = lam_iv + sum((kiv[c] for c in r['combo']), iv.mpf(0)) - kiv[r['t']] - gcache[key]
        lo = slack.a
        if not lo > 0:
            fails += 1
            print('GENERIC FAIL', [st['names'][c] for c in r['combo']], '->', st['names'][r['t']], slack)
        if worst is None or lo < worst[0]:
            worst = (lo, [st['names'][c] for c in r['combo']], st['names'][r['t']])
    return fails, worst, counts, kiv


def identity_check(st):
    """numerical sanity of the exact identities (they hold by algebra; see the paper)."""
    lam_iv, b_iv, kiv = st['lam_iv'], st['b_iv'], st['kex_iv']
    names = st['names']
    out = []
    for tn, ch in IDENT.items():
        if tn not in names: continue
        t = names.index(tn)
        xs = [{'L': Fr(1), 'K': Fr(1, 3)}[c] for c in ch]
        sl = lam_iv + sum((kiv[names.index(c)] for c in ch), iv.mpf(0)) - kiv[t] - G_iv(xs, b_iv)
        out.append((tn, sl))
    # chain bracket: lam + sum_side k_s - G(sides + x) for x = 0 and x = 1/2
    sidexs = []
    for c, m in st['sides'].items():
        sidexs += [st['types'][c][1]] * m
    for x in (Fr(0), Fr(1, 2)):
        sl = lam_iv + sum((kiv[c] * m for c, m in st['sides'].items()), iv.mpf(0)) \
            - G_iv(sidexs + [x], b_iv)
        out.append(('chain x=%s' % x, sl))
    return out


def main():
    D, K = int(sys.argv[1]), int(sys.argv[2])
    st = setup(D, K)
    rules = build_rules(st)
    kf, s, var = solve_lp(st, rules)
    print('Delta=%d K=%d  rho_D=%.15f  b=%.12f  types=%d rules=%d  LP min generic slack s*=%.3e'
          % (D, K, math.exp(st['lam']), st['b'], len(st['types']), len(rules), s))
    if s <= 0:
        print('  LP: no strictly feasible potential with this partition')
        return 1
    q = rationalize(st, rules, kf, var, s)
    fails, worst, counts, kiv = verify(st, rules, q)
    print('  rules by kind:', dict(counts))
    print('  identity sanity (should enclose 0):', [(n, '%.1e..%.1e' % (float(v.a), float(v.b))) for n, v in identity_check(st)])
    print('  worst generic slack lower bound: %.6e at %s -> %s' % (float(worst[0]), worst[1], worst[2]))
    print('  RESULT:', 'VERIFIED' if fails == 0 else 'FAILED (%d)' % fails)
    if '--save' in sys.argv:
        rec = dict(Delta=D, K=K, rho=math.exp(st['lam']), b=st['b'], sides=P.SIDES[D],
                   types=[(n, str(lo), str(hi)) for n, lo, hi in st['types']],
                   k={st['names'][i]: (str(q[i]) if i in q else 'exact') for i in range(len(st['types']))},
                   k_float={st['names'][i]: float(kiv[i].a) for i in range(len(st['types']))},
                   rules=dict(counts), worst=float(worst[0]), verified=(fails == 0))
        json.dump(rec, open('out/cert_D%d_K%d.json' % (D, K), 'w'), indent=1)
    return fails


if __name__ == '__main__':
    sys.exit(main())
