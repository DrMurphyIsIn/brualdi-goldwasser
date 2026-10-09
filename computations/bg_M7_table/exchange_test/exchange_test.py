"""Test of the exchanges (M1)-(M7) on explicit trees: for every tree with
NMIN <= n <= NMAX vertices (networkx.nonisomorphic_trees) and every vertex p at which the hypotheses of an
exchange hold, the exchange is carried out on the tree, the result is checked to be a tree on n vertices, and
pi is compared before and after.  pi is computed by a matching DP on the tree (not by the cavity formula of
the proof); in floating point first, and in exact Fraction arithmetic whenever the relative gain is < 1e-9.
A FAIL line is printed for every exchange that does not strictly increase pi.
Counts in the output are cumulative over n.
Usage: python3 exchange_test.py NMAX [NMIN]"""
import os, sys
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction as Fr
import networkx as nx
from collections import defaultdict

def pi_dp(adj, one=1.0):
    n = len(adj)
    deg = [len(a) for a in adj]
    order = []; par = [-1] * n; st = [0]; seen = [False] * n; seen[0] = True
    while st:
        v = st.pop(); order.append(v)
        for w in adj[v]:
            if not seen[w]:
                seen[w] = True; par[w] = v; st.append(w)
    assert len(order) == n, 'not connected'
    f0 = [None] * n; f1 = [None] * n
    for v in reversed(order):
        prod = one; s = 0 * one
        ch = [c for c in adj[v] if c != par[v]]
        tot = [f0[c] + f1[c] for c in ch]
        for t in tot: prod *= t
        for c, t in zip(ch, tot):
            s += one / (deg[v] * deg[c]) * f0[c] * prod / t
        f0[v] = prod; f1[v] = s
    return f0[0] + f1[0]

def children(adj, v, p):
    return [w for w in adj[v] if w != p]

def classify(adj, w, p):
    ch = children(adj, w, p)
    if not ch: return ('L',)
    cls = [classify(adj, c, w) for c in ch]
    if len(ch) == 1 and cls[0] == ('L',): return ('C',)
    if all(c == ('C',) for c in cls): return ('A', len(ch))
    if len(ch) == 1: return ('St', cls[0])
    return ('X', tuple(sorted(cls)))

def branch_vertices(adj, w, p):
    out = []; st = [(w, p)]
    while st:
        v, q = st.pop(); out.append(v)
        for x in adj[v]:
            if x != q: st.append((x, v))
    return out

# atom builders: return list of edges on new labels, root label, given a counter
def build(kind, nxt):
    """kind: 'L','C',('A',j). returns (root, edges, nxt)"""
    if kind == 'L' or kind == ('A', 0):
        return nxt, [], nxt + 1
    if kind == 'C':
        return nxt, [(nxt, nxt + 1)], nxt + 2
    j = kind[1]; r = nxt; nxt += 1; E = []
    for _ in range(j):
        E += [(r, nxt), (nxt, nxt + 1)]; nxt += 2
    return r, E, nxt

def exchange(adj, p, Oroots, Nkinds):
    """remove branches at p rooted at Oroots; attach atoms Nkinds at p. returns new adjacency."""
    n = len(adj)
    rm = set()
    for w in Oroots: rm |= set(branch_vertices(adj, w, p))
    keep = [v for v in range(n) if v not in rm]
    lab = {v: i for i, v in enumerate(keep)}
    E = [(lab[u], lab[v]) for u in keep for v in adj[u] if v in lab and u < v]
    nxt = len(keep)
    for k in Nkinds:
        r, e, nxt = build(k, nxt)
        E += e + [(lab[p], r)]
    return mkadj(nxt, E)

def mkadj(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    return adj

def size_kind(k):
    if k == 'L' or k == ('A', 0): return 1
    if k == 'C': return 2
    return 2 * k[1] + 1

FAILS = []
stats = defaultdict(lambda: [0, None, None])  # count, min rel gain, witness

def judge(tag, adj, new, n):
    assert len(new) == n, (tag, 'vertex count')
    assert sum(len(a) for a in new) == 2 * (n - 1), (tag, 'edge count')
    a = pi_dp(adj); b = pi_dp(new)
    rel = (b - a) / a
    if rel < 1e-9:
        ae = pi_dp(adj, Fr(1)); be = pi_dp(new, Fr(1))
        rel = float((be - ae) / ae)
        if be <= ae:
            FAILS.append(tag)
            print('FAIL', tag, n, [sorted(x) for x in adj], flush=True)
    s = stats[tag]; s[0] += 1
    if s[1] is None or rel < s[1]:
        s[1] = rel; s[2] = (n, tuple(tuple(sorted(x)) for x in adj))

def arm_j(c):
    if c == ('L',): return 0
    if c[0] == 'A': return c[1]
    return None

def test_tree(adj):
    n = len(adj)
    for p in range(n):
        k = len(adj[p])
        nb = adj[p]
        cl = {w: classify(adj, w, p) for w in nb}
        leaves = [w for w in nb if cl[w] == ('L',)]
        cher = [w for w in nb if cl[w] == ('C',)]
        # (M1)
        if len(leaves) >= 2 and k >= 3:
            judge('M1', adj, exchange(adj, p, leaves[:2], ['C']), n)
        # (M2), D0 >= 2
        if leaves and cher:
            if k >= 4:
                judge('M2', adj, exchange(adj, p, [leaves[0], cher[0]], [('A', 1)]), n)
        # (M3)
        if len(leaves) == 1 and k >= 3:
            l = leaves[0]
            rest_has_leaf = False
            for w in nb:
                if w == l or cl[w] in (('C',), ('L',)): continue
                chw = children(adj, w, p)
                if sum(1 for c in chw if len(adj[c]) == 1) > 1: continue
                # rest = nb minus {l, w}: no leaf (true since only one leaf at p)
                # rewire: children of w -> p ; l -> w
                E = [(u, v) for u in range(n) for v in adj[u] if u < v]
                Eset = set(frozenset(e) for e in E)
                for c in chw:
                    Eset.discard(frozenset((w, c))); Eset.add(frozenset((p, c)))
                Eset.discard(frozenset((p, l))); Eset.add(frozenset((w, l)))
                new = mkadj(n, [tuple(e) for e in Eset])
                judge('M3', adj, new, n)
        # (M4) balance, deg >= 3
        if k >= 3:
            arms = [(arm_j(cl[w]), w) for w in nb if arm_j(cl[w]) is not None]
            for (x, wx) in arms:
                for (y, wy) in arms:
                    if wx != wy and x >= y + 2:
                        judge('M4 (balance)', adj, exchange(adj, p, [wx, wy], [('A', x - 1), ('A', y + 1)]), n)
        # (M5): P5 branch, deg >= 2
        if k >= 2:
            for w in nb:
                if cl[w] == ('St', ('St', ('A', 1))):
                    judge('M5', adj, exchange(adj, p, [w], [('A', 2)]), n)
        # (M6): stalk [A_j], j>=5, at p with deg >= 2 ; exchange at the stalk vertex w
        if k >= 2:
            for w in nb:
                c = cl[w]
                if c[0] == 'St' and c[1][0] == 'A' and c[1][1] >= 5:
                    v = children(adj, w, p)[0]
                    j = c[1][1]
                    judge('M6', adj, exchange(adj, w, [v], ['C', ('A', j - 1)]), n)
        # (M7) stalk exchanges, deg >= 3, rest with at most one leaf
        if k >= 3:
            stalks = [(cl[w][1][1], w) for w in nb if cl[w][0] == 'St' and cl[w][1][0] == 'A' and cl[w][1][1] <= 4]
            for (j, ws) in stalks:
                for w2 in nb:
                    if w2 == ws: continue
                    restleaves = sum(1 for w in nb if w not in (ws, w2) and cl[w] == ('L',))
                    if restleaves > 1: continue
                    c2 = cl[w2]; N = None; tag = None
                    if j == 1 and arm_j(c2) is not None:
                        i = arm_j(c2); N = ['C', ('A', i + 1)]; tag = 'M7(i)'
                    elif j == 1 and c2 == ('C',):
                        N = ['C'] * 3; tag = 'M7(ii)'
                    elif j >= 2 and arm_j(c2) is not None and arm_j(c2) >= 1:
                        i = arm_j(c2); N = ['C', ('A', i + j)]; tag = 'M7(iv)'
                    elif c2 == ('L',):
                        N = ['C', ('A', j)]; tag = 'M7(v)'
                    elif c2 == ('C',):
                        N = {2: [('A', 1), ('A', 2)], 3: [('A', 1), ('A', 3)], 4: ['C', ('A', 2), ('A', 2)]}[j]; tag = 'M7(vi), stalk and cherry'
                    elif c2[0] == 'St' and c2[1][0] == 'A' and c2[1][1] <= j:
                        kk = c2[1][1]
                        Njk = {(1, 1): ['C'] * 4, (2, 1): ['C'] * 5, (2, 2): ['C'] * 6, (3, 1): ['C'] * 6, (4, 1): ['C'] * 7,
                               (3, 2): ['L', ('A', 6)], (3, 3): ['L', 'C', ('A', 6)], (4, 2): ['L', 'C', ('A', 6)],
                               (4, 3): ['L', 'C', ('A', 7)], (4, 4): ['L', 'C', ('A', 8)]}
                        N = Njk[(j, kk)]; tag = 'M7(iii) and (vi), two stalks'
                    if N is None: continue
                    osz = 2 * j + 2 + sum(1 for _ in branch_vertices(adj, w2, p))
                    assert osz == sum(size_kind(x) for x in N), (tag, j, c2)
                    judge(tag, adj, exchange(adj, p, [ws, w2], N), n)

if __name__ == '__main__':
    NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    for n in range(NMIN, NMAX + 1):
        cnt = 0
        for G in nx.nonisomorphic_trees(n):
            adj = mkadj(n, list(G.edges())); cnt += 1
            test_tree(adj)
        print('n', n, 'trees', cnt, flush=True)
        for tag, s in sorted(stats.items()):
            print('   ', tag, 'instances', s[0], 'min rel gain', s[1], flush=True)
    print('total instances', sum(s[0] for s in stats.values()), 'failures', len(FAILS))
