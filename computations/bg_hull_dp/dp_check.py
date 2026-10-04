"""Independent cross-check of dp.py (different structure, filter, hull and tie handling).

Structure: unbounded-knapsack over branch SIZES.  For t = 1, 2, ..., n-1 (in this order):
    H[t] is final once all bundles with child sizes <= t-1 are final;
    then, for c = 1, 2, ... and every s,  B(s,c) <- K( B(s,c)  U  B(s-t,c-1) (x) H[t] ),
so each child multiset is generated with its children in nondecreasing size order.
After step t, B(s,c) = K(bundles of c children, s vertices, all child sizes <= t).

Points are Node objects (exact Fractions) with a list of DAG backpointers; identical values are
merged into one node whose backpointer list is the union.  All maximizing trees are enumerated
from the DAG at the end (not carried as payloads during the DP).

Hull K: strict vertex hull of the Pareto set (collinear points REMOVED), then every candidate is
tested exactly for membership in one of the hull edges with nonzero-length and negative slope
(or equality with a vertex).  Float prefilter: H-representation test -- a candidate is discarded
only if it satisfies every facet inequality of the float hull with relative slack 2*TAU,
which (float error <= 5u << TAU) certifies it lies in the interior of the down-closed hull.

Usage: OMP_NUM_THREADS=1 python3 dp_check.py NMAX [out]
"""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np
from fractions import Fraction as Fr
import networkx as nx

TAU = 1e-9
sys.setrecursionlimit(100000)


class Node:
    __slots__ = ("x", "y", "back", "kind")

    def __init__(self, x, y, kind):
        self.x, self.y, self.kind, self.back = x, y, kind, []


def hull_K(nodes):
    """nodes: dict (x,y)->Node.  Exact K via strict vertex hull + edge membership."""
    pts = sorted(nodes.keys())                   # x asc, y asc
    # strict Pareto maxima
    par = []
    ybest = None
    for p in reversed(pts):                      # x desc
        if ybest is None or p[1] > ybest:
            par.append(p); ybest = p[1]
    par.reverse()                                # x asc, y strictly desc
    V = []
    for p in par:                                # strict upper hull (collinear removed)
        while len(V) >= 2:
            a, b = V[-2], V[-1]
            if (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) >= 0:
                V.pop()
            else:
                break
        V.append(p)
    keep = set(V)
    for p in par:
        if p in keep:
            continue
        for a, b in zip(V, V[1:]):
            if a[0] < p[0] < b[0] and \
                    (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) == 0:
                keep.add(p)
                break
    return {p: nodes[p] for p in keep}


def interior_mask(fx, fy, cx, cy):
    """True where candidate (cx,cy) certifiably lies in the interior of the down-closed
    convex hull of the float points (fx, fy)."""
    order = np.lexsort((fy, fx))
    xs, ys = fx[order], fy[order]
    # Pareto + strict hull on floats (any sub-chain is admissible: the H-rep test is
    # evaluated for the polygon those points define, which is contained in D(points))
    chain = []
    for i in range(len(xs) - 1, -1, -1):
        if not chain or ys[i] > ys[chain[-1]]:
            chain.append(i)
    chain.reverse()
    V = []
    for i in chain:
        while len(V) >= 2:
            a, b = V[-2], V[-1]
            if (xs[b] - xs[a]) * (ys[i] - ys[a]) - (ys[b] - ys[a]) * (xs[i] - xs[a]) >= 0:
                V.pop()
            else:
                break
        V.append(i)
    vx, vy = xs[V], ys[V]
    lim = 1 - 2 * TAU
    ok = (cx <= lim * vx.max()) & (cy <= lim * vy.max())
    if len(V) >= 2:
        nx_ = vy[:-1] - vy[1:]                   # > 0
        ny_ = vx[1:] - vx[:-1]                   # > 0
        h = nx_ * vx[:-1] + ny_ * vy[:-1]
        lhs = np.multiply.outer(cx, nx_) + np.multiply.outer(cy, ny_)
        ok &= np.all(lhs <= lim * h, axis=1)
    return ok


def run(NMAX, log=sys.stderr):
    T0 = time.time()
    one = Fr(1)
    base = Node(one, Fr(0), "B"); base.back.append(None)
    B = {(0, 0): {(one, Fr(0)): base}}
    H = {}
    F = {}                                        # float caches for B states
    def fl(state):
        return F[state]
    def setB(key, dct):
        B[key] = dct
        ks = list(dct.keys())
        F[key] = (ks, np.array([float(k[0]) for k in ks]), np.array([float(k[1]) for k in ks]))
    setB((0, 0), B[(0, 0)])
    for t in range(1, NMAX):
        # H[t] from bundles on t-1 vertices (all child sizes <= t-1 are final now)
        hn = {}
        for c in range(0, t):
            st = B.get((t - 1, c))
            if not st:
                continue
            d = c + 1
            for (P, Q), node in st.items():
                key = (P + Q / d, P / d)
                nd = hn.get(key)
                if nd is None:
                    nd = hn[key] = Node(key[0], key[1], "H")
                nd.back.append(node)
        H[t] = hull_K(hn)
        hk = list(H[t].keys())
        hx = np.array([float(k[0]) for k in hk]); hy = np.array([float(k[1]) for k in hk])
        # add any number of size-t children
        for c in range(1, NMAX):
            for s in range(t + c - 1, NMAX):
                src = (s - t, c - 1)
                if src not in B:
                    continue
                sk, sx, sy = fl(src)
                cx = np.multiply.outer(sx, hx).ravel()
                cy = (np.multiply.outer(sy, hx) + np.multiply.outer(sx, hy)).ravel()
                cur = B.get((s, c), {})
                if cur:
                    _, ox, oy = F[(s, c)]
                    allx = np.concatenate((ox, cx)); ally = np.concatenate((oy, cy))
                else:
                    allx, ally = cx, cy
                inner = interior_mask(allx, ally, cx, cy)
                cand = np.nonzero(~inner)[0]
                if len(cand) == 0:
                    continue
                new = dict(cur)
                changed = False
                nh = len(hk)
                for g in cand:
                    i, j = divmod(int(g), nh)
                    (P, Q), (Z, W) = sk[i], hk[j]
                    key = (P * Z, Q * Z + P * W)
                    nd = new.get(key)
                    if nd is None:
                        nd = Node(key[0], key[1], "B"); new[key] = nd; changed = True
                    pair = (B[src][sk[i]], H[t][hk[j]])
                    if not any(p is pair[0] and q is pair[1] for p, q in
                               (bk for bk in nd.back if bk is not None)):
                        nd.back.append(pair)
                if changed:
                    setB((s, c), hull_K(new))
                else:
                    B[(s, c)] = new
        if log and t % 20 == 0:
            print(f"# t={t} |H|={len(H[t])} time={time.time()-T0:.1f}s", file=log, flush=True)
    # final hull sizes  and maxima
    res = {}
    for n in range(2, NMAX + 1):
        best = None; arg = []
        for c in range(1, n):
            for (P, Q), node in B.get((n - 1, c), {}).items():
                v = P + Q / c
                if best is None or v > best:
                    best, arg = v, [node]
                elif v == best:
                    arg.append(node)
        res[n] = (best, arg)
    return res, H, time.time() - T0


# ------------------------------------------------------------ enumerate trees from the DAG
_memoB, _memoH = {}, {}


def forms_B(node):
    """set of multisets (sorted tuples of planted-branch strings) realised by a bundle node."""
    r = _memoB.get(id(node))
    if r is not None:
        return r
    out = set()
    for bk in node.back:
        if bk is None:
            out.add(())
            continue
        bn, hn = bk
        for m in forms_B(bn):
            for h in forms_H(hn):
                out.add(tuple(sorted(m + (h,))))
    _memoB[id(node)] = out
    return out


def forms_H(node):
    r = _memoH.get(id(node))
    if r is not None:
        return r
    out = set()
    for bn in node.back:
        for m in forms_B(bn):
            out.add("[" + "".join(m) + "]")
    _memoH[id(node)] = out
    return out


def graph_of(bundle):
    G = nx.Graph(); G.add_node(0); cnt = [1]
    def build(s, i, parent):
        # s[i] == '[' ; returns index after the matching ']'
        v = cnt[0]; cnt[0] += 1; G.add_edge(parent, v); i += 1
        while s[i] == '[':
            i = build(s, i, v)
        return i + 1
    for b in bundle:
        build(b, 0, 0)
    return G


def is_spider(G):
    """exists centre v: height <= 3, depth-2 vertices have <= 1 child, and a depth-1 vertex
    with a leaf at depth 2 has exactly one child."""
    for v in G.nodes:
        dist = nx.single_source_shortest_path_length(G, v)
        if max(dist.values()) > 3:
            continue
        ok = True
        for u, du in dist.items():
            kids = [w for w in G[u] if dist[w] == du + 1]
            if du == 2 and len(kids) > 1:
                ok = False; break
            if du == 1 and any(G.degree(w) == 1 for w in kids) and len(kids) != 1:
                ok = False; break
        if ok:
            return True
    return False


def perL_over_prod(G):
    """pi(T) = per L / prod deg via brute matching recursion with integers (independent)."""
    root = next(iter(G.nodes))
    deg = dict(G.degree())
    par = {root: None}; order = [root]
    for u in order:
        for w in G[u]:
            if w not in par:
                par[w] = u; order.append(w)
    a = {}; b = {}                           # a: v unmatched (weight deg v), b: v matched
    for v in reversed(order):
        kids = [w for w in G[v] if par.get(w) == v]
        tot = 1
        for w in kids:
            tot *= a[w] + b[w]
        a[v] = tot * deg[v]
        bb = 0
        for w in kids:
            pr = a[w] // deg[w]
            for x in kids:
                if x != w:
                    pr *= a[x] + b[x]
            bb += pr
        b[v] = bb
    pd = 1
    for v in G.nodes:
        pd *= deg[v]
    return Fr(a[root] + b[root], pd)


if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    out = sys.argv[2] if len(sys.argv) > 2 else f"results_check_{NMAX}.txt"
    res, H, tdp = run(NMAX)
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from dp import parse_table        # only the LaTeX table parser is shared
    table = parse_table(os.path.join(os.path.dirname(os.path.abspath(__file__)), "table_maximizers.tex"))
    lines = []; bad = []; multi = []; mism = []
    for n in range(2, NMAX + 1):
        val, nodes = res[n]
        trees = []
        for nd in nodes:
            for m in forms_B(nd):
                G = graph_of(m)
                if not any(nx.is_isomorphic(G, T) for T in trees):
                    trees.append(G)
        for G in trees:
            assert G.number_of_nodes() == n and nx.is_tree(G)
            assert perL_over_prod(G) == val, n
        sp = [is_spider(G) for G in trees]
        if n >= 4 and not all(sp):
            bad.append(n)
        if len(trees) > 1:
            multi.append(n)
        tag = ""
        if n in table:
            c, arms, _ = table[n]
            S = nx.Graph(); S.add_node(0); k = 1
            for _ in range(c):
                S.add_edge(0, k); S.add_edge(k, k + 1); k += 2
            for j in arms:
                S.add_edge(0, k); u = k; k += 1
                for _ in range(j):
                    S.add_edge(u, k); S.add_edge(k, k + 1); k += 2
            hit = any(nx.is_isomorphic(S, G) for G in trees)
            tag = " table=" + ("MATCH" if hit else "MISMATCH")
            if not hit:
                mism.append(n)
        lines.append(f"n={n} M={val.numerator}/{val.denominator} count={len(trees)} "
                     f"allspider={all(sp)}{tag} |H_n|={len(H.get(n, {})) if n in H else '-'}")
    open(out, "w").write("\n".join(lines) + "\n")
    print(f"DP time {tdp:.1f}s")
    print("max |H_t| =", max(len(h) for h in H.values()))
    print("n with >1 maximizer:", multi)
    print("n>=4 with a non-spider maximizer:", bad)
    print("table mismatches:", mism)
