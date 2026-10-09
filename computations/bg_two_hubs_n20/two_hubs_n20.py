"""The two-hub tree on 20 vertices (local exchanges alone do not exclude two hubs).

Written in October 2026.

T0 = two adjacent vertices, each carrying two cherries and one arm A_2 (a vertex with two cherries), so
n = 20. Claim checked: T0 is not a maximizer, but it beats (strictly) every other tree obtained from it by at most
three edge exchanges. An edge exchange deletes one edge of a tree and reconnects the two components by another edge.

Method.
1. pi(T) = per L(T) / prod_v deg(v) is computed exactly (fractions.Fraction) by the matching-sum recursion
   pi(T) = sum over matchings M of prod_{uv in M} 1/(deg u deg v); the recursion is first compared with the
   permanent itself (Ryser's formula, exact integers) on every tree with at most 9 vertices.
2. All 823,065 trees on 20 vertices (networkx.nonisomorphic_trees) are evaluated exactly; the trees with
   pi > pi(T0) and with pi = pi(T0) are listed.
3. Exchange distance: the ball of radius 2 around T0 and the ball of radius 1 around each better tree are
   computed (trees up to isomorphism, by a canonical string of the center-rooted tree). If they are disjoint,
   every better tree is at exchange distance >= 4 from T0, so no tree within three exchanges beats T0; if
   moreover pi = pi(T0) only for T0 itself, T0 beats every other tree within three exchanges.

Usage: python3 two_hubs_n20.py
"""
from fractions import Fraction as F
from itertools import combinations
import sys, time
import networkx as nx

sys.setrecursionlimit(10000)


def pi_exact(adj):
    """sum over matchings of prod 1/(deg u deg v), by the tree recursion rooted at vertex 0."""
    n = len(adj)
    deg = [len(a) for a in adj]
    par = [-1] * n
    order, seen, st = [], [False] * n, [0]
    seen[0] = True
    while st:
        v = st.pop()
        order.append(v)
        for u in adj[v]:
            if not seen[u]:
                seen[u] = True
                par[u] = v
                st.append(u)
    free = [None] * n  # sum over matchings of the subtree of v that leave v unmatched
    tot = [None] * n   # sum over all matchings of the subtree of v
    for v in reversed(order):
        ch = [u for u in adj[v] if u != par[v]]
        p = F(1)
        for u in ch:
            p *= tot[u]
        s = F(0)
        for u in ch:
            s += F(1, deg[u] * deg[v]) * free[u] * (p / tot[u])
        free[v] = p
        tot[v] = p + s
    return tot[0]


def per_ratio(adj):
    """per L / prod deg, by Ryser's formula in exact integers (small n only)."""
    n = len(adj)
    L = [[0] * n for _ in range(n)]
    for v in range(n):
        L[v][v] = len(adj[v])
        for u in adj[v]:
            L[v][u] = -1
    total = 0
    for r in range(1, n + 1):
        for S in combinations(range(n), r):
            prod = 1
            for i in range(n):
                prod *= sum(L[i][j] for j in S)
            total += (-1) ** r * prod
    total *= (-1) ** n
    d = 1
    for a in adj:
        d *= len(a)
    return F(total, d)


def canon(adj):
    """canonical string of an unlabeled tree (rooted at its center or bicenter)."""
    n = len(adj)
    deg = [len(a) for a in adj]
    layer = [v for v in range(n) if deg[v] <= 1]
    rem = n
    while rem > 2:
        rem -= len(layer)
        nl = []
        for v in layer:
            for u in adj[v]:
                deg[u] -= 1
                if deg[u] == 1:
                    nl.append(u)
        layer = nl

    def enc(v, p):
        return "(" + "".join(sorted(enc(u, v) for u in adj[v] if u != p)) + ")"

    if len(layer) == 1:
        return enc(layer[0], -1)
    a, b = layer
    return "B" + "".join(sorted([enc(a, b), enc(b, a)]))


def from_canon(s):
    adj = []

    def parse(i, parent):
        v = len(adj)
        adj.append([])
        if parent >= 0:
            adj[v].append(parent)
            adj[parent].append(v)
        assert s[i] == "("
        i += 1
        while s[i] == "(":
            i = parse(i, v)
        return i + 1

    if s[0] == "B":
        i = parse(1, -1)
        parse(i, 0)
    else:
        parse(0, -1)
    return adj


def exchanges(adj):
    """canonical strings of all trees obtained by one edge exchange (other than the tree itself)."""
    n = len(adj)
    out = set()
    for u in range(n):
        for v in adj[u]:
            if u > v:
                continue
            comp, st = {u}, [u]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if (x, y) in ((u, v), (v, u)):
                        continue
                    if y not in comp:
                        comp.add(y)
                        st.append(y)
            A = sorted(comp)
            B = [x for x in range(n) if x not in comp]
            base = [list(a) for a in adj]
            base[u].remove(v)
            base[v].remove(u)
            for a in A:
                for b in B:
                    if (a, b) == (u, v):
                        continue
                    base[a].append(b)
                    base[b].append(a)
                    out.add(canon(base))
                    base[a].pop()
                    base[b].pop()
    out.discard(canon(adj))
    return out


def ball(adj, r):
    c0 = canon(adj)
    seen, front = {c0}, {c0}
    for _ in range(r):
        nf = set()
        for c in front:
            for c2 in exchanges(from_canon(c)):
                if c2 not in seen:
                    seen.add(c2)
                    nf.add(c2)
        front = nf
    return seen


def build_T0():
    adj = [[] for _ in range(20)]
    nxt = [2]

    def e(a, b):
        adj[a].append(b)
        adj[b].append(a)

    def new():
        v = nxt[0]
        nxt[0] += 1
        return v

    e(0, 1)
    for hub in (0, 1):
        for _ in range(2):  # two cherries
            s, l = new(), new()
            e(hub, s)
            e(s, l)
        a = new()  # arm A_2: a vertex carrying two cherries
        e(hub, a)
        for _ in range(2):
            s, l = new(), new()
            e(a, s)
            e(s, l)
    assert nxt[0] == 20
    return adj


if __name__ == "__main__":
    t0 = time.time()
    checked = 0
    for m in range(2, 10):
        for G in nx.nonisomorphic_trees(m):
            adj = [list(G[v]) for v in range(m)]
            assert pi_exact(adj) == per_ratio(adj)
            checked += 1
    print(f"recursion = per L / prod deg on all {checked} trees with 2..9 vertices")

    T0 = build_T0()
    p0 = pi_exact(T0)
    print(f"pi(T0) = {p0} = {float(p0):.10f}")
    better, equal, count = [], [], 0
    for G in nx.nonisomorphic_trees(20):
        count += 1
        adj = [list(G[v]) for v in range(20)]
        p = pi_exact(adj)
        if p > p0:
            better.append((p, adj))
        elif p == p0:
            equal.append(adj)
    print(f"trees on 20 vertices: {count}")
    print(f"trees with pi > pi(T0): {len(better)}; trees with pi = pi(T0): {len(equal)}"
          f" (T0 itself: {len(equal) == 1 and canon(equal[0]) == canon(T0)})")
    for p, adj in sorted(better, key=lambda z: -z[0]):
        print(f"  better: pi = {p} = {float(p):.10f}, degrees {sorted((len(a) for a in adj), reverse=True)[:6]}...")
    B0 = ball(T0, 2)
    print(f"exchange ball of radius 2 around T0: {len(B0)} trees (T0 included)")
    ok = True
    for i, (p, adj) in enumerate(sorted(better, key=lambda z: -z[0])):
        b1 = ball(adj, 1)
        meets = len(b1 & B0) > 0
        ok = ok and not meets
        print(f"  better tree {i}: radius-1 ball {len(b1)} trees; meets the radius-2 ball of T0: {meets}")
    print("every better tree is at exchange distance >= 4 from T0:", ok)
    print("T0 beats every other tree within three edge exchanges:", ok and len(equal) == 1)
    print(f"time {time.time() - t0:.0f} s", file=sys.stderr)
