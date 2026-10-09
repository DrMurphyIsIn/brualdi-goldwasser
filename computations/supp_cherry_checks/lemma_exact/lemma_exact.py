"""Exact check of the unmatched-vertices lemma (lem:lam-monomer) on all small planted branches.

Written in October 2026 (from the statement of the lemma; it shares no code with ../lemma_M_check.py).

Statement checked: for a planted branch b with n vertices (the root has one extra edge to its parent, so its
degree is its number of children plus one) and the monomer-dimer model with edge activities lam/(d_u d_v),
    S(b, lam) := sum over vertices v of P(v unmatched)  >=  2n/(2+lam).
The slack is S(b, lam) - 2n/(2+lam); it is 0 for the cherry at every lam. Everything is computed in exact
rational arithmetic (fractions.Fraction):
the cavity probabilities by a downward pass (child excluding its parent) and an upward pass (parent excluding
the child), then P(v unmatched) = 1/(1 + sum_w x_vw q_{w->v}).

Part 1: all planted branches with at most 14 vertices (53,272 of them) at lam in {2, 3, 10, 100, 10^6}.
Part 2: all planted branches with at most 12 vertices at lam in {1/2, 7/10, 8/10, 1}.

Usage: python3 lemma_exact.py
"""
from fractions import Fraction as F



def rooted_trees(nmax):
    """All rooted unlabeled trees with 1..nmax vertices, by size. A tree is the sorted tuple of its children."""
    by_size = {1: [()]}
    for n in range(2, nmax + 1):
        # children form a multiset of trees with total size n-1; enumerate as nonincreasing sequences in a
        # fixed total order of all smaller trees (index into `order`)
        order = [t for k in range(1, n) for t in by_size[k]]
        size = {}
        for k in range(1, n):
            for t in by_size[k]:
                size[t] = k
        out = []

        def rec(rem, maxi, acc):
            if rem == 0:
                out.append(tuple(sorted(acc)))
                return
            for i in range(maxi, -1, -1):
                t = order[i]
                s = size[t]
                if s <= rem:
                    acc.append(t)
                    rec(rem - s, i, acc)
                    acc.pop()

        rec(n - 1, len(order) - 1, [])
        by_size[n] = sorted(set(out))
    return by_size


def slack(t, lam):
    """Exact S(b, lam) - 2n/(2+lam) for the planted branch t."""
    # flatten
    parent, children = [-1], [[]]
    stack = [(t, 0)]
    while stack:
        node, v = stack.pop()
        for c in node:
            u = len(parent)
            parent.append(v)
            children.append([])
            children[v].append(u)
            stack.append((c, u))
    n = len(parent)
    deg = [len(children[v]) + 1 for v in range(n)]  # every vertex has its parent edge; the root's is the plant
    x = lambda u, v: lam / (deg[u] * deg[v])
    order = list(range(n))  # parents precede children by construction
    down = [None] * n  # down[v] = P(v unmatched) in the subtree of v, edge to parent removed
    for v in reversed(order):
        s = sum((x(v, c) * down[c] for c in children[v]), F(0))
        down[v] = 1 / (1 + s)
    up = [None] * n  # up[v] = P(parent(v) unmatched) in the tree with the subtree of v removed
    for v in order:
        for c in children[v]:
            s = sum((x(v, d) * down[d] for d in children[v] if d != c), F(0))
            if parent[v] >= 0:
                s += x(v, parent[v]) * up[v]
            up[c] = 1 / (1 + s)
    total = F(0)
    for v in range(n):
        s = sum((x(v, c) * down[c] for c in children[v]), F(0))
        if parent[v] >= 0:
            s += x(v, parent[v]) * up[v]
        total += 1 / (1 + s)
    return total - F(2 * n) / (2 + lam), n


def run(nmax, lams, label):
    trees = rooted_trees(nmax)
    count = sum(len(trees[k]) for k in range(1, nmax + 1))
    print(f"{label}: {count} planted branches with at most {nmax} vertices")
    for lam in lams:
        viol, zero, best = 0, [], None
        for k in range(1, nmax + 1):
            for t in trees[k]:
                s, n = slack(t, lam)
                if s < 0:
                    viol += 1
                if s == 0:
                    zero.append(t)
                if t != ((),) and (best is None or s < best[0]):
                    best = (s, n, t)
        s, n, t = best
        print(f"  lam = {str(lam):>8}: violations {viol:6d}; min slack over the other branches {float(s):+.6f} (n = {n}); "
              f"slack exactly 0 for {len(zero)} branch(es){': the cherry' if zero == [((),)] else ''}", flush=True)


if __name__ == "__main__":
    run(14, [F(2), F(3), F(10), F(100), F(10**6)], "Part 1")
    run(12, [F(1, 2), F(7, 10), F(8, 10), F(1)], "Part 2")
