"""Brute force for the matching-number problem: for every n in [NMIN, NMAX] and every tree T on n
vertices (networkx.nonisomorphic_trees), compute pi(T) exactly and the matching number nu(T), and
record, for every k, the maximum M(n,k) of pi over trees with nu = k and the number of
non-isomorphic trees attaining it.  The results are compared with the hull search output
../dpk215_8.txt (k <= 8) and, if present, with ../all_k/dp120_allk.txt (all k, n <= 120).

pi(T) = sum over matchings M of prod_{uv in M} 1/(deg u deg v), by the two-state tree DP
(root unmatched / root matched), in exact Fraction arithmetic.  nu(T) by the leaf-greedy rule
(a maximum matching of a tree is obtained by repeatedly matching a leaf to its neighbor), computed by
the same post-order traversal.

Written in October 2026 as an additional check.
Usage: python3 brute_force.py NMAX [NMIN]      (output on stdout, progress on stderr)
"""
import os, re, sys, time
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction as Fr
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))


def pi_and_nu(G):
    n = G.number_of_nodes()
    deg = [G.degree(v) for v in range(n)]
    order, parent = [], [-1] * n
    seen = [False] * n
    stack = [0]; seen[0] = True
    while stack:
        v = stack.pop(); order.append(v)
        for w in G[v]:
            if not seen[w]:
                seen[w] = True; parent[w] = v; stack.append(w)
    un = [None] * n   # weighted matching sum of the subtree with v unmatched
    tot = [None] * n  # weighted matching sum of the subtree
    matched = [False] * n
    nu = 0
    for v in reversed(order):
        ch = [w for w in G[v] if w != parent[v]]
        prod = Fr(1)
        for c in ch:
            prod *= tot[c]
        s = Fr(0)
        for c in ch:
            rest = Fr(1)
            for c2 in ch:
                if c2 != c:
                    rest *= tot[c2]
            s += Fr(1, deg[v] * deg[c]) * un[c] * rest
        un[v] = prod; tot[v] = prod + s
        # leaf-greedy maximum matching: match v to an unmatched child if there is one
        if any(not matched[c] for c in ch):
            matched[v] = True; nu += 1
            for c in ch:
                if not matched[c]:
                    matched[c] = True; break
    return tot[0], nu


def load(fn):
    ref = {}
    if not os.path.exists(fn):
        return None
    for line in open(fn):
        m = re.match(r'n=(\d+) k=(\d+) max=(\S+).*count=(\d+)', line)
        if m:
            ref[(int(m.group(1)), int(m.group(2)))] = (Fr(m.group(3)), int(m.group(4)))
    return ref


def main():
    NMAX = int(sys.argv[1]); NMIN = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    ref8 = load(os.path.join(HERE, "..", "dpk215_8.txt"))
    refall = load(os.path.join(HERE, "..", "all_k", "dp120_allk.txt"))
    trees = pairs = cmp8 = cmpall = 0
    bad = []
    t0 = time.time()
    for n in range(NMIN, NMAX + 1):
        best = {}
        for G in nx.nonisomorphic_trees(n):
            p, k = pi_and_nu(G); trees += 1
            if k not in best or p > best[k][0]:
                best[k] = [p, 1]
            elif p == best[k][0]:
                best[k][1] += 1
        for k in sorted(best):
            p, c = best[k]; pairs += 1
            print(f"n={n} k={k} max={p} count={c}")
            for name, ref in (("dpk215_8", ref8), ("dp120_allk", refall)):
                if ref is None or (n, k) not in ref or (name == "dpk215_8" and k > 8):
                    continue
                if name == "dpk215_8":
                    cmp8 += 1
                else:
                    cmpall += 1
                if ref[(n, k)] != (p, c):
                    bad.append((name, n, k, p, c, ref[(n, k)]))
        sys.stdout.flush()
        print(f"# n={n} done, {time.time() - t0:.0f} s", file=sys.stderr, flush=True)
    print(f"# trees enumerated: {trees}; pairs (n,k): {pairs}")
    print(f"# compared with dpk215_8.txt (k<=8): {cmp8} pairs; with all_k/dp120_allk.txt: {cmpall} pairs")
    for b in bad:
        print("# MISMATCH", b)
    print("# RESULT:", "PASS (values and numbers of maximizers agree)" if not bad else "FAIL")


if __name__ == "__main__":
    main()
