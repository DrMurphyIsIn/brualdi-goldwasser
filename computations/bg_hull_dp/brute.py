"""Brute force: M_n and all maximizers over ALL trees (networkx.nonisomorphic_trees), n <= NMAX.
pi(T) = per L / prod deg, per L = sum over matchings of prod_{v unmatched} deg v (integer DP).
Compares with results file of dp.py.   Usage: python3 brute.py 18 results_dp_491.txt
"""
import os, sys, re
os.environ.setdefault("OMP_NUM_THREADS", "1")
import networkx as nx
from fractions import Fraction as Fr


def perL(adj, deg):
    n = len(adj)
    par = [-1] * n; order = [0]; par[0] = 0
    for v in order:
        for u in adj[v]:
            if par[u] == -1 and u != 0:
                par[u] = v; order.append(u)
    a = [0] * n; b = [0] * n
    for v in reversed(order):
        kids = [u for u in adj[v] if u != par[v]]      # par[0] = 0 is not a neighbour
        tot = 1
        for u in kids:
            tot *= a[u] + b[u]
        a[v] = tot * deg[v]
        s = 0
        for u in kids:
            s += tot // (a[u] + b[u]) * (a[u] // deg[u])
        b[v] = s
    return a[0] + b[0]


def canon(G):
    return nx.weisfeiler_lehman_graph_hash(G, iterations=6)


if __name__ == "__main__":
    NMAX = int(sys.argv[1]); resf = sys.argv[2]
    dp = {}
    for line in open(resf):
        m = re.match(r"n=(\d+) M=(\d+)/(\d+) \S+ count=(\d+)", line)
        if m:
            dp[int(m.group(1))] = (Fr(int(m.group(2)), int(m.group(3))), int(m.group(4)))
    allok = True
    for n in range(2, NMAX + 1):
        best = None; arg = []; cnt = 0
        for T in nx.nonisomorphic_trees(n):
            cnt += 1
            adj = [list(T[v]) for v in range(n)]
            deg = [len(a) for a in adj]
            pd = 1
            for d in deg:
                pd *= d
            v = Fr(perL(adj, deg), pd)
            if best is None or v > best:
                best, arg = v, [T]
            elif v == best:
                arg.append(T)
        ok = dp[n] == (best, len(arg))
        allok &= ok
        print(f"n={n} trees={cnt} M={best} #max={len(arg)} dp={'OK' if ok else 'MISMATCH'}",
              flush=True)
    print("ALL OK" if allok else "FAILURES")
