# Exhaustive check for small n, written together with rational_dp.py: for every tree on n vertices
# (networkx.nonisomorphic_trees), pi is computed by direct enumeration of all matchings (each matching
# weighted by prod 1/(deg u deg v) over its edges), in exact rational arithmetic. Prints, per n:
#   n  max pi  number of maximizing trees  whether the table spider is among them.
# Usage: python3 brute_matchings.py NMAX [NMIN]   (default NMIN = 4)
import sys, networkx as nx
from fractions import Fraction as F
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rational_dp as mydp
def pi_enum(G):
    deg = dict(G.degree()); E = list(G.edges())
    tot = F(0)
    def rec(i, used, w):
        nonlocal tot
        if i == len(E): tot += w; return
        rec(i+1, used, w)
        u, v = E[i]
        if u not in used and v not in used:
            rec(i+1, used | {u, v}, w / (deg[u]*deg[v]))
    rec(0, frozenset(), F(1)); return tot
tab = mydp.table()
for n in range(int(sys.argv[2]) if len(sys.argv)>2 else 4, int(sys.argv[1])+1):
    best = None; arg = []
    for T in nx.nonisomorphic_trees(n):
        p = pi_enum(T)
        if best is None or p > best: best, arg = p, [T]
        elif p == best: arg.append(T)
    ts = nx.Graph(); a = mydp.spider(*tab[n])
    for v, nb in enumerate(a):
        for u in nb: ts.add_edge(v, u)
    print(n, best, len(arg), any(nx.is_isomorphic(ts, T) for T in arg), flush=True)
