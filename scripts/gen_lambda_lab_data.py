"""Embed every unlabeled tree on n <= 12 vertices in site/labs.js, for the "never attained" lab.

    python3 scripts/gen_lambda_lab_data.py          # needs networkx

Each tree is written as a parent array in breadth-first order from vertex 0 (so parent[i] < i), one
base-36 character per non-root vertex; the trees of one size are joined by commas. The lab computes
the matching sum of every tree by the cavity recursion in the browser and takes the maximum, which is
M_n(lambda) for n <= 12. The data is written between the markers // LTREES:BEGIN and // LTREES:END.
"""
import re
from pathlib import Path

import networkx as nx

NMAX = 12
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"


def parents(G):
    order, par, seen = [0], {0: -1}, {0}
    i = 0
    while i < len(order):
        v = order[i]; i += 1
        for w in sorted(G.neighbors(v)):
            if w not in seen:
                seen.add(w); par[w] = v; order.append(w)
    idx = {v: k for k, v in enumerate(order)}
    return "".join(DIGITS[idx[par[v]]] for v in order[1:])


def trees(n):
    if n == 1:
        return [""]
    return sorted(parents(G) for G in nx.nonisomorphic_trees(n))


def main():
    rows = [",".join(trees(n)) for n in range(1, NMAX + 1)]
    counts = [len(r.split(",")) for r in rows]
    assert counts == [1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551], counts
    body = ("  // every unlabeled tree on n vertices, n = 1.." + str(NMAX) +
            ", as base-36 parent arrays (scripts/gen_lambda_lab_data.py)\n  var LTREES = [\n" +
            ",\n".join('    "' + r + '"' for r in rows) + "\n  ];\n")
    js = Path(__file__).resolve().parent.parent / "site" / "labs.js"
    s = js.read_text()
    new, k = re.subn(r"(  // LTREES:BEGIN\n).*?(  // LTREES:END\n)", lambda m: m.group(1) + body + m.group(2), s, flags=re.S)
    if k != 1:
        raise SystemExit("markers not found in site/labs.js")
    js.write_text(new)
    print("wrote", sum(counts), "trees,", len(body), "bytes")


if __name__ == "__main__":
    main()
