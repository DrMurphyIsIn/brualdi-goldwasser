"""Check the lambda-family labs of the project page against an independent Python reference.

    python3 scripts/check_lambda_labs.py        # needs node and networkx

Runs the pure-function block of site/labs.js (between // LAMBDA-CORE:BEGIN and // LAMBDA-CORE:END) in node
and compares, at lambda = 1 and lambda = 4:
  * pi_lambda of every unlabeled tree with n <= 9, rooted at every vertex, computed by the lab's cavity
    recursion, with a brute-force matching sum over all matchings (exact fractions, true degrees);
  * T_b of every planted branch (every tree with n <= 9, planted at every vertex) with the planted matching
    sum (the root's degree counts the phantom parent edge);
  * M_n(lambda) for n <= 12 from the embedded tree list with the brute-force maximum over networkx's trees,
    and with the values 1, 2, 2, 5/2, 3, 29/8, 9/2, 43/8, 27/4, 65/8 (lambda = 1) and
    1, 5, 5, 10, 15, 25, 45, 70, 135, 205 (lambda = 4) for n = 1..10.
Every comparison must agree to a relative 1e-12.
"""
import json
import re
import subprocess
from fractions import Fraction
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parent.parent
TOL = 1e-12
core = re.search(r"// LAMBDA-CORE:BEGIN.*?\n(.*?)  // LAMBDA-CORE:END", (ROOT / "site/labs.js").read_text(), re.S).group(1)


def matchings(edges):
    out = [[]]
    def rec(i, used, cur):
        for k in range(i, len(edges)):
            u, v = edges[k]
            if u not in used and v not in used:
                out.append(cur + [(u, v)])
                rec(k + 1, used | {u, v}, cur + [(u, v)])
    rec(0, frozenset(), [])
    return out


def msum(edges, deg, lam):
    return sum((Fraction(1) if not M else
                __import__("math").prod(Fraction(lam) / (deg[u] * deg[v]) for u, v in M)) for M in matchings(edges))


def parents(G, r):
    order, par = [r], {r: -1}
    for v in order:
        for w in sorted(G.neighbors(v)):
            if w not in par:
                par[w] = v; order.append(w)
    idx = {v: k for k, v in enumerate(order)}
    return [-1] + [idx[par[v]] for v in order[1:]]


def trees(n):
    return [nx.empty_graph(1)] if n == 1 else list(nx.nonisomorphic_trees(n))


cases, expect = [], []
for lam in (1, 4):
    for n in range(1, 10):
        for G in trees(n):
            E = list(G.edges())
            deg = {v: G.degree(v) for v in G}
            pi = msum(E, deg, lam)
            for r in G:
                cases.append(["pi", lam, parents(G, r)]); expect.append(float(pi))
                pdeg = dict(deg); pdeg[r] += 1
                cases.append(["T", lam, parents(G, r)]); expect.append(float(msum(E, pdeg, lam)))
    for n in range(1, 13):
        best = max(msum(list(G.edges()), {v: G.degree(v) for v in G}, lam) for G in trees(n))
        cases.append(["M", lam, n]); expect.append(float(best))

KNOWN = {1: ["1", "2", "2", "5/2", "3", "29/8", "9/2", "43/8", "27/4", "65/8"],
         4: ["1", "5", "5", "10", "15", "25", "45", "70", "135", "205"]}
for lam, vals in KNOWN.items():
    for n, v in enumerate(vals, 1):
        cases.append(["M", lam, n]); expect.append(float(Fraction(v)))

js = core + """
var cases = JSON.parse(require("fs").readFileSync(0, "utf8"));
console.log(JSON.stringify(cases.map(function (c) {
  if (c[0] === "pi") return wholePi(parToBr(c[2]), c[1]);
  if (c[0] === "T") return brT(parToBr(c[2]), c[1]);
  return maxPi(c[2], c[1]).v;
})));
"""
got = json.loads(subprocess.run(["node", "-e", js], input=json.dumps(cases), capture_output=True, text=True, check=True).stdout)
bad = [(c, e, g) for c, e, g in zip(cases, expect, got) if abs(g - e) > TOL * max(1.0, abs(e))]
for b in bad[:10]:
    print("MISMATCH", b)
kinds = {k: sum(1 for c in cases if c[0] == k) for k in ("pi", "T", "M")}
print(f"{len(cases)} comparisons ({kinds['pi']} rooted trees, {kinds['T']} planted branches, {kinds['M']} maxima): "
      + ("all agree to 1e-12" if not bad else f"{len(bad)} MISMATCHES"))
raise SystemExit(1 if bad else 0)
