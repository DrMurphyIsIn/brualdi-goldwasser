"""Exact hull DP for the Brualdi-Goldwasser maximum Laplacian ratio.

    M_n = max { pi(T) : T a tree on n vertices },  pi(T) = per L(T) / prod deg
        = sum over matchings of prod_{uv in M} 1/(deg u deg v).

Planted branch (joined by one edge to an outside parent), root with c children, degree d = c+1:
    Z = P + Q/d,  W = P/d,   P = prod Z_i,  Q = sum_i W_i prod_{j != i} Z_j,
and at an (unplanted) root with k children  pi = P + Q/k.

States (all sets are sets of exact rational points, each carrying the list of trees realising it):
    H[m]      planted branches with m vertices, point (Z, W)
    B[s][c]   ordered/unordered bundles of c branches, s vertices in total, point (P, Q)
Recurrences:
    B[0][0] = {(1,0)},   B[s][c] = K( U_j  B[s-j][c-1] (x) H[j] ),   (P,Q)(x)(Z,W) = (PZ, QZ+PW)
    H[m]    = K( U_c { (P+Q/(c+1), P/(c+1)) : (P,Q) in B[m-1][c] } )
    M_n     = max_k max_{(P,Q) in B[n-1][k]} P + Q/k
where K(S) = the points of S that maximise some STRICTLY positive linear functional over S
(upper-right hull vertices plus points on hull edges, identical values merged, all trees kept).
Correctness: see the paper, Section 5 (prop:bgx-dp).  Every tree attaining M_n is recovered.

Arithmetic: a float prefilter discards a candidate only when a float convex combination of two
other candidates certifiably dominates it by a relative margin 2*TAU in BOTH coordinates;
float inputs are float(Fraction) of exact values, so float candidates have relative error
<= 5u << TAU and every discarded point is strictly dominated by a convex combination of true
candidates, hence not in K.  Survivors are recomputed exactly (Fractions) and K is taken exactly.

Usage: OMP_NUM_THREADS=1 python3 dp.py NMAX [outfile]
"""
import os, sys, time, json
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np
from fractions import Fraction as Fr

TAU = 1e-9
NOFILTER = os.environ.get("DP_NOFILTER") == "1"   # sanity mode: exact K on all candidates

# ---------------------------------------------------------------- tree interning
TREES = [()]            # planted tree id -> sorted tuple of child ids ; id 0 = single vertex
TID = {(): 0}


def intern(ch):
    t = TID.get(ch)
    if t is None:
        t = len(TREES)
        TREES.append(ch)
        TID[ch] = t
    return t


# ---------------------------------------------------------------- exact K
def exact_K(pts):
    """pts: dict (x, y) exact -> set of payloads.  Return list of (x, y, payloads) in K."""
    items = sorted(pts.items(), key=lambda t: t[0])   # x asc, y asc
    # strict Pareto (distinct values; a point with a weakly larger other point is dropped)
    par = []
    for (x, y), pay in reversed(items):         # x desc, and y desc within equal x
        if par and (y <= par[-1][1]):
            continue
        par.append((x, y, pay))
    par.reverse()                               # x asc, y strictly desc
    out = []
    for p in par:
        while len(out) >= 2:
            a, b = out[-2], out[-1]
            cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
            if cross > 0:                        # b strictly below chord a-p
                out.pop()
            else:
                break
        out.append(p)
    return out


# ---------------------------------------------------------------- float prefilter
def float_survivors(X, Y):
    """Indices of candidates NOT certifiably strictly dominated by a convex combination
    of two other candidates (conservative; see module docstring)."""
    m = len(X)
    if m <= 1:
        return np.arange(m)
    order = np.lexsort((-Y, X))                 # x asc, y desc
    xs, ys = X[order], Y[order]
    # float upper-right chain of witnesses (any subset of candidates is admissible)
    rev = np.arange(m - 1, -1, -1)
    ymax_right = np.maximum.accumulate(ys[rev])[::-1]
    nxt = np.concatenate((ymax_right[1:], [-np.inf]))
    par = np.nonzero(ys > nxt)[0]
    ch = []
    for i in par:
        px, py = xs[i], ys[i]
        while len(ch) >= 2:
            ax, ay = xs[ch[-2]], ys[ch[-2]]
            bx, by = xs[ch[-1]], ys[ch[-1]]
            if (bx - ax) * (py - ay) - (by - ay) * (px - ax) >= 0:
                ch.pop()
            else:
                break
        ch.append(i)
    cx, cy = xs[ch], ys[ch]
    tx = (1 + 3 * TAU) * X
    idx = np.searchsorted(cx, tx, side='left')
    keep = np.ones(m, dtype=bool)
    k = len(cx)
    inside = idx < k
    # single witness (idx == 0)
    s0 = inside & (idx == 0)
    j0 = np.nonzero(s0)[0]
    if len(j0):
        dom = (cx[0] >= (1 + 2 * TAU) * X[j0]) & (cy[0] >= (1 + 2 * TAU) * Y[j0])
        keep[j0[dom]] = False
    s1 = inside & (idx > 0)
    j1 = np.nonzero(s1)[0]
    if len(j1):
        b = idx[j1]; a = b - 1
        lam = (cx[b] - tx[j1]) / (cx[b] - cx[a])
        lam = np.clip(lam, 0.0, 1.0)
        mu = 1.0 - lam
        wx = lam * cx[a] + mu * cx[b]
        wy = lam * cy[a] + mu * cy[b]
        dom = (wx >= (1 + 2 * TAU) * X[j1]) & (wy >= (1 + 2 * TAU) * Y[j1])
        keep[j1[dom]] = False
    return np.nonzero(keep)[0]


class Hull:
    __slots__ = ("x", "y", "pay", "fx", "fy")

    def __init__(self, K):
        self.x = [p[0] for p in K]
        self.y = [p[1] for p in K]
        self.pay = [p[2] for p in K]
        self.fx = np.array([float(v) for v in self.x])
        self.fy = np.array([float(v) for v in self.y])

    def __len__(self):
        return len(self.x)


def run(NMAX, log=sys.stderr):
    one = Fr(1)
    H = {1: Hull([(one, one, {0})])}
    B = {0: {0: Hull([(one, Fr(0), {()})])}}
    results = {}
    stats = {}
    for s in range(1, NMAX):
        B[s] = {}
        for c in range(1, s + 1):
            blocks = []
            for j in range(1, s - c + 2):
                bg = B[s - j].get(c - 1)
                if bg is None:
                    continue
                hg = H[j]
                X = np.multiply.outer(bg.fx, hg.fx).ravel()
                Y = (np.multiply.outer(bg.fy, hg.fx) + np.multiply.outer(bg.fx, hg.fy)).ravel()
                blocks.append((X, Y, bg, hg))
            if not blocks:
                continue
            X = np.concatenate([b[0] for b in blocks]); Y = np.concatenate([b[1] for b in blocks])
            sel = np.arange(len(X)) if NOFILTER else float_survivors(X, Y)
            offs = np.cumsum([0] + [len(b[0]) for b in blocks])
            pts = {}
            for g in sel:
                blk = int(np.searchsorted(offs, g, side='right') - 1)
                _, _, bg, hg = blocks[blk]
                r = int(g - offs[blk]); bi, hi = divmod(r, len(hg))
                P = bg.x[bi] * hg.x[hi]
                Q = bg.y[bi] * hg.x[hi] + bg.x[bi] * hg.y[hi]
                S = pts.setdefault((P, Q), set())
                for bun in bg.pay[bi]:
                    for t in hg.pay[hi]:
                        S.add(tuple(sorted(bun + (t,))))
            B[s][c] = Hull(exact_K(pts))
        # planted branches with s+1 vertices, and the unrooted maximum on s+1 vertices
        pts = {}
        best = None; bestpay = []
        for c, bg in B[s].items():
            d = c + 1
            for P, Q, pay in zip(bg.x, bg.y, bg.pay):
                S = pts.setdefault((P + Q / d, P / d), set())
                for bun in pay:
                    S.add(intern(bun))
                v = P + Q / c
                if best is None or v > best:
                    best, bestpay = v, [(c, bun) for bun in pay]
                elif v == best:
                    bestpay += [(c, bun) for bun in pay]
        H[s + 1] = Hull(exact_K(pts))
        results[s + 1] = (best, [b for _, b in bestpay])
        stats[s + 1] = dict(H=len(H[s + 1]), Bmax=max(len(g) for g in B[s].values()),
                            Btot=sum(len(g) for g in B[s].values()))
        if log and (s + 1) % 20 == 0:
            print(f"# n={s+1} |H|={stats[s+1]['H']} max|B|={stats[s+1]['Bmax']} "
                  f"sum|B|={stats[s+1]['Btot']} t={time.time()-T0:.1f}s", file=log, flush=True)
    return results, stats, H


# ---------------------------------------------------------------- tree utilities
def adj_of_bundle(bun):
    """unrooted tree (adjacency lists) from a root bundle (tuple of planted tree ids)."""
    adj = [[]]
    def add(tid, parent):
        v = len(adj); adj.append([parent]); adj[parent].append(v)
        for c in TREES[tid]:
            add(c, v)
    sys.setrecursionlimit(10000)
    for t in bun:
        add(t, 0)
    return adj


def canon(adj):
    """canonical string of an unrooted tree (AHU at the centre / bicentre)."""
    n = len(adj)
    if n == 1:
        return "()"
    deg = [len(a) for a in adj]
    layer = [v for v in range(n) if deg[v] == 1]
    rem = n
    while rem > 2:
        rem -= len(layer); nl = []
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


def pi_exact(adj):
    """pi via the matching DP (independent of the cavity recursion)."""
    n = len(adj); deg = [len(a) for a in adj]
    order = []; par = [-1] * n; seen = [False] * n; st = [0]; seen[0] = True
    while st:
        v = st.pop(); order.append(v)
        for u in adj[v]:
            if not seen[u]:
                seen[u] = True; par[u] = v; st.append(u)
    f0 = [None] * n; f1 = [None] * n        # f0: v unmatched, f1: v matched (in subtree)
    for v in reversed(order):
        ch = [u for u in adj[v] if u != par[v]]
        a = 1; tot = [f0[u] + f1[u] for u in ch]
        for t in tot:
            a *= t
        b = Fr(0)
        for i, u in enumerate(ch):
            pr = Fr(1, deg[u] * deg[v]) * f0[u]
            for j, w in enumerate(ch):
                if j != i:
                    pr *= tot[j]
            b += pr
        f0[v] = Fr(a); f1[v] = b
    return f0[0] + f1[0]


def spider_form(adj):
    """If adj is a spider (centre whose branches are leaves A0, cherries C, arms A_j, j>=1)
    return a canonical description string, else None.  Among valid centres prefer max degree."""
    n = len(adj)
    def branch_type(v, u):          # branch of centre v through neighbour u
        rest = [w for w in adj[u] if w != v]
        if not rest:
            return 0                                  # leaf  (A_0)
        if len(rest) == 1 and len(adj[rest[0]]) == 1:
            return 'C'                                # cherry: u - leaf
        j = 0
        for w in rest:                                # arm: every other neighbour is a cherry
            ww = [x for x in adj[w] if x != u]
            if len(ww) == 1 and len(adj[ww[0]]) == 1:
                j += 1
            else:
                return None
        return j
    best = None
    for v in sorted(range(n), key=lambda v: -len(adj[v])):
        types = []
        for u in adj[v]:
            t = branch_type(v, u)
            if t is None:
                break
            types.append(t)
        else:
            if n == 1:
                return "K1"
            c = types.count('C'); arms = sorted([t for t in types if t != 'C'], reverse=True)
            return fmt_spider(c, arms)
    return best


def fmt_spider(c, arms):
    s = []
    if c:
        s.append("C" if c == 1 else f"C^{c}")
    from collections import Counter
    for j, r in sorted(Counter(arms).items(), key=lambda t: -t[0]):
        s.append((f"A{j}" if r == 1 else f"A{j}^{r}"))
    return " ".join(s)


def spider_adj(c, arms):
    adj = [[]]
    def new(p):
        v = len(adj); adj.append([p]); adj[p].append(v); return v
    for _ in range(c):
        u = new(0); new(u)
    for j in arms:
        u = new(0)
        for _ in range(j):
            w = new(u); new(w)
    return adj


def parse_table(path):
    import re
    txt = open(path).read()
    out = {}
    for row in txt.split("\\\\"):
        cells = [x.strip() for x in row.split("&")]
        for i in range(0, len(cells) - 2, 3):
            m = re.search(r"(\d+)\s*$", cells[i])
            if not m or "$" not in cells[i + 1]:
                continue
            n = int(m.group(1)); desc = cells[i + 1]
            c = 0; arms = []
            for base, sub, exp in re.findall(r"\$([CA])(?:_\{(\d+)\})?(?:\^\{(\d+)\})?\$", desc):
                r = int(exp) if exp else 1
                if base == 'C':
                    c += r
                else:
                    arms += [int(sub)] * r
            out[n] = (c, arms, desc)
    return out


T0 = time.time()
if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    outf = sys.argv[2] if len(sys.argv) > 2 else f"results_dp_{NMAX}.txt"
    res, stats, H = run(NMAX)
    tdp = time.time() - T0
    table = parse_table(os.path.join(os.path.dirname(os.path.abspath(__file__)), "table_maximizers.tex"))
    lines = []; summary = dict(nonspider=[], tablemismatch=[], multi=[])
    for n in range(2, NMAX + 1):
        val, buns = res[n]
        forms = {}
        for bun in buns:
            adj = adj_of_bundle(bun)
            cf = canon(adj)
            if cf in forms:
                continue
            assert len(adj) == n
            forms[cf] = (adj, spider_form(adj))
        # exact re-verification of each maximizer by an independent matching DP
        for cf, (adj, sp) in forms.items():
            assert pi_exact(adj) == val, n
        descs = sorted(sp if sp else "NONSPIDER" for _, sp in forms.values())
        if any(sp is None for _, sp in forms.values()) and n >= 4:
            summary["nonspider"].append(n)
        if len(forms) > 1:
            summary["multi"].append(n)
        tab = ""
        if n in table:
            c, arms, desc = table[n]
            tc = canon(spider_adj(c, arms))
            ok = tc in forms
            tab = " table=" + ("MATCH" if ok else "MISMATCH")
            if not ok:
                summary["tablemismatch"].append(n)
        lines.append(f"n={n} M={val.numerator}/{val.denominator} ({float(val):.12g}) "
                     f"count={len(forms)} maximizers: " + " | ".join(descs) + tab
                     + f" |H_n|={stats[n]['H'] if n in stats else 1}")
    with open(outf, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"DP time {tdp:.1f}s total {time.time()-T0:.1f}s")
    print("max |H_m| =", max(s['H'] for s in stats.values()),
          " max |B[s][c]| =", max(s['Bmax'] for s in stats.values()))
    print("n with >1 maximizer:", summary["multi"])
    print("n>=4 with a non-spider maximizer:", summary["nonspider"])
    print("table mismatches:", summary["tablemismatch"],
          " (table covers", sum(1 for n in table if n <= NMAX), "values of n <= NMAX)")
    json.dump(dict(stats={int(k): v for k, v in stats.items()}, time=tdp),
              open(outf.replace(".txt", "_stats.json"), "w"))
