"""Exact-structure DP for M(n,k) = max{pi(T): |T|=n, nu(T)=k}.

A planted branch b (joined to one external parent) is summarized by
    Z_b = weighted matching sum of its internal edges (degrees counted with the parent edge),
    W_b = U_b / deg(b)  (U_b: sum over matchings leaving the root unmatched),
so that the message is y_b = W_b / Z_b.  If the root of b has children c_1..c_m (deg = m+1):
    Z_b = P + Q/(m+1),   W_b = P/(m+1),
    P = prod Z_c,  Q = sum_c W_c prod_{c' != c} Z_{c'}.
At a root with k children:  pi = P + Q/k.
Everything is multilinear with nonnegative coefficients in the children's (Z,W), so in every
class it suffices to keep the vertices of the upper-right convex hull (points maximizing some
nonnegative linear functional).  Classes are (size, nu, s) where s = 1 iff the root is exposed
by some maximum matching of the branch ("free"):  s_b = 1 iff no child is free,
nu_b = sum nu_c + [some child free].

Arithmetic: floats for pruning (with a small tolerance so near-ties are kept), then every
reported maximizer is recomputed exactly with Fractions from its tree.
"""
import sys, os
os.environ.setdefault("OMP_NUM_THREADS", "1")
from fractions import Fraction as Fr

EPS = 1e-11
EXACT = False
KEEP_TIES = True
ONE = 1.0


def hull(points):
    """points: list of (P, Q, tree).  Keep the vertices of the upper-right convex hull,
    i.e. every point that maximizes some linear functional aP + bQ with a, b > 0.

    Every functional applied downstream has strictly positive coefficients, so a point is
    needed iff it lies ON the upper-right hull.  With KEEP_TIES (default) points lying on a
    hull edge (collinear) and exact duplicates with different trees are kept too, so no
    maximizer is ever lost, including tied ones.  In float mode the tests use a relative
    tolerance in the keeping direction (points within EPS of the hull are kept)."""
    if len(points) <= 1:
        return points
    # dedupe identical (value, tree)
    seen = {}
    for p in points:
        seen.setdefault((p[0], p[1], p[2]), p)
    pts = sorted(seen.values(), key=lambda t: (-t[0], -t[1]))
    # Pareto: drop points weakly dominated by an earlier point with a different value
    par = []
    bestq = None
    for p in pts:
        if bestq is None:
            par.append(p); bestq = p[1]; continue
        if EXACT:
            keep = p[1] > bestq or (KEEP_TIES and p[1] == par[-1][1] and p[0] == par[-1][0])
        else:
            tol = EPS * max(1.0, abs(bestq), abs(p[0]))
            keep = p[1] > bestq - (tol if KEEP_TIES else -tol)
        if keep:
            par.append(p); bestq = max(bestq, p[1])
    # par: P non-increasing, Q non-decreasing.  Upper-right concave chain.
    out = []
    for p in par:
        while len(out) >= 2:
            a, b = out[-2], out[-1]
            # cross > 0  <=>  b strictly above the chord a-p  (b is a hull vertex)
            cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
            if EXACT:
                rem = cross < 0 if KEEP_TIES else cross <= 0
            else:
                scale = max(1.0, abs(a[0]), abs(p[0])) * max(1.0, abs(a[1]), abs(p[1]))
                rem = cross < -EPS * scale if KEEP_TIES else cross <= EPS * scale
            if rem:
                out.pop()
            else:
                break
        out.append(p)
    return out


def run(N, verbose=False):
    # classes[m] = dict (nu, s) -> list of (Z, W, tree)
    classes = {1: {(0, 1): [(ONE, ONE, ())]}}
    # bundles[size] = dict (c, nu, flag) -> list of (P, Q, childlist)
    bundles = {0: {(0, 0, 0): [(ONE, 0 * ONE, ())]}}
    results = {}
    for s in range(1, N):
        # bundles of size s, children sizes j = 1..s (classes of size <= s known)
        acc = {}
        for j in range(1, s + 1):
            for (cnu, cs), items in classes[j].items():
                for key, blist in bundles[s - j].items():
                    c, nu, f = key
                    nk = (c + 1, nu + cnu, f | cs)
                    L = acc.setdefault(nk, [])
                    for (P, Q, ch) in blist:
                        for (Z, W, t) in items:
                            L.append((P * Z, Q * Z + P * W, ch + (t,)))
        bundles[s] = {k: [(P, Q, tuple(sorted(ch))) for (P, Q, ch) in hull(v)] for k, v in acc.items()}
        # classes of size s+1 (planted)
        cl = {}
        for (c, nu, f), blist in bundles[s].items():
            d = c + 1
            key = (nu + f, 1 - f)
            L = cl.setdefault(key, [])
            for (P, Q, ch) in blist:
                L.append((P + Q / d, P / d, ch))
        classes[s + 1] = {k: hull(v) for k, v in cl.items()}
        # unrooted results for n = s+1
        n = s + 1
        best = {}
        for (c, nu, f), blist in bundles[s].items():
            k = nu + f
            for (P, Q, ch) in blist:
                val = P + Q / c
                tol = 0 if EXACT else 1e-12
                if k not in best or val > best[k][0] + tol:
                    best[k] = (val, [ch])
                elif abs(val - best[k][0]) <= tol * val:
                    best[k][1].append(ch)
        results[n] = best
        if verbose:
            tot = sum(len(v) for v in bundles[s].values())
            print(f"# size {s}: bundle states {len(bundles[s])}, points {tot}", file=sys.stderr, flush=True)
    return results


# ---------- exact tools on the nested-tuple representation (root = the tuple itself) ----------

def canon(adj):
    """canonical string of an unrooted tree (AHU encoding rooted at the centre(s))"""
    n = len(adj)
    if n <= 2:
        return f"K{n}"
    deg = {v: len(adj[v]) for v in adj}
    layer = [v for v in adj if deg[v] == 1]
    removed = len(layer)
    while removed < n:
        nxt = []
        for v in layer:
            for u in adj[v]:
                deg[u] -= 1
                if deg[u] == 1:
                    nxt.append(u)
        removed += len(nxt)
        if removed >= n:
            layer = nxt
            break
        layer = nxt
    centres = layer

    def enc(v, p):
        return "(" + "".join(sorted(enc(u, v) for u in adj[v] if u != p)) + ")"
    return min(enc(c, None) for c in centres)


def to_adj(tree):
    adj = {0: []}
    stack = [(tree, 0)]
    nxt = 1
    while stack:
        t, v = stack.pop()
        for ch in t:
            u = nxt; nxt += 1
            adj[u] = [v]; adj[v].append(u)
            stack.append((ch, u))
    return adj


def pi_exact(adj):
    r = 0; par = {r: None}; order = [r]
    for u in order:
        for v in adj[u]:
            if v not in par:
                par[v] = u; order.append(v)
    T = {}; Y = {}
    for u in reversed(order):
        d = len(adj[u]); prod = Fr(1); R = Fr(0)
        for v in adj[u]:
            if v != par[u]:
                prod *= T[v]; R += Y[v]
        if u == r:
            return prod * (1 + R / d) if d > 0 else Fr(1)
        T[u] = prod * (d + R) / d; Y[u] = 1 / (d + R)


def nu_tree(adj):
    # greedy leaf matching
    r = 0; par = {r: None}; order = [r]
    for u in order:
        for v in adj[u]:
            if v not in par:
                par[v] = u; order.append(v)
    matched = set(); k = 0
    for u in reversed(order):
        p = par[u]
        if p is not None and u not in matched and p not in matched:
            matched.add(u); matched.add(p); k += 1
    return k


def describe(adj):
    """Structural notation. Hubs = vertices of degree >= 3. For each hub list its pendant
    decorations: leaves (L), cherries (C = pendant P2), longer pendant paths, and the way
    hubs are linked (direct edge '-' or through a path of degree-2 vertices '-(j)-' with j
    internal vertices)."""
    n = len(adj)
    deg = {v: len(adj[v]) for v in adj}
    hubs = sorted([v for v in adj if deg[v] >= 3], key=lambda v: -deg[v])
    if not hubs:
        return f"path P{n}"
    hubset = set(hubs)
    name = {h: f"h{i+1}" for i, h in enumerate(hubs)}
    parts = []
    links = []
    seen_links = set()
    for h in hubs:
        leaves = 0; pend = {}
        for u in adj[h]:
            # walk along degree-2 chain
            prev, cur, length = h, u, 1
            while deg[cur] == 2:
                nx = [w for w in adj[cur] if w != prev][0]
                prev, cur = cur, nx; length += 1
            if deg[cur] == 1:
                if length == 1:
                    leaves += 1
                else:
                    pend[length] = pend.get(length, 0) + 1
            else:
                key = tuple(sorted((h, cur))) + (length,)
                if key not in seen_links:
                    seen_links.add(key)
                    links.append(f"{name[h]}{'-' if length == 1 else '-(' + str(length - 1) + ')-'}{name[cur]}")
        desc = [f"{name[h]}[deg {deg[h]}:"]
        items = []
        if leaves: items.append(f"{leaves}L")
        for L in sorted(pend):
            if L == 2: items.append(f"{pend[L]}C")
            else: items.append(f"{pend[L]}P{L}")
        desc.append(" ".join(items) if items else "-")
        parts.append("".join(desc[:1]) + desc[1] + "]")
    return " ".join(parts) + ("  links: " + ", ".join(links) if links else "")


if __name__ == "__main__":
    N = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == "exact":
        EXACT = True; ONE = Fr(1)
    res = run(N, verbose=True)
    for n in range(2, N + 1):
        print(f"n={n}")
        for k in sorted(res[n]):
            val, trees = res[n][k]
            exact = {}
            for t in trees:
                adj = to_adj(t)
                c = canon(adj)
                if c not in exact:
                    exact[c] = (pi_exact(adj), nu_tree(adj), describe(adj))
            m = max(e[0] for e in exact.values())
            win = {c: e for c, e in exact.items() if e[0] == m}
            assert all(e[1] == k for e in win.values()), (n, k)
            print(f"  nu={k}: max={m} ({float(m):.6f}) count={len(win)}  " + " || ".join(e[2] for e in win.values()))
        sys.stdout.flush()
