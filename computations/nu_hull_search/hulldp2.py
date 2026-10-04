"""Fast exact hull-DP for M(n,k) (replaces hulldp.py / hulldp_k.py for the large runs).

Same mathematics as hulldp.py (see its docstring):  planted branch -> (Z, W) = (T, T*y);
children bundle (P, Q):  P = prod Z_c,  Q = sum_c W_c prod_{c' != c} Z_c';
planted root of degree d = c+1:  Z = P + Q/d,  W = P/d;  unrooted root with c children: pi = P + Q/c.
All maps are multilinear with nonnegative coefficients and every functional used downstream has
strictly positive coefficients, so each class needs exactly the points on its upper-right convex
hull (vertices AND points on hull edges, which we keep so that tied maximizers are never lost).

Implementation:
  * candidates are generated with numpy (float64), and a CONSERVATIVE float filter discards only
    points that are below the hull by a relative margin TOL = 1e-9 (float rounding in products of
    <= 300 factors is < 1e-13 relative, so a discarded point is truly strictly inside the hull and
    every hull vertex / hull-edge point survives);
  * survivors get exact Fraction values (from the exact values of their parents) and the final
    hull (with ties) is computed in exact arithmetic;
  * trees are interned: tree id -> sorted tuple of child tree ids (id 0 = single vertex).
Classes: (nu, s) with s = 1 iff the root is missed by some maximum matching.
KMAX (optional) discards classes with nu > KMAX (nu is monotone under taking subtrees).

Usage: python3 hulldp2.py NMAX [KMAX]
Output: for every n, k: exact max, number of non-isomorphic extremal trees, their descriptions.
"""
import os, sys
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

TOL = 1e-9

LAST_CLASSES = {}
TREES = [()]          # id -> tuple of child ids
TID = {(): 0}


def intern(ch):
    t = TID.get(ch)
    if t is None:
        t = len(TREES); TREES.append(ch); TID[ch] = t
    return t


def float_filter(P, Q):
    """indices of points that may lie on the upper-right hull (conservative)."""
    m = len(P)
    if m <= 2:
        return np.arange(m)
    order = np.lexsort((-Q, -P))           # P desc, then Q desc
    Ps, Qs = P[order], Q[order]
    runmax = np.maximum.accumulate(Qs)
    prev = np.concatenate(([-np.inf], runmax[:-1]))
    keep = Qs >= prev - TOL * np.maximum(1.0, np.abs(prev))
    idx = order[keep]
    Pk, Qk = P[idx], Q[idx]
    out = []
    for i in range(len(idx)):
        while len(out) >= 2:
            a, b = out[-2], out[-1]
            cross = (Pk[b] - Pk[a]) * (Qk[i] - Qk[a]) - (Qk[b] - Qk[a]) * (Pk[i] - Pk[a])
            scale = max(1.0, abs(Pk[a]), abs(Pk[i])) * max(1.0, abs(Qk[a]), abs(Qk[i]))
            if cross < -TOL * scale:
                out.pop()
            else:
                break
        out.append(i)
    return idx[out]


def exact_hull(pts):
    """pts: list of (Px, Qx, payload) exact; keep hull vertices, hull-edge points, duplicates."""
    if len(pts) <= 1:
        return pts
    pts = sorted(pts, key=lambda t: (-t[0], -t[1]))
    par = []
    for p in pts:
        if not par or p[1] > par[-1][1] or (p[0] == par[-1][0] and p[1] == par[-1][1]):
            par.append(p)
    out = []
    for p in par:
        while len(out) >= 2:
            a, b = out[-2], out[-1]
            cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
            if cross < 0:
                out.pop()
            else:
                break
        out.append(p)
    return out


class Group:
    """a hull: float arrays + exact values + payload (tree id or child tuple)."""
    __slots__ = ("F1", "F2", "X1", "X2", "pay")

    def __init__(self, pts):
        self.X1 = [p[0] for p in pts]; self.X2 = [p[1] for p in pts]; self.pay = [p[2] for p in pts]
        self.F1 = np.array([float(x) for x in self.X1]); self.F2 = np.array([float(x) for x in self.X2])


def run(NMAX, KMAX=None, log=sys.stderr):
    one = Fr(1)
    classes = {1: {(0, 1): Group([(one, one, 0)])}}
    bundles = {0: {(0, 0, 0): Group([(one, Fr(0), ())])}}
    results = {}
    for s in range(1, NMAX):
        # gather candidates per target key
        cand = {}
        for j in range(1, s + 1):
            for (cnu, cs), cg in classes[j].items():
                for (c, nu, f), bg in bundles[s - j].items():
                    nk = (c + 1, nu + cnu, f | cs)
                    if KMAX is not None and nu + cnu > KMAX:
                        continue
                    Pn = np.multiply.outer(bg.F1, cg.F1).ravel()
                    Qn = (np.multiply.outer(bg.F2, cg.F1) + np.multiply.outer(bg.F1, cg.F2)).ravel()
                    L = cand.setdefault(nk, [])
                    L.append((Pn, Qn, bg, cg, len(cg.F1)))
        newb = {}
        for nk, lst in cand.items():
            P = np.concatenate([x[0] for x in lst]); Q = np.concatenate([x[1] for x in lst])
            sel = float_filter(P, Q)
            offs = np.cumsum([0] + [len(x[0]) for x in lst])
            pts = {}
            for g in sel:
                blk = int(np.searchsorted(offs, g, side='right') - 1)
                _, _, bg, cg, nc = lst[blk]
                r = int(g - offs[blk]); bi, ci = divmod(r, nc)
                ch = tuple(sorted(bg.pay[bi] + (cg.pay[ci],)))
                if ch in pts:
                    continue
                Px = bg.X1[bi] * cg.X1[ci]
                Qx = bg.X2[bi] * cg.X1[ci] + bg.X1[bi] * cg.X2[ci]
                pts[ch] = (Px, Qx, ch)
            newb[nk] = Group(exact_hull(list(pts.values())))
        bundles[s] = newb
        # planted classes of size s+1 and unrooted maxima on s+1 vertices
        cl = {}
        best = {}
        for (c, nu, f), bg in newb.items():
            d = c + 1
            key = (nu + f, 1 - f)
            L = cl.setdefault(key, [])
            k = nu + f
            for P, Q, ch in zip(bg.X1, bg.X2, bg.pay):
                L.append((P + Q / d, P / d, intern(ch)))
                val = P + Q / c
                if k not in best or val > best[k][0]:
                    best[k] = (val, [ch])
                elif val == best[k][0]:
                    best[k][1].append(ch)
        classes[s + 1] = {key: Group(exact_hull(v)) for key, v in cl.items()}
        results[s + 1] = best
        LAST_CLASSES.clear(); LAST_CLASSES.update(classes)
        if log:
            tot = sum(len(g.X1) for g in newb.values())
            print(f"# size {s}: bundle states {len(newb)}, points {tot}", file=log, flush=True)
    return results


def tree_of_children(ch):
    """nested-tuple tree (hulldp format) from a tuple of child ids"""
    def build(t):
        return tuple(build(c) for c in TREES[t])
    return tuple(build(c) for c in ch)


if __name__ == "__main__":
    from hulldp import to_adj, pi_exact, nu_tree, describe, canon
    NMAX = int(sys.argv[1]); KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else None
    res = run(NMAX, KMAX)
    for n in range(2, NMAX + 1):
        for k in sorted(res[n]):
            val, chs = res[n][k]
            win = {}
            for ch in chs:
                adj = to_adj(tree_of_children(ch))
                c = canon(adj)
                if c in win:
                    continue
                assert pi_exact(adj) == val and nu_tree(adj) == k, (n, k)
                win[c] = describe(adj)
            print(f"n={n} k={k} max={val} ({float(val):.9f}) count={len(win)} " + " || ".join(win.values()))
        sys.stdout.flush()
