#!/usr/bin/env python3
"""
Certified exhaustive search for the Brualdi-Goldwasser maximizer on small trees, with RIGOROUS
interval arithmetic (no floating-point error analysis is needed).

Objective: pi(T) = per(L(T)) / prod deg = sum over matchings of prod 1/(deg u deg v)  (`Aobj`).

What it proves (for the requested range, see `main`):
  for every n, the exact maximum of pi over all trees on n vertices (or over all trees whose maximum
  degree is <= KC) is computed exactly, and every tree attaining it is identified and tested for being a
  SPIDER (a vertex all of whose branches are leaves, cherries or arms; an arm is a vertex adjacent to the
  centre whose other neighbours are all cherries).

Method.  Rooted trees are built bottom-up from planted branches ("items").  A planted branch b has
  T_b = prod T_c * (d + R)/d,   y_b = 1/(d + R),   R = sum_c y_c,   d = #children + 1,
and a tree rooted at a vertex with k children has pi = prod T_c * (k + R)/k.
A partial root state (k children so far, child sizes summing to s) is summarised by
lp = log prod T_c and R = sum y_c.
Exact dominance facts (proved in the doc proof/docs/BG_CERTIFIED_SEARCH_2026-09-25.md):
  (I)  items: in any tree, pi = T_b * (A + y_b * B) with A > 0, B >= 0 independent of b (b a pendant
       subtree of fixed size).  So an item with T' > T and y' >= y strictly beats it in EVERY tree.
  (S)  states at the same key (k, s): every completion evaluates to e^lp * ((c + R) A + B)/d with
       c >= D := max(k, 1), A > 0, B >= 0.  So if lp' > lp and lp' + log(D + R') > lp + log(D + R),
       the state (lp', R') is strictly better in every completion.
Both tests are applied to guaranteed enclosures [lo, hi] (outward rounding after every float operation,
libm log widened by 4 ulps), so a discarded object is PROVABLY strictly beaten, and the exact maximizers
all survive.  Duplicate generation is avoided by adding items in non-decreasing id order; when a state is
discarded its dominator inherits its "allowed next id" (a sound relaxation that keeps the search
exhaustive; see the doc).  Every surviving root state whose upper bound reaches the best lower bound is
rebuilt and evaluated EXACTLY in fractions.Fraction.

Usage:  python3 bg_certified_interval.py N [KC]      (KC = maximum vertex degree; default: no cap)
"""
import json
import sys
import time
from fractions import Fraction as Fr

import numpy as np

INF = np.inf


def dn(x):
    return np.nextafter(x, -INF)


def up(x):
    return np.nextafter(x, INF)


def log_dn(x):
    return dn(dn(dn(dn(np.log(x)))))


def log_up(x):
    return up(up(up(up(np.log(x)))))


class Store:
    FIELDS = (("lplo", float), ("lphi", float), ("Rlo", float), ("Rhi", float),
              ("prev", np.int64), ("item", np.int64), ("allow", np.int64))

    def __init__(self):
        self.cap = 1 << 20
        self.n = 0
        self.a = {f: np.empty(self.cap, dtype=t) for f, t in self.FIELDS}

    def add(self, **kw):
        m = len(kw["lplo"])
        while self.n + m > self.cap:
            self.cap *= 2
            for f, t in self.FIELDS:
                new = np.empty(self.cap, dtype=t)
                new[:self.n] = self.a[f][:self.n]
                self.a[f] = new
        idx = np.arange(self.n, self.n + m)
        for f, _ in self.FIELDS:
            self.a[f][idx] = kw[f]
        self.n += m
        return idx


def prune_states(lplo, lphi, vlo, vhi):
    """Indices to keep, and for each dropped index its (surviving) dominator.
    j dominates i  iff  lplo[j] > lphi[i] and vlo[j] > vhi[i]."""
    n = len(lplo)
    order = np.argsort(-lplo, kind="stable")          # lplo descending
    lsorted = lplo[order]
    v_sorted = vlo[order]
    pm = np.maximum.accumulate(v_sorted)
    # argmax index of the running max
    am = np.zeros(n, dtype=np.int64)
    best = -INF
    bi = -1
    for t in range(n):
        if v_sorted[t] > best:
            best, bi = v_sorted[t], t
        am[t] = bi
    # number of points with lplo > lphi[i]: lsorted is descending, so count = searchsorted on negated
    cnt = np.searchsorted(-lsorted, -lphi, side="left")
    drop = np.zeros(n, dtype=bool)
    dom = np.full(n, -1, dtype=np.int64)
    has = cnt > 0
    idx = np.nonzero(has)[0]
    c = cnt[idx] - 1
    d = pm[c] > vhi[idx]
    drop[idx[d]] = True
    dom[idx[d]] = order[am[c[d]]]
    return np.nonzero(~drop)[0], drop, dom


def prune_items(ltlo, lthi, ylo, yhi):
    """Keep mask for items.  j dominates i iff ltlo[j] > lthi[i] and ylo[j] >= yhi[i]."""
    n = len(ltlo)
    order = np.argsort(-ltlo, kind="stable")
    lsorted = ltlo[order]
    pm = np.maximum.accumulate(ylo[order])
    cnt = np.searchsorted(-lsorted, -lthi, side="left")
    keep = np.ones(n, dtype=bool)
    idx = np.nonzero(cnt > 0)[0]
    keep[idx[pm[cnt[idx] - 1] >= yhi[idx]]] = False
    return np.nonzero(keep)[0]


def search(N, KC=None, log=print):
    KC = KC or N
    st = Store()
    root = st.add(lplo=np.array([0.0]), lphi=np.array([0.0]), Rlo=np.array([0.0]), Rhi=np.array([0.0]),
                  prev=np.array([-1]), item=np.array([-1]), allow=np.array([-1]))
    states = {(0, 0): root}
    item_src = []      # item id -> state index it was built from
    t0 = time.time()
    for m in range(1, N):
        # ---- items of size m (planted branches): from states (k, m-1), root has k <= KC-1 children
        parts = []
        for k in range(0, KC):
            e = states.get((k, m - 1))
            if e is None:
                continue
            d = float(k + 1)
            a = st.a
            s_lo = dn(d + a["Rlo"][e])
            s_hi = up(d + a["Rhi"][e])
            ltlo = dn(a["lplo"][e] + log_dn(dn(s_lo / d)))
            lthi = up(a["lphi"][e] + log_up(up(s_hi / d)))
            ylo = dn(1.0 / s_hi)
            yhi = up(1.0 / s_lo)
            parts.append((ltlo, lthi, ylo, yhi, e))
        ltlo = np.concatenate([p[0] for p in parts])
        lthi = np.concatenate([p[1] for p in parts])
        ylo = np.concatenate([p[2] for p in parts])
        yhi = np.concatenate([p[3] for p in parts])
        esrc = np.concatenate([p[4] for p in parts])
        keep = prune_items(ltlo, lthi, ylo, yhi)
        first_id = len(item_src)
        ids = np.arange(first_id, first_id + len(keep), dtype=np.int64)
        item_src.extend(int(x) for x in esrc[keep])
        Iltlo, Ilthi, Iylo, Iyhi = ltlo[keep], lthi[keep], ylo[keep], yhi[keep]
        # ---- add items of size m to states (any number of them), in non-decreasing id order
        for s in range(0, N - m):
            for k in range(0, KC):
                src = states.get((k, s))
                if src is None:
                    continue
                a = st.a
                allow = a["allow"][src]
                mask = ids[None, :] >= allow[:, None]
                si, ii = np.nonzero(mask)
                if len(si) == 0:
                    continue
                sidx = src[si]
                lplo = dn(a["lplo"][sidx] + Iltlo[ii])
                lphi = up(a["lphi"][sidx] + Ilthi[ii])
                Rlo = dn(a["Rlo"][sidx] + Iylo[ii])
                Rhi = up(a["Rhi"][sidx] + Iyhi[ii])
                key = (k + 1, s + m)
                old = states.get(key)
                if old is not None:
                    alplo = np.concatenate((a["lplo"][old], lplo))
                    alphi = np.concatenate((a["lphi"][old], lphi))
                    aRlo = np.concatenate((a["Rlo"][old], Rlo))
                    aRhi = np.concatenate((a["Rhi"][old], Rhi))
                    aallow = np.concatenate((a["allow"][old], ids[ii]))
                    no = len(old)
                else:
                    alplo, alphi, aRlo, aRhi, aallow, no = lplo, lphi, Rlo, Rhi, ids[ii].copy(), 0
                D = float(max(k + 1, 1))
                vlo = dn(alplo + log_dn(dn(D + aRlo)))
                vhi = up(alphi + log_up(up(D + aRhi)))
                kp, drop, dom = prune_states(alplo, alphi, vlo, vhi)
                # permission transfer: the dominator may take any id the dropped state could
                dropped = np.nonzero(drop)[0]
                if len(dropped):
                    np.minimum.at(aallow, dom[dropped], aallow[dropped])
                kold = kp[kp < no]
                knew = kp[kp >= no]
                if old is not None and len(kold):
                    a["allow"][old[kold]] = aallow[kold]
                keep_old = old[kold] if old is not None else np.empty(0, dtype=np.int64)
                if len(knew):
                    j = knew - no
                    newidx = st.add(lplo=lplo[j], lphi=lphi[j], Rlo=Rlo[j], Rhi=Rhi[j],
                                    prev=sidx[j], item=ids[ii][j], allow=aallow[knew])
                else:
                    newidx = np.empty(0, dtype=np.int64)
                states[key] = np.concatenate((keep_old, newidx))
        if m % 25 == 0:
            log(f"  [search N={N} KC={KC}] m={m} states={st.n} items={len(item_src)} t={time.time() - t0:.0f}s")
    return st, states, item_src


def rebuild(st, item_src):
    memo = {}

    def kids(e):
        out = []
        while st.a["prev"][e] >= 0:
            out.append(int(st.a["item"][e]))
            e = int(st.a["prev"][e])
        return out

    def item_exact(i):
        if i in memo:
            return memo[i]
        ch = [item_exact(c) for c in kids(item_src[i])]
        d = len(ch) + 1
        P, R = Fr(1), Fr(0)
        for T, y, _ in ch:
            P *= T
            R += y
        shape = ("node", tuple(sorted((c[2] for c in ch), key=repr)))
        memo[i] = (P * (d + R) / d, 1 / (d + R), shape)
        return memo[i]
    return kids, item_exact


def shape_edges(children_shapes):
    """Edge list of the tree whose root has the given child shapes."""
    edges = []
    cnt = [1]

    def build(shape, parent):
        v = cnt[0]
        cnt[0] += 1
        edges.append((parent, v))
        for c in shape[1]:
            build(c, v)
    for c in children_shapes:
        build(c, 0)
    return cnt[0], edges


def is_spider(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    def is_leaf(u, p):
        return len(adj[u]) == 1

    def is_cherry(u, p):   # u has exactly one other neighbour, which is a leaf
        o = [w for w in adj[u] if w != p]
        return len(o) == 1 and is_leaf(o[0], u)

    def is_atom(u, p):     # leaf, cherry, or arm (every other neighbour is a cherry)
        o = [w for w in adj[u] if w != p]
        return len(o) == 0 or is_cherry(u, p) or all(is_cherry(w, u) for w in o)
    return any(all(is_atom(u, c) for u in adj[c]) for c in range(n))


def certify(N, KC=None, log=print):
    t0 = time.time()
    st, states, item_src = search(N, KC, log)
    kids, item_exact = rebuild(st, item_src)
    a = st.a
    out = {}
    for n in range(2, N + 1):
        s = n - 1
        vals = []
        for k in range(1, min(KC or N, s) + 1):
            e = states.get((k, s))
            if e is None:
                continue
            kf = float(k)
            vlo = dn(a["lplo"][e] + log_dn(dn(dn(kf + a["Rlo"][e]) / kf)))
            vhi = up(a["lphi"][e] + log_up(up(up(kf + a["Rhi"][e]) / kf)))
            vals.append((vlo, vhi, e, k))
        best_lo = max(float(np.max(v[0])) for v in vals)
        cands = []
        for vlo, vhi, e, k in vals:
            for j in np.nonzero(vhi >= best_lo)[0]:
                ch = [item_exact(c) for c in kids(int(e[j]))]
                P, R = Fr(1), Fr(0)
                for T, y, _ in ch:
                    P *= T
                    R += y
                cands.append((P * (k + R) / k, [c[2] for c in ch]))
        mx = max(c[0] for c in cands)
        maxi = [c[1] for c in cands if c[0] == mx]
        spiders = []
        for sh in maxi:
            nn, edges = shape_edges(sh)
            assert nn == n
            spiders.append(is_spider(nn, edges))
        out[n] = {"max_exact": f"{mx.numerator}/{mx.denominator}", "n_candidates": len(cands),
                  "n_maximizer_rootings": len(maxi), "all_maximizers_spiders": all(spiders)}
    log(f"[certify N={N} KC={KC}] done in {time.time() - t0:.0f}s, states={st.n}")
    return out


if __name__ == "__main__":
    N = int(sys.argv[1])
    KC = int(sys.argv[2]) if len(sys.argv) > 2 else None
    res = certify(N, KC, log=lambda s: print(s, flush=True))
    tag = f"N{N}" + (f"_KC{KC}" if KC else "")
    with open(f"bg_certified_interval_{tag}.json", "w") as f:
        json.dump(res, f, indent=0)
    print(f"wrote bg_certified_interval_{tag}.json")
