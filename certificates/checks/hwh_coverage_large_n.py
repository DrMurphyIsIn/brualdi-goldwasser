"""
hwh / HnormMulti evidence at larger n: exhaustive coverage (viability) n = 16..N, exhaustive per-size
Aobj maximizer via an exact Pareto-frontier DP, best-backbone per size, and a large-n adversarial search.

Definitions (identical to phase0_straightprogress_sized.py / hwh_viability.py, which mirror Lean
R47R7Straighten.strDefect and the matching-sum Aobj):
  Aobj(T)   = per(L(T)) / prod deg = sum over matchings M of prod_{uv in M} 1/(deg u * deg v).
  rooted recognizers (children = neighbours other than the parent):
    isCherry(v) = exactly one child and it is a leaf;  isArm(v) = every child is a cherry (a leaf is an arm);
    isPiece(v)  = isArm(v) or isCherry(v);
    strDefect(v) = max(0, #nonpiece children - 1) + sum strDefect(c) over nonpiece children c.
  backbone   := min over roots of strDefect == 0  (the repo's "hub-backbone" / backboneU s shape:
                a spine path whose vertices carry leaves, cherries and arms = stars of cherries).
  coverage (viability) at T with d = minDefect(T) > 0: some SPR-distance-1 tree T' on the same vertex
                set has minDefect(T') < d AND Aobj(T') >= Aobj(T).   (free reroot = min over roots)

Cavity form used everywhere (derived from the matching sum; checked against pi_literal below):
  for a vertex v with parent edge and children c: d_v = #children + 1,
      R_v = sum_c r_c,   S_v = prod_c S_c * (d_v + R_v)/d_v,   r_v = 1/(d_v + R_v)    (leaf: S=1, r=1)
  and at a root with k children: Aobj = prod_c S_c * (k + R)/k.
  For any fixed context, Aobj(T) = S_v * (Z(rest) + r_v * Z(rest - p)/d_p), i.e. Aobj is strictly INCREASING in
  both S_v and r_v of any pendant subtree.  Hence replacing a pendant subtree by one of the same size that
  is Pareto-better in (S, r) never lowers Aobj -- the basis of the exhaustive frontier DP (`frontier`).

The coverage test and the search use floats only as a prefilter (margin REL_TOL); every coverage witness
and every reported failure is re-decided in exact fractions.Fraction.  The frontier DP is exact throughout.

Subcommands (run from proof/verification/):
  python3 hwh_coverage_large_n.py sanity                  engines vs pi_literal / min_defect_over_roots, n<=10
  python3 hwh_coverage_large_n.py coverage 16 23 16       exhaustive single-SPR coverage (16 workers)
  python3 hwh_coverage_large_n.py frontier 64 18          exact per-size max (all trees, backbones), brute check n<=18
  python3 hwh_coverage_large_n.py frontier 100            same, to n=100
  python3 hwh_coverage_large_n.py pant 64                 Pant families: backbone?, Aobj vs exact max of that size
  python3 hwh_coverage_large_n.py search 20 64 12 F.json  annealing + coverage on near-top non-backbones + random
  HWH_NEAR_FRAC=0.6 python3 hwh_coverage_large_n.py search-small 24 29 F.json 30000
  python3 hwh_coverage_large_n.py probe 23 40 32000 F.json random trees / perturbed backbones, coverage
  python3 hwh_coverage_large_n.py witness                 exact + independent-engine check of the failure witnesses

RESULT (2026-09-24, wall clock ~45 min on a shared 32-core machine):
  * HnormMulti holds for EVERY n <= 100 (exhaustive, exact): the frontier DP gives max Aobj over all
    n-vertex trees == max Aobj over backbones, and every maximizer is a backbone.  The maximizer is unique
    up to isomorphism except n=21 (two: the subdivided star = spider with 10 legs of length 2, and T(3,3,3)).
    For n >= 32 it is a single centre carrying cherries and arms (stars of cherries) -- no longer spine
    (only n=31 has a 2-vertex spine: T(5,5,4)).  Examples: n=36 centre+4 cherries+arms(4,4,4);
    n=52 centre+7 cherries+arms(6,6,5), Aobj = 370829981399553/8220835840 ~ 45108.55 (> T(6,6,6,6) ~ 44887.39);
    n=64 centre+6 cherries+arms(5,5,5,4,4).  DP cross-checked against brute force over all trees and over
    all backbones for every n <= 18.
  * Pant's families T(3,t,3), T(t,t,t,t), T(t,t,t+1,t) are all backbones (minDefect 0); T(3,3,3) (n=21)
    and T(3,4,3) (n=23) are per-size maximizers, the others are strictly below the exact maximum.
  * Single-SPR coverage (the hwh_viability.py test): exhaustive n <= 23 -> 0 failures
    (n=16..23: 4237, 13436, 41402, 124881, 370205, 1082692, 3132218, 8982602 defective trees).
    It FAILS at larger n: exact, independently confirmed witnesses at n = 25 (WITNESS_25), 29, 34, and
    many more up to n = 64 (all minDefect 1, all at 75-87% of the best backbone of their size).  n = 24 not exhaustive.
    These refute only the LOCAL single-SPR move route, not HnormMulti.
conjecture1_proved = False.
"""
from __future__ import annotations

import math
import os
import random
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

REL_TOL = 1e-9          # float values within this relative margin are re-decided exactly
NEAR_CAP = 1500         # max near-top non-backbones per n sent to the coverage test
# "near the top" for the search: Aobj >= NEAR_FRAC * best backbone of that size
NEAR_FRAC = float(os.environ.get("HWH_NEAR_FRAC", "0.75"))


# ============================================================================ tree plumbing
def adj_from_edges(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def adj_from_layout(layout):
    """WROM level sequence (networkx nonisomorphic_trees internal layout) -> adjacency list."""
    n = len(layout)
    adj = [[] for _ in range(n)]
    last = {}
    for i, lev in enumerate(layout):
        if lev > 0:
            p = last[lev - 1]
            adj[i].append(p)
            adj[p].append(i)
        last[lev] = i
    return adj


def layouts(n):
    """All non-isomorphic free trees on n vertices as level sequences (same enumeration as
    networkx.nonisomorphic_trees, without building Graph objects)."""
    from networkx.generators.nonisomorphic_trees import _next_rooted_tree, _next_tree
    layout = list(range(n // 2 + 1)) + list(range(1, (n + 1) // 2))
    while layout is not None:
        layout = _next_tree(layout)
        if layout is not None:
            yield tuple(layout)
            layout = _next_rooted_tree(layout)


def _postorder(adj, root):
    parent = [-1] * len(adj)
    order = [root]
    parent[root] = root
    i = 0
    while i < len(order):
        v = order[i]
        i += 1
        for w in adj[v]:
            if parent[w] == -1:
                parent[w] = v
                order.append(w)
    parent[root] = -1
    return order, parent


# ============================================================================ Aobj
def aobj_float(adj, root=0):
    order, parent = _postorder(adj, root)
    S = [1.0] * len(adj)
    r = [1.0] * len(adj)
    for v in reversed(order):
        prodS = 1.0
        R = 0.0
        k = 0
        for c in adj[v]:
            if c != parent[v]:
                prodS *= S[c]
                R += r[c]
                k += 1
        d = len(adj[v])
        if v == root:
            return prodS * (k + R) / k if k else 1.0
        S[v] = prodS * (d + R) / d
        r[v] = 1.0 / (d + R)


def aobj_exact(adj, root=0):
    order, parent = _postorder(adj, root)
    S = [Fr(1)] * len(adj)
    r = [Fr(1)] * len(adj)
    for v in reversed(order):
        prodS = Fr(1)
        R = Fr(0)
        k = 0
        for c in adj[v]:
            if c != parent[v]:
                prodS *= S[c]
                R += r[c]
                k += 1
        d = len(adj[v])
        if v == root:
            return prodS * (k + R) / k if k else Fr(1)
        S[v] = prodS * (d + R) / d
        r[v] = 1 / (d + R)


# ============================================================================ strDefect
def min_defect(adj):
    """min over roots of strDefect, with memo over directed edges (v, parent)."""
    deg = [len(a) for a in adj]
    n = len(adj)

    def is_cherry(v, p):   # exactly one child and it is a leaf
        if p < 0:
            return deg[v] == 1 and deg[adj[v][0]] == 1
        if deg[v] != 2:
            return False
        c = adj[v][0] if adj[v][1] == p else adj[v][1]
        return deg[c] == 1

    def is_arm(v, p):      # every child is a cherry
        for c in adj[v]:
            if c != p and not (deg[c] == 2 and deg[adj[c][0] if adj[c][1] == v else adj[c][1]] == 1):
                return False
        return True

    memo = {}

    def sd(v, p):
        key = v * n + p if p >= 0 else -1 - v
        x = memo.get(key)
        if x is not None:
            return x
        cnt = 0
        tot = 0
        for c in adj[v]:
            if c != p and not (is_arm(c, v) or is_cherry(c, v)):
                cnt += 1
                tot += sd(c, v)
        x = tot + (cnt - 1 if cnt > 1 else 0)
        memo[key] = x
        return x

    best = None
    for r0 in range(n):
        x = sd(r0, -1)
        if best is None or x < best:
            best = x
            if best == 0:
                return 0
    return best


# ============================================================================ SPR moves
def spr_moves(adj):
    """Yield (u, v, a, b): remove edge uv, add edge ab (a on u's side, b on v's side), (a,b) != (u,v).
    Labeled duplicates are not removed (harmless for existence checks)."""
    n = len(adj)
    for u in range(n):
        for v in adj[u]:
            if u > v:
                continue
            # component of u after removing uv
            side = [False] * n
            side[u] = True
            st = [u]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if not side[y] and not (x == u and y == v):
                        side[y] = True
                        st.append(y)
            A = [x for x in range(n) if side[x]]
            B = [x for x in range(n) if not side[x]]
            for a in A:
                for b in B:
                    if a == u and b == v:
                        continue
                    yield u, v, a, b


def apply_move(adj, mv):
    u, v, a, b = mv
    new = [list(x) for x in adj]
    new[u].remove(v)
    new[v].remove(u)
    new[a].append(b)
    new[b].append(a)
    return new


# ============================================================================ coverage (viability)
def coverage_one(adj):
    """Return (status, d, info).  status: 'backbone' | 'covered' | 'FAIL'.
    'covered' is certified exactly (Aobj(T') >= Aobj(T) in Fraction, minDefect recomputed).
    'FAIL' means: every SPR neighbour with lower minDefect has exact Aobj < Aobj(T) (floats below
    the margin are decisive; anything within REL_TOL is decided exactly)."""
    d = min_defect(adj)
    if d == 0:
        return "backbone", 0, None
    a = aobj_float(adj)
    thr = a * (1 - REL_TOL)
    aex = None
    best_below = None
    for mv in spr_moves(adj):
        t = apply_move(adj, mv)
        at = aobj_float(t)
        if at < thr:
            continue
        if min_defect(t) >= d:
            continue
        if aex is None:
            aex = aobj_exact(adj)
        atx = aobj_exact(t)
        if atx >= aex:
            return "covered", d, (mv, min_defect(t), atx - aex)
        best_below = atx
    return "FAIL", d, {"edges": edges_of(adj), "aobj": aobj_exact(adj), "near": best_below}


def _cov_chunk(lays):
    out = {"backbone": 0, "covered": 0, "FAIL": 0, "fails": [], "strict": 0, "tie": 0}
    for lay in lays:
        st, d, info = coverage_one(adj_from_layout(lay))
        out[st] += 1
        if st == "FAIL":
            out["fails"].append(info)
        elif st == "covered":
            if info[2] > 0:
                out["strict"] += 1
            else:
                out["tie"] += 1
    return out


def _chunks(it, size):
    buf = []
    for x in it:
        buf.append(x)
        if len(buf) == size:
            yield buf
            buf = []
    if buf:
        yield buf


def run_coverage(nmin, nmax, workers=12):
    results = {}
    with Pool(workers) as pool:
        for n in range(nmin, nmax + 1):
            t0 = time.time()
            agg = {"backbone": 0, "covered": 0, "FAIL": 0, "fails": [], "strict": 0, "tie": 0}
            for out in pool.imap_unordered(_cov_chunk, _chunks(layouts(n), 500)):
                for k in ("backbone", "covered", "FAIL", "strict", "tie"):
                    agg[k] += out[k]
                agg["fails"] += out["fails"]
            tot = agg["backbone"] + agg["covered"] + agg["FAIL"]
            print(f"[coverage n={n}] trees={tot} backbones={agg['backbone']} defective="
                  f"{agg['covered'] + agg['FAIL']} covered={agg['covered']} (strict={agg['strict']} "
                  f"tie={agg['tie']}) FAIL={agg['FAIL']}  {time.time() - t0:.0f}s", flush=True)
            for f in agg["fails"][:5]:
                print("   FAIL", f, flush=True)
            results[n] = agg
    return results


# ============================================================================ exhaustive frontier DP
# A pendant subtree (vertex v with a parent edge p) acts on Aobj only through (S_v, r_v):
#     Aobj(T) = S_v * Z(rest) + (1/(d_p d_v)) Z0_v * Z(rest - p) = S_v * (Z(rest) + r_v Z(rest - p)/d_p),
# where Z(rest), Z(rest - p) > 0 do not depend on the subtree.  So Aobj is STRICTLY increasing in both S_v
# and r_v, and a pendant subtree that is strictly Pareto-dominated in (S, r) by another of the same size is
# never part of a maximizer.  F[m] = the (non-strict) Pareto frontier over pendant subtrees of size m.
#
# A vertex with child multiset C is built by an unbounded knapsack over frontier items; partial states
# (k children, total size s[, backbone flag]) hold points (P = prod S_c, R = sum r_c).  Points in the same
# state receive identical continuations (j more children with product Q and r-sum x).  The final factor
# is P Q (d + R + x)/d with d >= k (d = k + j at a root, k + j + 1 elsewhere) and r = 1/(d + R + x).  If
#     R2 <= R1  and  P2 (k + R2) > P1 (k + R1)
# then (K + R2)/(K + R1) is nondecreasing in K >= k, so point 2 gives a strictly larger S and a larger or
# equal r in EVERY continuation: point 1 can be discarded without losing any maximizer (exact ties kept).
# Everything below is exact fractions.Fraction; no floating point enters the DP.


def _prune(points, k):
    """points: list of (P, R, rep).  Drop p1 iff some p2 has R2 <= R1 and P2 (D+R2) > P1 (D+R1), D=max(k,1)."""
    if len(points) <= 1:
        return points
    D = max(k, 1)
    dec = sorted(((p[1], p[0] * (D + p[1]), p) for p in points), key=lambda t: (t[0], -t[1]))
    kept = []
    best = None
    for R, y, p in dec:
        if best is not None and best > y:
            continue
        kept.append(p)
        if best is None or y > best:
            best = y
    return kept


def _prune_SR(entries):
    """entries: list of (S, r, rep).  Drop e1 iff some e2 >= e1 in both coordinates, strictly in one."""
    dec = sorted(entries, key=lambda e: (-e[1], -e[0]))
    kept = []
    best = None           # max S among strictly larger r
    cur_r, cur_best = None, None
    for e in dec:
        if e[1] != cur_r:
            if cur_best is not None and (best is None or cur_best > best):
                best = cur_best
            cur_r, cur_best = e[1], e[0]      # first of its r-group has the max S of the group
        if best is not None and best >= e[0]:
            continue                           # strictly larger r, S at least as large
        if e[0] < cur_best:
            continue                           # same r, strictly smaller S
        kept.append(e)
    return kept


class FrontierDP:
    """Exact exhaustive per-size maximizer of Aobj.
    mode 'all': every tree.  mode 'backbone': only trees admitting a root of strDefect 0.
    Items are pendant-subtree classes (size, S, r, children item ids, is_nonpiece).  In backbone mode an
    item is either a piece (leaf, cherry, arm_j -- always allowed as a child) or a strDefect-0 non-piece
    subtree (at most one per vertex, tracked by the flag in the state key) -- exactly the Lean condition
    strDefect(v) = 0  <=>  at most one non-piece child and it has strDefect 0."""

    def __init__(self, nmax, mode="all"):
        self.nmax = nmax
        self.mode = mode
        self.items = []
        self.states = {(0, 0, 0): [(Fr(1), Fr(0), ())]}
        self.frontier_sizes = {}
        self.best = {}             # n -> list of (Aobj, rep) over all root states
        self._run()

    def _add_item(self, size, S, r, ch, nonpiece):
        iid = len(self.items)
        self.items.append((size, S, r, ch, nonpiece))
        bb = self.mode == "backbone"
        for s in range(0, self.nmax - size):          # new total s+size <= nmax-1
            touched = []
            for k in range(0, s + 1):
                for fl in (0, 1):
                    src = self.states.get((k, s, fl))
                    if not src:
                        continue
                    if bb and nonpiece and fl == 1:
                        continue
                    key = (k + 1, s + size, 1 if (bb and nonpiece) else fl)
                    dst = self.states.setdefault(key, [])
                    for (P, R, rep) in src:
                        dst.append((P * S, R + r, rep + (iid,)))
                    touched.append(key)
            # prune states of total s+size before they are read as sources later in this pass
            for key in touched:
                self.states[key] = _prune(self.states[key], key[0])
        return iid

    def _is_piece_children(self, ch):
        """Is a (non-root) vertex with these child items a piece (cherry or arm)?"""
        if len(ch) == 1 and self.items[ch[0]][0] == 1:
            return True                                        # cherry: single leaf child
        return all(self.items[c][0] == 2 for c in ch)          # arm: all children cherries (incl. leaf)

    def _run(self):
        for m in range(1, self.nmax):
            cand = []
            for (k, s, fl), pts in self.states.items():
                if s != m - 1:
                    continue
                d = k + 1
                for (P, R, rep) in pts:
                    cand.append((P * (d + R) / d, 1 / (d + R), (rep, fl)))
            if self.mode == "all":
                front = _prune_SR(cand)
                self.frontier_sizes[m] = len(front)
                for (S, r, (rep, fl)) in front:
                    self._add_item(m, S, r, rep, False)
            else:
                pieces = [c for c in cand if c[2][1] == 0 and self._is_piece_children(c[2][0])]
                nonp = [c for c in cand if not (c[2][1] == 0 and self._is_piece_children(c[2][0]))]
                front = _prune_SR(nonp)
                self.frontier_sizes[m] = (len(pieces), len(front))
                for (S, r, (rep, fl)) in pieces:
                    self._add_item(m, S, r, rep, False)
                for (S, r, (rep, fl)) in front:
                    self._add_item(m, S, r, rep, True)
        for (k, s, fl), pts in self.states.items():
            if k == 0:
                continue
            for (P, R, rep) in pts:
                self.best.setdefault(s + 1, []).append((P * (k + R) / k, rep))

    def tree(self, rep):
        """Rebuild an adjacency list from a root rep (tuple of child item ids)."""
        edges = []
        cnt = [1]

        def build(iid, parent):
            v = cnt[0]
            cnt[0] += 1
            edges.append((parent, v))
            for c in self.items[iid][3]:
                build(c, v)

        for c in rep:
            build(c, 0)
        return adj_from_edges(cnt[0], edges)

    def top(self, n):
        """(max Aobj, list of pairwise non-isomorphic maximizers) at size n; every root state is a
        rooting of some tree, and all exact maximizers survive the (strict-dominance) pruning."""
        lst = self.best[n]
        mx = max(v for v, _ in lst)
        out = {}
        for v, rep in lst:
            if v == mx:
                adj = self.tree(rep)
                assert aobj_exact(adj) == mx          # independent recomputation from the rebuilt tree
                out.setdefault(canon(adj), adj)
        return mx, list(out.values())


def canon(adj):
    """Canonical string of an unrooted tree (AHU at the center/bicenter)."""
    n = len(adj)
    if n <= 2:
        return str(n)
    deg = [len(a) for a in adj]
    leaves = [v for v in range(n) if deg[v] == 1]
    rem = n
    while rem > 2:
        rem -= len(leaves)
        nl = []
        for v in leaves:
            for w in adj[v]:
                deg[w] -= 1
                if deg[w] == 1:
                    nl.append(w)
            deg[v] = 0
        leaves = nl

    def enc(v, p):
        return "(" + "".join(sorted(enc(w, v) for w in adj[v] if w != p)) + ")"
    return min(enc(c, -1) for c in leaves)


def rooted_defect(adj, root):
    """strDefect at a given root (plain recursion; used for reporting only)."""
    deg = [len(a) for a in adj]

    def cherry(v, p):
        ch = [c for c in adj[v] if c != p]
        return len(ch) == 1 and deg[ch[0]] == 1

    def piece(v, p):
        return cherry(v, p) or all(cherry(c, v) for c in adj[v] if c != p)

    def sd(v, p):
        np_ = [c for c in adj[v] if c != p and not piece(c, v)]
        return max(0, len(np_) - 1) + sum(sd(c, v) for c in np_)
    return sd(root, -1), piece


def describe(adj):
    """Backbone: spine from a strDefect-0 root, each spine vertex as {L: leaves, C: cherries, A: arm
    sizes (#cherries)}.  Non-backbone: hub degree multiset and min defect."""
    for r0 in range(len(adj)):
        d, piece = rooted_defect(adj, r0)
        if d == 0:
            break
    else:
        degs = sorted((len(a) for a in adj if len(a) >= 3), reverse=True)
        return f"NONBACKBONE(minDefect={min_defect(adj)}, hubdegs={degs})"
    deg = [len(a) for a in adj]
    parts = []
    v, p = r0, -1
    while v is not None:
        L = C = 0
        A = []
        nxt = None
        for c in adj[v]:
            if c == p:
                continue
            ch = [x for x in adj[c] if x != v]
            if not ch:
                L += 1
            elif len(ch) == 1 and deg[ch[0]] == 1:
                C += 1
            elif piece(c, v):
                A.append(len(ch))
            else:
                nxt = c
        parts.append(f"L{L}C{C}" + (f"A{sorted(A, reverse=True)}" if A else ""))
        v, p = nxt, v
    return "-".join(parts)


def run_frontier(nmax, compare_brute_upto=0):
    t0 = time.time()
    dpa = FrontierDP(nmax, "all")
    t1 = time.time()
    dpb = FrontierDP(nmax, "backbone")
    t2 = time.time()
    print(f"[frontier] all-trees DP to n={nmax}: {t1 - t0:.1f}s; backbone DP: {t2 - t1:.1f}s", flush=True)
    print(f"[frontier] pendant frontier sizes (all): {dpa.frontier_sizes}")
    print(f"[frontier] pendant frontier sizes (backbone: pieces, nonpiece): {dpb.frontier_sizes}")
    rows = {}
    for n in range(4, nmax + 1):
        ma, argsA = dpa.top(n)
        mb, argsB = dpb.top(n)
        allbb = all(min_defect(a) == 0 for a in argsA)
        rows[n] = (ma, mb, allbb, argsA)
        print(f"n={n:3d} maxAobj={float(ma):.12g} bestBackbone={float(mb):.12g} "
              f"equal_exact={ma == mb} #maximizers(non-iso)={len(argsA)} all_maximizers_backbones={allbb} "
              f"shapes={[describe(a) for a in argsA]}", flush=True)
    if compare_brute_upto:
        for n in range(4, compare_brute_upto + 1):
            best = bestbb = 0.0
            for lay in layouts(n):
                adj = adj_from_layout(lay)
                a = aobj_float(adj)
                best = max(best, a)
                if a > bestbb and min_defect(adj) == 0:
                    bestbb = a
            assert abs(best - float(rows[n][0])) <= 1e-12 * best, (n, best, float(rows[n][0]))
            assert abs(bestbb - float(rows[n][1])) <= 1e-12 * bestbb, (n, bestbb, float(rows[n][1]))
        print(f"[frontier] brute-force max over ALL trees and over ALL backbones agrees with the two DPs "
              f"for every n<={compare_brute_upto}")
    return dpa, dpb, rows


# ============================================================================ Pant families
def pant_tree(a):
    """T(a_1..a_m): core path c_1..c_m, core c_i carries a_i pendant paths of length 2 (cherries)
    (Pant, arXiv 2605.14176; same construction as _pant_check.py / bg_maximizer_family.caterpillar)."""
    m = len(a)
    edges = [(i, i + 1) for i in range(m - 1)]
    nid = m
    for i, ai in enumerate(a):
        for _ in range(ai):
            edges += [(i, nid), (nid, nid + 1)]
            nid += 2
    return adj_from_edges(nid, edges)


def pant_families(nmax):
    fams = []
    for t in range(3, 30):
        fams.append(("T(3,t,3)", (3, t, 3)))
        fams.append(("T(t,t,t,t)", (t, t, t, t)))
        fams.append(("T(t,t,t+1,t)", (t, t, t + 1, t)))
    return [(name, a) for name, a in fams if len(a) + 2 * sum(a) <= nmax]


def run_pant(nmax=64, dpa=None):
    dpa = dpa or FrontierDP(nmax, "all")
    rows = []
    for name, a in pant_families(nmax):
        adj = pant_tree(a)
        n = len(adj)
        v = aobj_exact(adj)
        mx, args = dpa.top(n)
        md = min_defect(adj)
        rows.append((name, a, n, md, v, mx))
        print(f"{name:13s} {str(a):16s} n={n:3d} minDefect={md} backbone={md == 0} Aobj={float(v):.10g} "
              f"max_n={float(mx):.10g} ratio={float(v / mx):.6f} is_maximizer={v == mx} "
              f"describe={describe(adj)}", flush=True)
    return rows


# ============================================================================ adversarial search
def random_tree(n, rng, kind):
    if kind == "prufer":
        seq = [rng.randrange(n) for _ in range(n - 2)]
        deg = [1] * n
        for x in seq:
            deg[x] += 1
        edges = []
        import heapq
        leaves = [i for i in range(n) if deg[i] == 1]
        heapq.heapify(leaves)
        for x in seq:
            leaf = heapq.heappop(leaves)
            edges.append((leaf, x))
            deg[x] -= 1
            if deg[x] == 1:
                heapq.heappush(leaves, x)
        u, v = heapq.heappop(leaves), heapq.heappop(leaves)
        edges.append((u, v))
        return adj_from_edges(n, edges)
    # preferential attachment (hub-rich) / cherry-biased growth
    adj = [[]]
    for v in range(1, n):
        if kind == "pa":
            wts = [len(a) + 1 for a in adj]
            p = rng.choices(range(v), weights=wts)[0]
        else:  # "cherry": attach to a random vertex, or extend a leaf into a cherry
            p = rng.randrange(v)
        adj.append([p])
        adj[p].append(v)
    return adj


def random_spr(adj, rng):
    n = len(adj)
    u = rng.randrange(n)
    v = rng.choice(adj[u])
    side = [False] * n
    side[u] = True
    st = [u]
    while st:
        x = st.pop()
        for y in adj[x]:
            if not side[y] and not (x == u and y == v):
                side[y] = True
                st.append(y)
    A = [x for x in range(n) if side[x]]
    B = [x for x in range(n) if not side[x]]
    a, b = rng.choice(A), rng.choice(B)
    if a == u and b == v:
        return None
    return apply_move(adj, (u, v, a, b))


def local_max(adj, a, rng):
    """First-improvement SPR ascent to a local maximum (float, strict gain > 1e-12 relative)."""
    improved = True
    while improved:
        improved = False
        moves = list(spr_moves(adj))
        rng.shuffle(moves)
        for mv in moves:
            t = apply_move(adj, mv)
            at = aobj_float(t)
            if at > a * (1 + 1e-12):
                adj, a, improved = t, at, True
                break
    return adj, a


def _search_job(args):
    n, seed, start, bb, steps = args
    rng = random.Random(seed)
    if start[0] == "random":
        adj = random_tree(n, rng, start[1])
    else:
        adj = [list(x) for x in start[1]]
        for _ in range(start[2]):
            t = random_spr(adj, rng)
            if t is not None:
                adj = t
    a = aobj_float(adj)
    thr = NEAR_FRAC * bb
    near = {}                 # canon -> edges for NON-backbones with Aobj >= NEAR_FRAC * best backbone
    beat = []
    best_nb = 0.0
    T0, T1 = 0.4, 0.001
    for i in range(steps):
        T = T0 * (T1 / T0) ** (i / steps)
        t = random_spr(adj, rng)
        if t is None:
            continue
        at = aobj_float(t)
        if at >= a or rng.random() < math.exp((math.log(at) - math.log(a)) / T):
            adj, a = t, at
            if a >= thr:
                if a > bb * (1 + 1e-12):
                    beat.append(edges_of(adj))
                if min_defect(adj) > 0:
                    best_nb = max(best_nb, a)
                    if len(near) < 150:
                        near.setdefault(canon(adj), edges_of(adj))
    adj, a = local_max(adj, a, rng)
    lm_defect = min_defect(adj)
    if a > bb * (1 + 1e-12):
        beat.append(edges_of(adj))
    # probe the neighbourhood of the local maximum (and of the seed): 1-3 random SPR moves, keeping
    # non-backbones with Aobj >= NEAR_FRAC * best backbone (these feed the coverage test)
    bases = [adj] + ([] if start[0] == "random" else [start[1]])
    for base in bases:
        for _ in range(300):
            t = base
            for _ in range(rng.randint(1, 3)):
                t2 = random_spr(t, rng)
                t = t2 if t2 is not None else t
            at = aobj_float(t)
            if at >= thr and min_defect(t) > 0:
                best_nb = max(best_nb, at)
                if len(near) < 300:
                    near.setdefault(canon(t), edges_of(t))
            if at > bb * (1 + 1e-12):
                beat.append(edges_of(t))
    return {"n": n, "start": start[0] if start[0] == "random" else start[3], "final": a,
            "final_edges": edges_of(adj), "final_defect": lm_defect, "near": near, "beat": beat,
            "best_nonbackbone": best_nb}


def _cov_edges(args):
    n, edges = args
    st, d, info = coverage_one(adj_from_edges(n, edges))
    return n, st, d, info if st == "FAIL" else None


def run_search(nmin, nmax, workers=16, runs_random=16, runs_seeded=16, steps=60000, n_random_cov=2000,
               near_cap=None, dump=None):
    near_cap = near_cap or NEAR_CAP
    t0 = time.time()
    dpa = FrontierDP(nmax, "all")
    dpb = FrontierDP(nmax, "backbone")
    BB = {}
    MX = {}
    for n in range(nmin, nmax + 1):
        mb, argsB = dpb.top(n)
        ma, argsA = dpa.top(n)
        BB[n], MX[n] = mb, (ma, argsA)
    print(f"[search] exhaustive DPs to n={nmax} done {time.time() - t0:.0f}s", flush=True)
    jobs = []
    rng = random.Random(20260924)
    for n in range(nmin, nmax + 1):
        bb = float(BB[n])
        for j in range(runs_random):
            jobs.append((n, rng.random(), ("random", ("prufer", "pa", "cherry")[j % 3]), bb, steps))
        seeds = [("dp_maximizer", MX[n][1][0])]
        for name, a in pant_families(nmax):
            if len(a) + 2 * sum(a) == n:
                seeds.append((f"pant{a}", pant_tree(a)))
        if n == 52:
            seeds.append(("T(6,6,6,6)", pant_tree((6, 6, 6, 6))))
        for j in range(runs_seeded):
            name, sadj = seeds[j % len(seeds)]
            jobs.append((n, rng.random(), ("seed", sadj, 1 + j % 6, name), bb, steps))
    print(f"[search] {len(jobs)} annealing runs, {steps} SPR steps each + local-max ascent", flush=True)
    per_n = {n: {"runs": 0, "best": 0.0, "lm_nonbb": [], "near": {}, "beat": [], "best_nb": 0.0}
             for n in range(nmin, nmax + 1)}
    with Pool(workers) as pool:
        for res in pool.imap_unordered(_search_job, jobs):
            r = per_n[res["n"]]
            r["runs"] += 1
            r["best"] = max(r["best"], res["final"])
            r["best_nb"] = max(r["best_nb"], res["best_nonbackbone"])
            if res["final_defect"] > 0:
                r["lm_nonbb"].append((res["final"], res["final_edges"], res["start"]))
            r["near"].update(res["near"])
            r["beat"] += res["beat"]
        print(f"[search] annealing done {time.time() - t0:.0f}s", flush=True)
        # exact confirmation of anything that beat the best backbone in floats (none expected)
        for n, r in per_n.items():
            for e in r["beat"]:
                v = aobj_exact(adj_from_edges(n, e))
                print(f"  !! n={n} float-beat candidate exact={v} bestBackbone={BB[n]} beats={v > BB[n]}")
        # coverage on the near-top non-backbones (capped per n) and on random trees
        cov_jobs = []
        for n, r in per_n.items():
            for c, e in list(r["near"].items())[:near_cap]:
                cov_jobs.append((n, e))
            for _, e, _ in r["lm_nonbb"]:
                cov_jobs.append((n, e))
        n_near = len(cov_jobs)
        crng = random.Random(7)
        for n in range(nmin, nmax + 1):
            for j in range(n_random_cov):
                cov_jobs.append((n, edges_of(random_tree(n, crng, ("prufer", "pa", "cherry")[j % 3]))))
        cov = {n: {"near_tested": 0, "rand_tested": 0, "backbone": 0, "covered": 0, "FAIL": []}
               for n in range(nmin, nmax + 1)}
        for idx, (n, st, d, info) in enumerate(pool.imap(_cov_edges, cov_jobs, chunksize=8)):
            c = cov[n]
            c["near_tested" if idx < n_near else "rand_tested"] += 1
            if st == "FAIL":
                info["origin"] = "near-top" if idx < n_near else "random"
                info["min_defect"] = d
                info["ratio_to_best_backbone"] = float(info["aobj"] / BB[n])
                c["FAIL"].append(info)
            else:
                c[st] += 1
        print(f"[search] coverage done {time.time() - t0:.0f}s", flush=True)
    if dump:
        import json
        with open(dump, "w") as fh:
            json.dump([dict(f, n=n, aobj=str(f["aobj"]), near=str(f["near"]))
                       for n in cov for f in cov[n]["FAIL"]], fh)
    for n in range(nmin, nmax + 1):
        r, c = per_n[n], cov[n]
        print(f"n={n:3d} runs={r['runs']} bestFound/bestBackbone={r['best'] / float(BB[n]):.9f} "
              f"float_beats={len(r['beat'])} nonbackbone_local_maxima={len(r['lm_nonbb'])} "
              f"(max ratio {max([x[0] for x in r['lm_nonbb']], default=0) / float(BB[n]):.4f}) "
              f"best_nonbackbone_seen_ratio={r['best_nb'] / float(BB[n]):.4f} "
              f"near_top_nonbackbones={len(r['near'])} | coverage near={c['near_tested']} "
              f"random={c['rand_tested']} (backbone {c['backbone']}, covered {c['covered']}) "
              f"FAIL={len(c['FAIL'])}", flush=True)
        for f in c["FAIL"][:1]:
            print("   FAIL", f)
    return per_n, cov


# ============================================================================ targeted coverage probe
def random_backbone(n, rng):
    """Uniform-ish random backbone: a spine whose vertices receive leaves / cherries / arms until the
    size is exactly n."""
    edges = []
    nid = 1
    spine = [0]
    while nid < n:
        room = n - nid
        kind = rng.random()
        v = rng.choice(spine)
        if kind < 0.15 and room >= 1:
            edges.append((v, nid)); nid += 1                              # new spine vertex / leaf
            spine.append(nid - 1)
        elif kind < 0.25:
            edges.append((v, nid)); nid += 1                              # leaf
        elif kind < 0.65 and room >= 2:
            edges += [(v, nid), (nid, nid + 1)]; nid += 2                 # cherry
        elif room >= 3:
            j = rng.randint(1, max(1, min(8, (room - 1) // 2)))
            a = nid; edges.append((v, a)); nid += 1
            for _ in range(j):
                edges += [(a, nid), (nid, nid + 1)]; nid += 2             # arm with j cherries
    return adj_from_edges(n, edges)


def _probe_job(args):
    n, seed, count = args
    rng = random.Random(seed)
    tested = fails = 0
    out = []
    for _ in range(count):
        if rng.random() < 0.5:
            t = random_backbone(n, rng)
            for _ in range(rng.randint(1, 2)):
                t2 = random_spr(t, rng)
                t = t2 if t2 is not None else t
            origin = "backbone+SPR"
        else:
            t = random_tree(n, rng, ("prufer", "pa", "cherry")[rng.randrange(3)])
            origin = "random"
        st, d, info = coverage_one(t)
        if st == "backbone":
            continue
        tested += 1
        if st == "FAIL":
            fails += 1
            info["origin"] = origin
            info["min_defect"] = d
            out.append(info)
    return n, tested, fails, out


def run_probe(nmin, nmax, count, workers=16, dump=None):
    import json
    jobs = [(n, 1000 * n + j, count // 16) for n in range(nmin, nmax + 1) for j in range(16)]
    agg = {}
    allf = []
    with Pool(workers) as pool:
        for n, tested, fails, out in pool.imap_unordered(_probe_job, jobs):
            a = agg.setdefault(n, [0, 0])
            a[0] += tested
            a[1] += fails
            allf += [dict(f, n=n) for f in out]
    for n in sorted(agg):
        print(f"[probe n={n}] defective sampled={agg[n][0]} FAIL={agg[n][1]}", flush=True)
    if dump:
        with open(dump, "w") as fh:
            json.dump([dict(f, aobj=str(f["aobj"]), near=str(f["near"])) for f in allf], fh)
    return agg, allf


# ============================================================================ local-coverage witnesses
# Trees with minDefect 1 for which NO SPR-distance-1 tree has lower minDefect and Aobj >= Aobj(T), i.e.
# counterexamples to the single-SPR (+ free reroot) coverage tested by hwh_viability.py.  They do NOT
# contradict HnormMulti (each is far below the best backbone of its size) nor the Lean obligation
# StraightProgress_sized, whose witness t' may be ANY same-size tree (see the report).
WITNESS_25 = [(0, 3), (1, 22), (1, 24), (1, 5), (2, 24), (2, 7), (3, 21), (4, 9), (4, 13), (5, 10), (6, 10), (7, 11), (8, 14), (8, 15), (9, 16), (12, 16), (12, 22), (12, 21), (14, 18), (15, 19), (15, 22), (17, 23), (17, 20), (19, 23)]
WITNESS_29 = [(0, 24), (1, 5), (2, 7), (2, 26), (2, 28), (3, 9), (3, 28), (4, 13), (4, 26), (5, 25), (6, 11), (6, 16), (7, 12), (8, 12), (9, 14), (10, 17), (10, 18), (11, 19), (14, 23), (15, 19), (15, 25), (15, 26), (17, 21), (18, 22), (18, 26), (20, 24), (20, 27), (22, 27)]
WITNESS_34 = [(0, 21), (1, 17), (2, 4), (2, 32), (3, 28), (4, 10), (4, 18), (4, 21), (5, 16), (5, 25), (6, 13), (7, 8), (7, 10), (7, 22), (8, 33), (9, 10), (9, 29), (9, 30), (10, 15), (10, 25), (11, 12), (12, 22), (13, 20), (14, 18), (15, 27), (16, 24), (17, 31), (19, 23), (20, 29), (23, 33), (24, 26), (25, 31), (28, 30)]


def check_witness(edges, independent=True):
    """Exact re-verification (this file's engine, and optionally the repo's networkx engine
    phase0_straightprogress_sized: spr_neighbors / min_defect_over_roots / Aobj = pi_literal)."""
    n = max(max(e) for e in edges) + 1
    adj = adj_from_edges(n, edges)
    a, md = aobj_exact(adj), min_defect(adj)
    red = [aobj_exact(t) for t in (apply_move(adj, mv) for mv in spr_moves(adj)) if min_defect(t) < md]
    res = {"n": n, "Aobj": a, "minDefect": md, "defect_reducing_moves": len(red), "best": max(red),
           "fail": max(red) < a}
    if independent:
        import networkx as nx
        import phase0_straightprogress_sized as P
        G = nx.Graph(edges)
        aG, dG = P.Aobj(G), P.min_defect_over_roots(G)
        res["independent_fail"] = (aG == a and dG == md and all(
            P.Aobj(Gp) < aG for Gp in P.spr_neighbors(G) if P.min_defect_over_roots(Gp) < dG))
    return res


# ============================================================================ sanity
def sanity(nmax=10):
    import networkx as nx
    import phase0_straightprogress_sized as P
    cnt = 0
    for n in range(2, nmax + 1):
        for G in nx.nonisomorphic_trees(n):
            G = nx.convert_node_labels_to_integers(G)
            adj = adj_from_edges(n, G.edges())
            ref = P.Aobj(G)
            assert aobj_exact(adj) == ref, (n, ref)
            for r0 in range(n):
                assert aobj_exact(adj, r0) == ref
            assert abs(aobj_float(adj) - float(ref)) <= 1e-12 * float(ref)
            assert min_defect(adj) == P.min_defect_over_roots(G), (n, list(G.edges()))
            cnt += 1
    # layout enumeration count check (OEIS A000055)
    for n, c in [(10, 106), (12, 551), (14, 3159)]:
        assert sum(1 for _ in layouts(n)) == c
    print(f"[sanity] {cnt} trees n<=({nmax}): aobj_exact == pi_literal (all roots), aobj_float ok, "
          f"min_defect == P.min_defect_over_roots; layout counts match A000055 -- OK")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "sanity"
    if cmd == "sanity":
        sanity()
    elif cmd == "coverage":
        run_coverage(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 12)
    elif cmd == "witness":
        for name, w in (("WITNESS_25", WITNESS_25), ("WITNESS_29", WITNESS_29), ("WITNESS_34", WITNESS_34)):
            r = check_witness(w)
            print(f"{name}: n={r['n']} minDefect={r['minDefect']} Aobj={r['Aobj']} ({float(r['Aobj']):.6f}) "
                  f"defect-reducing SPR moves={r['defect_reducing_moves']} best Aobj among them={r['best']} "
                  f"({float(r['best']):.6f}) single-SPR coverage FAILS={r['fail']} "
                  f"independent engine agrees={r['independent_fail']}")
    elif cmd == "probe":
        run_probe(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
                  dump=sys.argv[5] if len(sys.argv) > 5 else None)
    elif cmd == "pant":
        run_pant(int(sys.argv[2]) if len(sys.argv) > 2 else 64)
    elif cmd == "search":
        run_search(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 16,
                   dump=sys.argv[5] if len(sys.argv) > 5 else None)
    elif cmd == "search-small":      # denser near-top search for the smallest single-SPR coverage failure
        run_search(int(sys.argv[2]), int(sys.argv[3]), 16, runs_random=48, runs_seeded=48, n_random_cov=0,
                   near_cap=int(sys.argv[5]) if len(sys.argv) > 5 else 6000, dump=sys.argv[4] if len(sys.argv) > 4 else None)
    elif cmd == "frontier":
        run_frontier(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 0)
