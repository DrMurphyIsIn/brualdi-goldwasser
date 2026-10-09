# Third implementation of the hull computation (M_n for 4 <= n <= 491, all maximizers), written separately from dp.py and
# dp_check.py, from the statements alone: pure Fractions throughout (no floating-point step), its own hull
# routine (exact strict-Pareto sweep + gift wrapping, all collinear points kept), its own interning of
# rooted branches, its own centre/bicentre canonical form and its own matching recursion for pi.
#
# Usage: python3 rational_dp.py N [NB]
#   N  : run the DP for all n <= N and print one line per n (2 <= n <= N);
#   NB : optional; for every class with s <= NB, also assert that the gift-wrap hull equals the set given
#        by the definition of Ext (K_brute).
# The appendix table is read from ../table_maximizers.tex (relative to this file).
import sys, os, re
from fractions import Fraction as F
sys.setrecursionlimit(100000)

def K_giftwrap(pts):
    """pts: dict (x,y)->payload set.  Return dict of points that maximise some a>0 (a1,a2>0)."""
    P = list(pts.keys())
    if not P: return {}
    # exact strict-Pareto sweep (x desc, y desc); a Pareto-dominated point is never in K
    P.sort(reverse=True)
    par = []; ym = None
    for p in P:
        if ym is None or p[1] > ym: par.append(p); ym = p[1]
    P = par
    # start: max y, then max x
    ymax = max(p[1] for p in P)
    v = max((p for p in P if p[1] == ymax), key=lambda p: p[0])
    keep = {v}
    while True:
        right = [p for p in P if p[0] > v[0]]
        if not right: break
        best = None; on = []
        for p in right:
            s = (p[1] - v[1]) / (p[0] - v[0])
            if best is None or s > best: best, on = s, [p]
            elif s == best: on.append(p)
        if best >= 0:
            raise AssertionError("nonnegative slope from hull vertex")
        keep.update(on)
        v = max(on, key=lambda p: p[0])
    return {p: pts[p] for p in keep}

def K_brute(pts):
    """Definition: p in K iff exists t>0 with p maximising x + t*y (a=(1,t))."""
    P = list(pts)
    out = set()
    for p in P:
        lo = F(0); lo_closed = False; hi = None; ok = True
        for q in P:
            if q == p: continue
            dx = p[0]-q[0]; dy = p[1]-q[1]
            # need dx + t dy >= 0
            if dy > 0:
                b = -dx/dy
                if b > lo or (b == lo and not lo_closed and b > 0): lo, lo_closed = b, True
                elif b == lo: lo_closed = True
            elif dy < 0:
                b = dx/(-dy)
                if hi is None or b < hi: hi = b
            else:
                if dx < 0: ok = False; break
        if not ok: continue
        # need t>0, t>=lo, t<=hi
        if hi is not None and hi <= 0: continue
        if hi is None: out.add(p); continue
        if lo > 0:
            if lo <= hi: out.add(p)
        else:
            out.add(p)  # hi>0
    return out

TR = {(): 0}; TL = [()]
def tid(ch):
    t = TR.get(ch)
    if t is None:
        t = len(TL); TL.append(ch); TR[ch] = t
    return t

def run(N, check_brute_upto=0):
    H = {1: {(F(1), F(1)): {0}}}
    B = {0: {0: {(F(1), F(0)): {()}}}}
    res = {}
    for s in range(1, N):
        B[s] = {}
        for c in range(1, s+1):
            cand = {}
            for j in range(1, s-c+2):
                prev = B[s-j].get(c-1)
                if not prev: continue
                for (P, Q), pb in prev.items():
                    for (Z, W), ph in H[j].items():
                        key = (P*Z, Q*Z + P*W)
                        S = cand.setdefault(key, set())
                        for b in pb:
                            for h in ph:
                                S.add(tuple(sorted(b + (h,))))
            if not cand: continue
            K = K_giftwrap(cand)
            if s <= check_brute_upto:
                assert set(K) == K_brute(cand), (s, c)
            B[s][c] = K
        cand = {}
        best = None; bp = []
        for c, bc in B[s].items():
            for (P, Q), pb in bc.items():
                key = (P + Q/(c+1), P/(c+1))
                S = cand.setdefault(key, set())
                for b in pb: S.add(tid(b))
                v = P + Q/c
                if best is None or v > best: best, bp = v, list(pb)
                elif v == best: bp += list(pb)
        K = K_giftwrap(cand)
        if s+1 <= check_brute_upto:
            assert set(K) == K_brute(cand)
        H[s+1] = K
        res[s+1] = (best, bp)
        if os.environ.get('PROG'):
            forms = {canon(bundle_adj(b)) for b in bp}
            print(f'n={s+1} M={best.numerator}/{best.denominator} count={len(forms)}', file=sys.stderr, flush=True)
    return res

def bundle_adj(b):
    adj = [[]]
    def add(t, p):
        v = len(adj); adj.append([p]); adj[p].append(v)
        for c in TL[t]: add(c, v)
    for t in b: add(t, 0)
    return adj

def canon(adj):
    n = len(adj)
    if n <= 2: return str(n)
    deg = [len(a) for a in adj]; leaves = [v for v in range(n) if deg[v] == 1]; rem = n
    alive = [True]*n
    while rem > 2:
        nl = []
        for v in leaves:
            alive[v] = False; rem -= 1
            for u in adj[v]:
                if alive[u]:
                    deg[u] -= 1
                    if deg[u] == 1: nl.append(u)
        leaves = nl
    cents = [v for v in range(n) if alive[v]]
    def enc(v, p):
        return tuple(sorted(enc(u, v) for u in adj[v] if u != p))
    if len(cents) == 1: return ("c", enc(cents[0], -1))
    a, b = cents
    return ("b",) + tuple(sorted([enc(a, b), enc(b, a)]))

def pi_tree(adj):
    """matching DP: g0[v]=weight of matchings in subtree with v free, g1 v matched."""
    n = len(adj); deg = [len(a) for a in adj]
    par = [-1]*n; order = [0]; 
    for v in order:
        for u in adj[v]:
            if u != par[v]: par[u] = v; order.append(u)
    g0 = [F(0)]*n; g1 = [F(0)]*n
    for v in reversed(order):
        ch = [u for u in adj[v] if u != par[v]]
        prod = F(1)
        for u in ch: prod *= (g0[u] + g1[u])
        g0[v] = prod
        s = F(0)
        for u in ch:
            s += prod / (g0[u] + g1[u]) * g0[u] / (deg[u]*deg[v])
        g1[v] = s
    return g0[0] + g1[0]

def is_spider(adj):
    n = len(adj)
    for v in range(n):
        good = True
        for u in adj[v]:
            ch = [w for w in adj[u] if w != v]
            if not ch: continue
            if len(ch) == 1 and len(adj[ch[0]]) == 1: continue  # cherry
            if all(len(adj[w]) == 2 and len(adj[[x for x in adj[w] if x != u][0]]) == 1 for w in ch): continue
            good = False; break
        if good: return True
    return False

def spider(c, arms):
    adj = [[]]
    def nv(p):
        v = len(adj); adj.append([p]); adj[p].append(v); return v
    for _ in range(c): nv(nv(0))
    for j in arms:
        u = nv(0)
        for _ in range(j): nv(nv(u))
    return adj

def table():
    txt = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "table_maximizers.tex")).read()
    out = {}
    for line in txt.splitlines():
        if not re.match(r"^\s*\d+\s*&", line): continue
        cells = line.replace("\\\\", "").split("&")
        for i in range(0, len(cells) - 1, 3):
            if not cells[i].strip(): continue
            n = int(cells[i].strip()); d = cells[i+1]
            c = 0; arms = []
            for tok in re.findall(r"\$([^$]*)\$", d):
                m = re.fullmatch(r"(C|A_\{(\d+)\})(?:\^\{(\d+)\})?", tok.strip())
                assert m, tok
                r = int(m.group(3) or 1)
                if m.group(1) == "C": c += r
                else: arms += [int(m.group(2))]*r
            assert 1 + 2*c + sum(1+2*j for j in arms) == n, (n, d)
            out[n] = (c, arms)
    return out

if __name__ == "__main__":
    N = int(sys.argv[1]); cb = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    res = run(N, cb); tab = table()
    for n in range(2, N+1):
        v, bp = res[n]
        forms = {}
        for b in bp:
            a = bundle_adj(b); forms.setdefault(canon(a), a)
        for a in forms.values(): assert pi_tree(a) == v
        sp = all(is_spider(a) for a in forms.values())
        tm = ""
        if n in tab:
            ta = spider(*tab[n]); tm = "MATCH" if canon(ta) in forms else "MISMATCH"
            assert pi_tree(ta) == v or tm == "MISMATCH"
        print(f"n={n} M={v.numerator}/{v.denominator} count={len(forms)} allspider={sp} table={tm}", flush=True)
