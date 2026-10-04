"""Independent implementation of the (Z,W) upper-right hull search (written separately from hulldp.py / hulldp2.py).
Usage: python3 mydp.py NMAX [KMAX] [mode]; mode = hull (default) | pareto
Prints n k M(n,k) exact.
Planted branch: Z = sum over matchings of branch internal edges (root degree counts parent edge),
W = (sum over matchings with root unmatched)/deg(root).  Children bundle: P = prod Z, Q = sum W_c prod others.
Branch: Z = P + Q/d, W = P/d (d = #children + 1).  Unrooted: pi = P + Q/c.
Leaves added in closed form (lam leaves: Q += lam P), non-leaf children limited by KMAX.
"""
import sys
from fractions import Fraction as Fr

MODE = "hull"


def prune(pts):
    if len(pts) <= 1:
        return pts
    pts = sorted(set(pts), key=lambda p: (-p[0], -p[1]))
    par = []
    for p in pts:
        if not par or p[1] > par[-1][1]:
            par.append(p)
    if MODE == "pareto":
        return par
    out = []
    for p in par:  # x descending, y ascending
        while len(out) >= 2:
            a, b = out[-2], out[-1]
            cr = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
            if cr <= 0:  # b on or below chord a-p: not a strict vertex
                out.pop()
            else:
                break
        out.append(p)
    return out


def run(NMAX, KMAX):
    cls = {}   # size -> {(nu, free): [(Z,W)]} for non-leaf planted branches (size>=2)
    NB = {0: {(0, 0, 0): [(Fr(1), Fr(0))]}}  # nonleaf bundles: size -> {(c, nu, anyfree): [(P,Q)]}
    res = {}
    for s in range(1, NMAX):
        acc = {}
        for j in range(2, s + 1):
            for (cnu, cf), items in cls.get(j, {}).items():
                for (c, nu, f), bl in NB.get(s - j, {}).items():
                    if nu + cnu > KMAX:
                        continue
                    L = acc.setdefault((c + 1, nu + cnu, f | cf), [])
                    for (P, Q) in bl:
                        for (Z, W) in items:
                            L.append((P * Z, Q * Z + P * W))
        NB[s] = {key: prune(v) for key, v in acc.items()}
        newc = {}; best = {}
        for size in range(0, s + 1):
            lam = s - size
            for (c, nu, f), bl in NB.get(size, {}).items():
                cc = c + lam
                ff = f | (1 if lam > 0 else 0)
                kk = nu + ff
                if kk > KMAX:
                    continue
                for (P, Q) in bl:
                    QQ = Q + lam * P
                    d = cc + 1
                    if size == s and lam == 0 and c == 0:
                        pass
                    newc.setdefault((kk, 1 - ff), []).append((P + QQ / d, P / d))
                    if cc >= 1:
                        v = P + QQ / cc
                        if kk not in best or v > best[kk]:
                            best[kk] = v
        cls[s + 1] = {key: prune(v) for key, v in newc.items()}
        res[s + 1] = best
    return res


if __name__ == "__main__":
    NMAX = int(sys.argv[1]); KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    if len(sys.argv) > 3:
        MODE = sys.argv[3]
    res = run(NMAX, KMAX)
    for n in range(2, NMAX + 1):
        for k in sorted(res[n]):
            print(f"n={n} k={k} max={res[n][k]}")
        sys.stdout.flush()
