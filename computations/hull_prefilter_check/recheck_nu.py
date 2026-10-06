"""Re-check of the floating-point prefilter of ../nu_hull_search/hulldp2.py (lem:nu-small-cv).

Runs the recursion of hulldp2.py (its own functions, imported unchanged: float_filter, exact_hull,
Group, intern) and, for every bundle class, certifies with certify_drop.py that no candidate discarded
by the prefilter lies in Ext of the class. (hulldp2.py's filter uses absolute tolerances and is not
by itself a proof that only interior points are discarded; this re-check makes it one.) At the end it
compares the exact maxima M(n, k) with ../nu_hull_search/dpk215_8.txt.

Usage: OMP_NUM_THREADS=1 python3 recheck_nu.py [NMAX [KMAX]]      (default 215 8)
"""
import os
import re
import sys
import time
from fractions import Fraction as Fr

os.environ.setdefault("OMP_NUM_THREADS", "1")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "nu_hull_search"))
sys.path.insert(0, HERE)
import numpy as np
import hulldp2 as H2                            # ../nu_hull_search/hulldp2.py, unchanged
from certify_drop import Tally, certify_class


def run(NMAX, KMAX, tally):
    one = Fr(1)
    classes = {1: {(0, 1): H2.Group([(one, one, 0)])}}
    bundles = {0: {(0, 0, 0): H2.Group([(one, Fr(0), ())])}}
    results = {}
    for s in range(1, NMAX):
        cand = {}
        for j in range(1, s + 1):
            for (cnu, cs), cg in classes[j].items():
                for (c, nu, f), bg in bundles[s - j].items():
                    nk = (c + 1, nu + cnu, f | cs)
                    if KMAX is not None and nu + cnu > KMAX:
                        continue
                    Pn = np.multiply.outer(bg.F1, cg.F1).ravel()
                    Qn = (np.multiply.outer(bg.F2, cg.F1) + np.multiply.outer(bg.F1, cg.F2)).ravel()
                    cand.setdefault(nk, []).append((Pn, Qn, bg, cg, len(cg.F1)))
        newb = {}
        for nk, lst in cand.items():
            P = np.concatenate([x[0] for x in lst])
            Q = np.concatenate([x[1] for x in lst])
            sel = H2.float_filter(P, Q)
            offs = np.cumsum([0] + [len(x[0]) for x in lst])

            def locate(g, lst=lst, offs=offs):
                blk = int(np.searchsorted(offs, g, side="right") - 1)
                _, _, bg, cg, nc = lst[blk]
                r = int(g - offs[blk])
                bi, ci = divmod(r, nc)
                return bg, cg, bi, ci

            def exact_of(g):
                bg, cg, bi, ci = locate(g)
                return (bg.X1[bi] * cg.X1[ci], bg.X2[bi] * cg.X1[ci] + bg.X1[bi] * cg.X2[ci])

            pts = {}
            surv = []
            for g in sel:
                bg, cg, bi, ci = locate(int(g))
                ch = tuple(sorted(bg.pay[bi] + (cg.pay[ci],)))
                Px, Qx = exact_of(int(g))
                surv.append((Px, Qx))
                if ch in pts:
                    continue
                pts[ch] = (Px, Qx, ch)
            certify_class(P, Q, sel, surv, exact_of, tally, (s, nk))
            newb[nk] = H2.Group(H2.exact_hull(list(pts.values())))
        bundles[s] = newb
        cl = {}
        best = {}
        for (c, nu, f), bg in newb.items():
            d = c + 1
            key = (nu + f, 1 - f)
            L = cl.setdefault(key, [])
            k = nu + f
            for Pv, Qv, ch in zip(bg.X1, bg.X2, bg.pay):
                L.append((Pv + Qv / d, Pv / d, H2.intern(ch)))
                val = Pv + Qv / c
                if k not in best or val > best[k]:
                    best[k] = val
        classes[s + 1] = {key: H2.Group(H2.exact_hull(v)) for key, v in cl.items()}
        results[s + 1] = best
        if (s + 1) % 25 == 0:
            print("# n=%d  %s" % (s + 1, tally.line()), file=sys.stderr, flush=True)
    return results


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 215
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    t0 = time.time()
    tally = Tally()
    res = run(NMAX, KMAX, tally)
    print("nu_hull_search prefilter re-check, n <= %d, KMAX = %d (%.0f s)" % (NMAX, KMAX, time.time() - t0))
    print("  " + tally.line())
    ref = {}
    for line in open(os.path.join(HERE, "..", "nu_hull_search", "dpk215_8.txt")):
        m = re.match(r"n=(\d+) k=(\d+) max=(\S+)", line)
        if m:
            ref[(int(m.group(1)), int(m.group(2)))] = Fr(m.group(3))
    mine = {(n, k): v for n in res for k, v in res[n].items()}
    common = [key for key in mine if key in ref]
    same = all(mine[key] == ref[key] for key in common) and len(common) == len(mine)
    print("  exact M(n, k) equal to dpk215_8.txt on all %d pairs computed: %s" % (len(common), same))
    ok = same and not tally.failed
    if tally.failed:
        print("  first uncertified points:", tally.failed[:5])
    print("RESULT: " + ("every discarded candidate is outside Ext of its class" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
