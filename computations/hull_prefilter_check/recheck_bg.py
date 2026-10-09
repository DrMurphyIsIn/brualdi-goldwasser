"""Re-check of the floating-point prefilter of ../bg_hull_dp/dp.py (exact maxima M_n, n <= 491).

Runs the recursion of dp.py (its own functions, imported unchanged: float_survivors, exact_K, Hull,
intern) and, for every bundle class B[s][c], certifies with certify_drop.py that no candidate
discarded by the prefilter lies in Ext of the class. At the end it compares the exact maxima M_n with
../bg_hull_dp/results_dp_491.txt.

Usage: OMP_NUM_THREADS=1 python3 recheck_bg.py [NMAX]      (default NMAX = 491)
"""
import os
import re
import sys
import time
from fractions import Fraction as Fr

os.environ.setdefault("OMP_NUM_THREADS", "1")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "bg_hull_dp"))
sys.path.insert(0, HERE)
import numpy as np
import dp                                       # ../bg_hull_dp/dp.py, unchanged
from certify_drop import Tally, certify_class


def run(NMAX, tally):
    one = Fr(1)
    H = {1: dp.Hull([(one, one, {0})])}
    B = {0: {0: dp.Hull([(one, Fr(0), {()})])}}
    results = {}
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
            X = np.concatenate([b[0] for b in blocks])
            Y = np.concatenate([b[1] for b in blocks])
            sel = dp.float_survivors(X, Y)
            offs = np.cumsum([0] + [len(b[0]) for b in blocks])

            def exact_of(g, blocks=blocks, offs=offs):
                blk = int(np.searchsorted(offs, g, side="right") - 1)
                _, _, bg, hg = blocks[blk]
                r = int(g - offs[blk])
                bi, hi = divmod(r, len(hg))
                return (bg.x[bi] * hg.x[hi], bg.y[bi] * hg.x[hi] + bg.x[bi] * hg.y[hi])

            pts = {}
            for g in sel:
                P, Q = exact_of(int(g))
                blk = int(np.searchsorted(offs, g, side="right") - 1)
                _, _, bg, hg = blocks[blk]
                r = int(g - offs[blk])
                bi, hi = divmod(r, len(hg))
                S = pts.setdefault((P, Q), set())
                for bun in bg.pay[bi]:
                    for t in hg.pay[hi]:
                        S.add(tuple(sorted(bun + (t,))))
            certify_class(X, Y, sel, list(pts.keys()), exact_of, tally, (s, c))
            B[s][c] = dp.Hull(dp.exact_K(pts))
        pts = {}
        best = None
        for c, bg in B[s].items():
            d = c + 1
            for P, Q, pay in zip(bg.x, bg.y, bg.pay):
                S = pts.setdefault((P + Q / d, P / d), set())
                for bun in pay:
                    S.add(dp.intern(bun))
                v = P + Q / c
                if best is None or v > best:
                    best = v
        H[s + 1] = dp.Hull(dp.exact_K(pts))
        results[s + 1] = best
        if (s + 1) % 50 == 0:
            print("# n=%d  %s" % (s + 1, tally.line()), file=sys.stderr, flush=True)
    return results


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 491
    t0 = time.time()
    tally = Tally()
    res = run(NMAX, tally)
    print("bg_hull_dp prefilter re-check, n <= %d (%.0f s)" % (NMAX, time.time() - t0))
    print("  " + tally.line())
    ref = {}
    for line in open(os.path.join(HERE, "..", "bg_hull_dp", "results_dp_491.txt")):
        m = re.match(r"n=(\d+) M=(\d+)/(\d+) ", line)
        if m:
            ref[int(m.group(1))] = Fr(int(m.group(2)), int(m.group(3)))
    same = all(res[n] == ref[n] for n in range(2, NMAX + 1))
    print("  exact M_n equal to results_dp_491.txt for 2 <= n <= %d: %s" % (NMAX, same))
    ok = same and not tally.failed
    if tally.failed:
        print("  first uncertified points:", tally.failed[:5])
    print("RESULT: " + ("every discarded candidate is outside Ext of its class" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
