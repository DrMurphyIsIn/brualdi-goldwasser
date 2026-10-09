"""Negative control for the rate gaps at lambda = 1: each tabulated Gamma_K + 10^-5 must be rejected.

The check is the function `gamma` of ../../bg_spider_comparison/conc.py, imported unchanged: for the cap
K it encloses sigma~(B) for every stalk [A_j], j <= 4, and every end hub with arms of at most 18 cherries
(more if needed), covers longer arms by the proved tail bound, and returns the enclosure at the minimizing
shape together with that shape. A tabulated value G is accepted as a lower bound for Gamma_K iff the lower
end of that enclosure is >= G.

Positive control: G = the stated value of Gamma_{k-1} (k = K + 1), for K = 1, ..., 22;
the minimizing shape must be the one in the table.
Negative control: G + 10^-5 must be rejected; moreover the upper end of the enclosure at the minimizing
shape must lie below G + 10^-5, i.e. that single shape refutes the perturbed bound (it is false, not merely
uncertified).

Usage: python3 nc_rate_gap.py
"""
import os
import sys
import time
from pathlib import Path

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "bg_spider_comparison"))

from fractions import Fraction as Fr
import conc                      # reads ../../bg_spider_comparison/certify_out.json (the certified rates)
from ivtools import F

# stated lower bounds Gamma_{k-1} and shapes, indexed by k = K + 1 (k = 2..23)
TABLE = {
    2: ("0.039104", "A1"), 3: ("0.039104", "A1"), 4: ("0.026563", "C2A3"), 5: ("0.015081", "C3A4"),
    6: ("0.008500", "C4A4"), 7: ("0.006729", "C5A4"), 8: ("0.006839", "C6A4"), 9: ("0.007662", "C6A4"),
    10: ("0.008335", "C6A4"), 11: ("0.008895", "C6A4"), 12: ("0.009366", "C6A4"), 13: ("0.009768", "C6A4"),
    14: ("0.010116", "C6A4"), 15: ("0.010418", "C6A4"), 16: ("0.010685", "C6A4"), 17: ("0.010920", "C6A4"),
    18: ("0.011131", "C6A4"), 19: ("0.011321", "C6A4"), 20: ("0.011491", "C6A4"), 21: ("0.011647", "C6A4"),
    22: ("0.011788", "C6A4"), 23: ("0.011918", "C6A4"),
}
EPS = Fr(1, 10 ** 5)


def shape_name(arg):
    """conc.gamma's argmin -> the notation of the table: ('stalk', j) = [A_j]; ('hub', (c, s, m1, m2)) =
    [C^c A_s^m1 A_{s+1}^m2]"""
    if arg[0] == 'stalk':
        return f"A{arg[1]}"
    c, s, m1, m2 = arg[1]
    out = f"C{c}" if c else ""
    if m1:
        out += f"A{s}" + (f"^{m1}" if m1 > 1 else "")
    if m2:
        out += f"A{s + 1}" + (f"^{m2}" if m2 > 1 else "")
    return out


if __name__ == "__main__":
    t0 = time.time()
    ok = True
    print("[control 3] rate gaps: tabulated Gamma_K (PASS expected) and Gamma_K + 1e-5 (FAIL expected)")
    print("   k   K  shape      enclosure at the minimizing shape   table G    unpert.  G+1e-5 pert.  refuted")
    for k in range(2, 24):
        K = k - 1
        best, arg = conc.gamma(K)
        G = Fr(TABLE[k][0])
        sh = shape_name(arg)
        unpert = best.a >= F(G) and sh == TABLE[k][1]
        pert = best.a >= F(G + EPS)
        refuted = best.b < F(G + EPS)
        good = unpert and (not pert) and refuted
        ok &= good
        print(f"  {k:2d}  {K:2d}  {sh:<9s}  [{float(best.a):.9f}, {float(best.b):.9f}]  {TABLE[k][0]}   "
              f"{'PASS' if unpert else 'FAIL':5s}    {'PASS' if pert else 'FAIL':5s}         {refuted}", flush=True)
    print(f"\nruntime {time.time() - t0:.1f} s")
    print("ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED" if ok else "SOME NEGATIVE CONTROL DID NOT BEHAVE AS EXPECTED")
    sys.exit(0 if ok else 1)
