"""Negative control for Proposition prop:bg-gap (non-atom gap): the check must reject delta_0 = 0.0143.

The check is section B of ../../bg_rate/certify.py, re-run here with the same routines (`ivtools`, `core`
of ../../bg_rate, imported unchanged): for each child count c of a minimal non-atom a rigorous lower bound
of sigma_v + sum sigma(children) is computed (c = 1: Phi_1(3/7); 2 <= c <= 9: m_c + min_a (w_c(y_a) +
sigma(a)) over a in {leaf, A_1, ..., A_30} and the tail A_{>30}; c = 10, 11, 12: interval branch-and-bound
of min Phi_c on [0, c]; c >= 13: Q(13)), and delta_0 is accepted only if every bound is >= delta_0.

Positive control: delta_0 = 0.01426 (the value of the paper) must be accepted.
Negative control: delta_0 = 0.0143 must be rejected, since the per-child minimum (c = 6, a = A_4) is
0.014273... < 0.0143.

Usage: python3 nc_nonatom_gap.py
"""
import os
import sys
import time
from pathlib import Path

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "bg_rate"))

from fractions import Fraction as Fr
from mpmath import iv, mpf
from ivtools import F, ivfr, KAP, GAM, LAM, QI, THIRD, PhiH_iv, bb_lower
from core import log_encl, Q


# ---- section B of ../../bg_rate/certify.py (same formulas, same parameters) ----
def PhiI(c, S):
    SI = S if isinstance(S, iv.mpf) else F(S)
    return PhiH_iv(c, SI, 0)


def D_minus(c):
    r = F(Fr(3, 4 * c + 3))
    return 2 * KAP * (THIRD - QI) - r + 2 * KAP * (r - QI) * r ** 2


def D_plus(c):
    r = F(Fr(3, 4 * c + 3))
    return GAM - r + 2 * KAP * (r - QI) * r ** 2


def atom_slack(j):
    if j == 'L' or j == 'C':
        return iv.mpf(0)
    return PhiI(j, Fr(j, 3))


def atom_x(j):
    return Fr(1) if j == 'L' else (Fr(1, 3) if j == 'C' else Fr(3, 4 * j + 3))


def w_c(c, x):
    X = F(x)
    if x <= Fr(1, 3):
        return KAP * (THIRD - X) ** 2 + (-D_minus(c)) * (THIRD - X)
    return D_plus(c) * (X - THIRD)


def gap_rows(J=30):
    """The lower bounds of section B: list of (c, argmin, interval)."""
    rows = []
    for c in range(2, 10):
        assert D_minus(c).b < 0 < D_plus(c).a
        mc = PhiI(c, Fr(c, 3))
        cands = [('L', mc + w_c(c, Fr(1)))]
        for j in range(1, J + 1):
            cands.append((f'A{j}', mc + w_c(c, atom_x(j)) + atom_slack(j)))
        cands.append((f'A>{J}', mc + w_c(c, atom_x(J + 1))))
        best = min(cands, key=lambda t: t[1].a)
        rows.append((c, best[0], best[1]))
    rows.append((1, 'A_j (Phi_1(3/7))', PhiI(1, Fr(3, 7))))
    for c in (10, 11, 12):
        lb, ub = bb_lower(lambda X, c=c: PhiH_iv(c, X, 0), mpf(0), mpf(c), nmax=3000)
        rows.append((c, 'any', iv.mpf([lb, ub])))
    p = 1 + Q
    L = log_encl((1 + p * 13) / 14)
    q13 = LAM - KAP * F(Q) ** 2 - ivfr(L[0], L[1]) - F(13) / (4 * KAP * F(1 + p * 13) ** 2)
    rows.append(('>=13', 'any (Q(13))', q13))
    return rows


def check_delta0(rows, delta0):
    """The acceptance test of prop:bg-gap: every lower bound is >= delta0 (decided on interval endpoints).
    Returns (accepted, list of failing rows)."""
    D = F(delta0)
    fails = [(c, arg, v) for c, arg, v in rows if not v.a >= D]
    return (not fails), fails


if __name__ == "__main__":
    t0 = time.time()
    rows = gap_rows()
    print("prop:bg-gap, lower bounds by child count c (section B of bg_rate/certify.py):")
    for c, arg, v in rows:
        print(f"   c={c}: in [{float(v.a):.7f}, {float(v.b):.7f}]  (at {arg})")
    cmin, argmin, vmin = min(rows, key=lambda t: t[2].a)
    print(f"   minimum: c={cmin}, a={argmin}, enclosure [{float(vmin.a):.9f}, {float(vmin.b):.9f}]")
    ok = True
    print("\n[control 1] Proposition prop:bg-gap: delta_0 accepted iff every lower bound >= delta_0")
    for label, d0, want in (("unperturbed", Fr(1426, 100000), True), ("perturbed  ", Fr(143, 10000), False)):
        acc, fails = check_delta0(rows, d0)
        verdict = "PASS" if acc else "FAIL"
        extra = "" if acc else "  failing rows: " + ", ".join(f"c={c} ({arg}): {float(v.a):.6f} < {float(d0)}"
                                                              for c, arg, v in fails)
        good = acc == want
        ok &= good
        print(f"   {label} delta_0 = {float(d0):.5f}: {verdict} (expected {'PASS' if want else 'FAIL'}){extra}")
    # the failing row is decisive: the enclosure of the minimizing configuration lies entirely below 0.0143
    below = vmin.b < F(Fr(143, 10000))
    print(f"   the enclosure at c={cmin}, a={argmin} lies below 0.0143: {below}")
    ok &= below
    print(f"\nruntime {time.time() - t0:.1f} s")
    print("ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED" if ok else "SOME NEGATIVE CONTROL DID NOT BEHAVE AS EXPECTED")
    sys.exit(0 if ok else 1)
