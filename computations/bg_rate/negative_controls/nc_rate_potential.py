"""Negative control for Lemma lem:bg-rate (rate potential) at the exact zero (c, S) = (1, 1).

For the cap K = 1 the lemma needs Phi~_1(S) >= 0 on [0, 1], where Phi~_1(1) = 0 exactly for every eta.
The check (../certify.py, section D, with ../ivtools.py; and ../../bg_rate_zeros/rate_zeros.py, part [C])
closes the box at S = 1 by a one-sided derivative: the enclosure of Phi~_1' on [S_-, 1] must be <= 0.
This holds iff (10/9)(gamma + (3/2) eta) < 1/3, i.e. eta < (3/10 - gamma)/(3/2) = 0.00112107...; the table
uses eta_1 = 2791/2500000 = 0.0011164. For eta slightly above 0.0011211 the check must fail.

Positive control: eta = 2791/2500000 (and, for (a) and (c) only, eta = 0.0011210, just below the cap; there
the single-box test (b) is too coarse, since the derivative margin is only 1.2e-7, and the branch-and-bound
would subdivide the box).
Negative control: eta = 0.0011212.

For each eta this script runs, with the routines of ../ivtools.py and ../../bg_rate_zeros/rate_zeros.py
imported unchanged:
  (a) the convexity condition of the lemma, eta (621/14 - 3/2) <= gamma - s (it does not depend on (1, 1)
      and passes for all these eta; listed so that the failure below is attributed to (1, 1));
  (b) the local step of ivtools.bb_min_ge0 on the box [1 - 2^-14, 1] that the branch-and-bound on [0, 1]
      reaches (the first box at S = 1 of width < 10^-4): derivative enclosure upper end <= 0;
  (c) the local step with the exact endpoint of rate_zeros.py [C]: max of the derivative enclosure over
      64 sub-boxes of [1 - 10^-4, 1] is <= 0, in mpmath.iv and in Arb;
  (d) the full branch-and-bound ivtools.bb_min_ge0 for Phi~_1 >= 0 on [0, 1] (as in ../certify.py). For
      the perturbed eta it is stopped after as many function evaluations as the unperturbed run needed to
      certify, and reported as not certified; in addition
  (e) a refutation: an interval enclosure of Phi~_1(1 - 10^-6) that lies below 0. Then the inequality is
      false, so no (sound) branch-and-bound can certify it at any depth.

Usage: python3 nc_rate_potential.py
"""
import os
import sys
import time
from pathlib import Path

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "bg_rate_zeros"))
sys.path.insert(0, str(HERE.parent))

from fractions import Fraction as Fr
import rate_zeros as RZ           # sets mpmath.iv precision to 256 bits on import
from mpmath import iv, mpf
import ivtools as IVT             # resets it to 120 bits, as in ../certify.py
from ivtools import F, AWI, GAM, KAP, THIRD, QI, PhiH_iv, dPhiH_iv, bb_min_ge0

ETA_TABLE = Fr(2791, 2500000)
ETA_BELOW = Fr(11210, 10 ** 7)
ETA_PERT = Fr(11212, 10 ** 7)


class Budget(Exception):
    pass


def convexity_ok(eta):
    return (F(eta) * (AWI - F(Fr(3, 2)))).b <= (GAM - 2 * KAP * (THIRD - QI)).a


def local_bb_box(eta):
    """the test of bb_min_ge0 at the eq point 1 on the box [1 - 2^-14, 1] (deriv as in certify.py, c = 1)"""
    lo = mpf(1) - mpf(2) ** -14
    d = dPhiH_iv(1, iv.mpf([lo, mpf(1)]), eta, 'L')
    return d.b <= 0, d.b


def local_exact(eta):
    """rate_zeros.py [C] at (1, 1), both arithmetics: max of Phi~_1' over [1 - 1e-4, 1] must be <= 0"""
    out = []
    W = Fr(1, 10 ** 4)
    for B in (RZ.Iv, RZ.Ab):
        _, _, _, gamma, _, _ = RZ.constants(B)
        m = RZ.sub_max(B, lambda X: RZ.deriv1(B, gamma, eta, X), 1 - W, Fr(1))
        out.append((B.name, m <= 0, m))
    return out


def full_bb(eta, budget=None):
    """bb_min_ge0 for Phi~_1 >= 0 on [0, 1] with the eq point 1, exactly as in certify.py section D.
    Returns (result, number of function evaluations); result None = stopped by the budget."""
    n = [0]

    def f(X):
        n[0] += 1
        if budget is not None and n[0] > budget:
            raise Budget
        return PhiH_iv(1, X, eta)

    def deriv(I, side):
        return dPhiH_iv(1, I, eta, 'L')

    try:
        res = bb_min_ge0(f, mpf(0), mpf(1), (mpf(1),), deriv)
    except Budget:
        res = None
    return res, n[0]


def witness(eta):
    v = PhiH_iv(1, F(1 - Fr(1, 10 ** 6)), eta)
    return v.b < 0, v


if __name__ == "__main__":
    t0 = time.time()
    cap = (F(Fr(3, 10)) - GAM) / F(Fr(3, 2))
    print(f"cap (3/10 - gamma)/(3/2) in [{float(cap.a):.12f}, {float(cap.b):.12f}]")
    ok = True
    print("\n[control 2] Lemma lem:bg-rate at (c, S) = (1, 1), cap K = 1")
    results = {}
    for label, eta in (("unperturbed", ETA_TABLE), ("near cap   ", ETA_BELOW), ("perturbed  ", ETA_PERT)):
        cv = convexity_ok(eta)
        lb, lbv = local_bb_box(eta)
        le = local_exact(eta)
        dPhi1 = dPhiH_iv(1, F(1), eta, 'L')
        print(f"   {label} eta = {eta} = {float(eta):.7f}:  Phi~_1'(1) in [{float(dPhi1.a):.4e}, {float(dPhi1.b):.4e}]")
        print(f"      (a) convexity condition: {'PASS' if cv else 'FAIL'}")
        print(f"      (b) bb_min_ge0 local step on [1 - 2^-14, 1]: derivative <= {float(lbv):.4e}: {'PASS' if lb else 'FAIL'}"
              + ("  (single box, not used here)" if eta == ETA_BELOW else ""))
        for name, okk, m in le:
            print(f"      (c) rate_zeros [C] on [1 - 1e-4, 1], {name}: max derivative <= {float(m):.4e}: {'PASS' if okk else 'FAIL'}")
        results[label] = (cv, lb, all(x[1] for x in le))
    # (d), (e)
    t1 = time.time()
    r0, n0 = full_bb(ETA_TABLE)
    print(f"   unperturbed (d) full branch-and-bound on [0, 1]: {'certified' if r0 else 'NOT certified'} "
          f"({n0} evaluations, {time.time() - t1:.1f} s)")
    t1 = time.time()
    r1, n1 = full_bb(ETA_PERT, budget=n0)
    print(f"   perturbed   (d) full branch-and-bound on [0, 1]: "
          f"{'certified' if r1 else ('NOT certified (returned False)' if r1 is False else 'NOT certified within the same number of evaluations')}"
          f" ({min(n1, n0)} evaluations, {time.time() - t1:.1f} s)")
    w0, v0 = witness(ETA_TABLE)
    w1, v1 = witness(ETA_PERT)
    print(f"   unperturbed (e) Phi~_1(1 - 1e-6) in [{float(v0.a):.4e}, {float(v0.b):.4e}]")
    print(f"   perturbed   (e) Phi~_1(1 - 1e-6) in [{float(v1.a):.4e}, {float(v1.b):.4e}]: "
          f"{'refuted (enclosure below 0)' if w1 else 'not refuted'}")

    cvT, lbT, leT = results["unperturbed"]
    cvB, lbB, leB = results["near cap   "]
    cvP, lbP, leP = results["perturbed  "]
    unpert_pass = cvT and lbT and leT and r0 is True and not w0
    near_pass = cvB and leB    # (b) is a single box; at this small margin the B&B would subdivide it
    pert_pass = cvP and lbP and leP and r1 is True
    print(f"\n   unperturbed eta = 0.0011164: check {'PASS' if unpert_pass else 'FAIL'} (expected PASS)")
    print(f"   near cap    eta = 0.0011210: convexity and local step (c) {'PASS' if near_pass else 'FAIL'} (expected PASS)")
    print(f"   perturbed   eta = 0.0011212: check {'PASS' if pert_pass else 'FAIL'} (expected FAIL); "
          f"local steps fail: {not lbP and not leP}; refuted: {w1}")
    ok = unpert_pass and near_pass and (not pert_pass) and (not lbP) and (not leP) and w1 and cvP
    print(f"\nruntime {time.time() - t0:.1f} s")
    print("ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED" if ok else "SOME NEGATIVE CONTROL DID NOT BEHAVE AS EXPECTED")
    sys.exit(0 if ok else 1)
