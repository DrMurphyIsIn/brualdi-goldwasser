"""Negative control for Lemma lem:bg-compare(i): the comparison must fail at n = n-bar(k) - 1 for k = 9, 10.

The check is the per-k loop of ../conc.py (its __main__ block, repeated here verbatim as a function, with
`gamma`, `Psi`, `PsiB`, `tail_lb`, `phistar_lo` imported unchanged from ../conc.py): it builds the list of
candidate upper bounds for V_k(n) (with the minimal size N at which each is feasible) and, for each n,
compares V - eta_{k-1}(n - 1) with the lower bound Lambda_sp(n) of the table spider, on interval endpoints.
The comparison at n succeeds iff the upper end of V - eta (n - 1) is < Lambda_sp(n).

Positive control: for k = 9 and k = 10 the comparison succeeds for every n with n-bar(k) = 108 <= n <= 315.
Negative control: it fails at n = n-bar(k) - 1 = 107.

Usage: python3 nc_spider_comparison.py
"""
import os
import sys
import time
from pathlib import Path

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from mpmath import iv
import conc                      # reads ../certify_out.json (the certified rates)
from conc import gamma, Psi, PsiB, tail_lb, phistar_lo, ETA, F

NBAR = {9: 108, 10: 108}         # table tab:bg-rate


def comparison(k):
    """The loop of ../conc.py for one k. Returns {n: (upper end of V - eta (n-1), Lambda_sp(n) lower end)}
    for 7 <= n <= 315 (n with no feasible candidate omitted), and the minimizing shape of gamma."""
    MINQ = 4
    gm, arg = gamma(k - 1)
    eta = ETA[k - 1]
    P = Psi(k)
    cands = []
    cands.append(((iv.mpf(P) - tail_lb(19, eta) - gm.a).b, MINQ))
    jn = 1
    while jn <= k:
        if (iv.mpf(P) - jn * gm.a).b <= min(c[0] for c in cands):
            break
        _, _, lst = PsiB(k, jn=jn)
        for v, size, cf in lst:
            cands.append(((iv.mpf(v) - jn * gm.a).b, size + jn * MINQ))
        jn += 1
    cands.append(((iv.mpf(P) - jn * gm.a).b, jn * MINQ))
    out = {}
    for n in range(7, 316):
        N = n - 1
        if not any(c[1] <= N for c in cands):
            continue
        V = max(c[0] for c in cands if c[1] <= N)
        out[n] = ((iv.mpf(V) - F(eta) * N).b, phistar_lo(n))
    return out, arg


if __name__ == "__main__":
    t0 = time.time()
    def _f(x):
        """Display value of an interval (midpoint) or a number."""
        return float(x.mid) if hasattr(x, "mid") else float(x)

    ok = True
    print("[control 4] Lemma lem:bg-compare(i): V_k(n) - eta_{k-1}(n-1) < Lambda_sp(n)")
    for k in (9, 10):
        t1 = time.time()
        res, arg = comparison(k)
        nb = NBAR[k]
        unpert = all(res[n][0] < res[n][1] for n in range(nb, 316))
        worst = min(range(nb, 316), key=lambda n: res[n][1] - res[n][0])
        ub, lam = res[nb - 1]
        pert = ub < lam
        bad = [n for n in res if not res[n][0] < res[n][1]]
        print(f"   k = {k} (eta = {ETA[k - 1]}, gamma shape {arg}), {time.time() - t1:.0f} s:")
        print(f"      unperturbed: all n in [{nb}, 315]: {'PASS' if unpert else 'FAIL'} (expected PASS); "
              f"at n = {nb}: {_f(res[nb][0]):.7f} < {_f(res[nb][1]):.7f}; smallest margin {_f(res[worst][1] - res[worst][0]):.3e} at n = {worst}")
        print(f"      perturbed:   n = {nb - 1}: {_f(ub):.7f} < {_f(lam):.7f} is {pert}: {'PASS' if pert else 'FAIL'} "
              f"(expected FAIL; margin {_f(lam - ub):.3e})")
        print(f"      largest failing n = {max(bad)} (so n-bar(k) = {max(bad) + 1})")
        ok &= unpert and not pert and max(bad) + 1 == nb
    print(f"\nruntime {time.time() - t0:.1f} s")
    print("ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED" if ok else "SOME NEGATIVE CONTROL DID NOT BEHAVE AS EXPECTED")
    sys.exit(0 if ok else 1)
