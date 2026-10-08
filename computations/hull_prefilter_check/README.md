# hull_prefilter_check: re-check of the floating-point prefilters of the two hull searches

**Paper items:** Theorem `thm:bg-small` (the paragraph "Exact arithmetic" in the section on the exact
hull computation; program `../bg_hull_dp/dp.py`) and Lemma `lem:nu-small-cv` with Appendix C, item C16
(program `../nu_hull_search/hulldp2.py`). Role: part of the proof (it certifies the one floating-point step
of each search).

## The point

Both hull searches generate, for each class, a set C of candidate points in exact rational arithmetic,
discard some of them with a floating-point prefilter, and compute Ext of the survivors C' exactly. This is
correct as soon as no discarded point lies in Ext(C), i.e. every discarded p satisfies
a . p < max over C' of a . x for every a > 0. For `dp.py` the paper proves this from the test itself (an
explicit rounding-error bound). `hulldp2.py` uses a different filter (a Pareto test and a cross-product
test with absolute tolerances) which is not by itself such a proof: a point whose first coordinate ties
another one in floating point, but is truly larger, could in principle be an Ext point. This folder checks
the property directly, class by class, for the full runs.

## What is checked

- `certify_drop.py` (the certifier). For each discarded p: (1) a domination test in double precision
  against the exact upper-right hull chain of the survivors: a float convex combination w~ of two
  consecutive chain points must exceed fl((1 + 2e-12) p~) in both coordinates. With u = 2^-53 and
  gamma_k = k u/(1 - k u), and all quantities positive, the candidate coordinates are within gamma_4 of the
  truth, the computed combination is at most (1 + gamma_4) times the true one, and the right side at least
  (1 + 2e-12 - u)(1 - u)(1 - gamma_4) times the true coordinate; since 2e-12 > 10 u, the true convex
  combination dominates p strictly in both coordinates, so a . p < max over C' for every a > 0.
  (2) Where (1) is inconclusive (or produces NaN/inf), an exact test in rational arithmetic:
  g(t) = max over the chain of (x - p.x) + t (y - p.y) must be > 0 at every breakpoint t of the chain and in
  the limits t -> 0+ and t -> infinity.
- `recheck_bg.py` runs the recursion of `../bg_hull_dp/dp.py` (imports its functions unchanged), applies the
  certifier to every bundle class up to n = 491, and compares the exact M_n with
  `../bg_hull_dp/results_dp_491.txt`.
- `recheck_nu.py` does the same for `../nu_hull_search/hulldp2.py` (n <= 215, matching number <= 8) and
  compares M(n, k) with `../nu_hull_search/dpk215_8.txt`.
- `test_certify.py` tests the certifier on 3000 random exact point sets with many exactly collinear, nearly
  collinear and nearly tied points (Ext computed by brute force from its definition): every non-Ext point
  must be certified (positive control) and a deliberately discarded Ext point must never be (negative
  control).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 test_certify.py
python3 recheck_bg.py 491        # progress lines on stderr
python3 recheck_nu.py 215 8      # progress lines on stderr
```

## Expected output

`expected_output.txt` (the three runs, stdout). Key lines:

    positive control: 42357 discarded non-Ext points in 3000 random sets, 42357 certified (1627 of them by the exact test)
    negative control: 2643 sets with one Ext point wrongly discarded, 2643 caught
    bg_hull_dp prefilter re-check, n <= 491
      candidates 355891085, discarded by the prefilter 355203177: certified by the float test 355203177, by the exact test 0, NOT certified 0
      exact M_n equal to results_dp_491.txt for 2 <= n <= 491: True
    nu_hull_search prefilter re-check, n <= 215, KMAX = 8
      candidates 2463178108, discarded by the prefilter 2457099678: certified by the float test 2457099678, by the exact test 0, NOT certified 0
      exact M(n, k) equal to dpk215_8.txt on all 1854 pairs computed: True

## Runtime and memory (measured here, one core)

| run | time | peak memory |
|---|---|---|
| `test_certify.py` | 53 s | 31 MB |
| `recheck_bg.py 491` | 163 s | 0.57 GB |
| `recheck_nu.py 215 8` | 1105 s | 2.9 GB |

## Re-run status

PASS: no discarded candidate lies in Ext of its class, in either search; the exact maxima agree with the
stored outputs of the original programs.

## Dependencies

Python 3.9 or later, `numpy`; `networkx` is not needed (the tree output of the original programs is not
recomputed).
