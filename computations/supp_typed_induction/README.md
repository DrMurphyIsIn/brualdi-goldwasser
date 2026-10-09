# supp_typed_induction -- typed induction on (0, 0.1]

**What this is:** the typed induction for the sharp ceiling at small activities, lambda in `(0, 0.1]`,
with its program, independent check and controls. Role: part of a proof in a confirmation route (the
typed-induction route to part (B) on `(0, 0.1]`, a confirmation of part (B), which is proved by the
witnesses W_1, W_2).

## What is checked

`certify_small.py` runs the checks (T1)-(T3) of the lemma, with `d_0 = 240`, `gamma_inf = 9/1000`,
`delta = 6/1000` and `gamma_2, ..., gamma_240` from the first-order value iteration, on 200 contiguous
`lambda`-boxes of width 1/2000 covering `[0, 0.1]`, in five chunks of 40 boxes. All quantities are scaled by
`1/lambda`, so the first box contains `lambda = 0`. Every `lambda`-dependent quantity is enclosed outward in
`mpmath.iv` (30 digits); the arithmetic is described exactly in the accompanying paper.

* (T1) parents of degree `d = 2..5`: enumeration over the Pareto front of child types;
* (T2) `6 <= d <= 240`: tangent of the concave `log(1 + lambda S/d)/lambda` (separable);
* (T3) `d > 240`: analytic tail.

Two companion checks:

* `small_spider_strict.py`: on every box, the unclipped enclosure of `g(A_j)/lambda` is positive (exceeds
  `0.0057`) for every arm except `A_3`, so the clip at 0 is active only at `A_3`.
* `small_hyp_check.py`: the typed hypothesis on all 53 272 planted branches with at most 14 vertices, by
  exact cavity values (double precision) at `lambda in {0.001, 0.02, 0.05, 0.1}`. It uses the tree
  enumerator and helper functions of `small_lambda_monotone.py`, `monotone_ratio.py` and `exp1_ceiling.py`
  (loaded by `exec` of their leading parts; keep the files together and run from this folder).

## How to run

    sh run_all.sh

(or one chunk: `python3 certify_small.py LAM1 0.0005 0.006 LAM0`, e.g. `python3 certify_small.py 0.02 0.0005 0.006 0`).

## Expected output

See `expected_output.txt`:

* five lines `lam in [a, b] ... CERTIFIED; 40 boxes` covering `[0, 0.1]` (200 boxes, no bisection);
* `max over boxes and spiders e != 4 of the unclipped l(S_e)/lam upper bound: -0.0057263...` at `(3, 0.0)`,
  i.e. at `A_2` on the first box (the spider with root degree `e` is the arm `A_{e-1}`);
* `53272 branches` at each of the four activities, with `max over GEN of (l/lam - g_e)` between `-0.00600`
  and `-0.00612` (margin about `delta = 0.006`), as stated in the accompanying paper.

## Runtime (single thread, one core)

About 49 s per chunk (paper: about 49 s), 248 s for `run_all.sh` in total; 23 MB.

## Dependencies

Python 3.9+, `mpmath`.
