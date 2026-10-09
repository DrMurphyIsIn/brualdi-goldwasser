# bg_rate/negative_controls: the rate lemma at (1, 1) must reject a rate above the cap

**What it checks:** the check of the rate potential at lambda = 1 at the exact zero (c, S) = (1, 1) for the
cap K = 1, where every admissible rate satisfies eta <= 0.0011210...
Role: negative control (a deliberately wrong input that the check must reject); no proof uses it.

## What is checked

For K = 1 the rate potential needs Phi~_1(S) >= 0 on [0, 1]. Since Phi~_1(1) = 0 for every eta, the check closes the
box at S = 1 by a one-sided derivative, which must be <= 0 there; this holds iff
(10/9)(gamma + (3/2) eta) < 1/3, i.e. eta < (3/10 - gamma)/(3/2) = 0.001121073580... The table uses
eta_1 = 2791/2500000 = 0.0011164. The negative control uses eta = 0.0011212, slightly above 0.0011211.

`nc_rate_potential.py` imports, unchanged, `../ivtools.py` (the routines of `../certify.py`, section D) and
`../../bg_rate_zeros/rate_zeros.py` (the exact-endpoint local step, part [C]), and runs for each eta:

- (a) the convexity condition eta (621/14 - 3/2) <= gamma - s (it does not involve (1, 1); it passes for
  every eta here, so the failure is attributed to (1, 1));
- (b) the local step of `ivtools.bb_min_ge0` on the box [1 - 2^-14, 1] that the branch-and-bound on [0, 1]
  reaches: the derivative enclosure must be <= 0;
- (c) the local step of `rate_zeros.py` [C] with the exact endpoint 1: the derivative over 64 sub-boxes of
  [1 - 10^-4, 1] must be <= 0, in `mpmath.iv` (256 bits) and in Arb (300 bits);
- (d) the full branch-and-bound `bb_min_ge0` for Phi~_1 >= 0 on [0, 1], exactly as in `../certify.py`.
  For the perturbed eta it is stopped after as many function evaluations as the unperturbed run needed
  (164,893), and reported as not certified. Run to the end it would not return quickly: Phi~_1 is
  positive but of size about 10^-10 just left of the zero, and value enclosures need very small boxes;
- (e) a refutation: the enclosure of Phi~_1(1 - 10^-6). For the perturbed eta it lies below 0, so the
  inequality is false and no sound branch-and-bound can certify it, at any depth.

Results:

| eta | Phi~_1'(1) | (a) | (b) | (c) | (d) | (e) Phi~_1(1 - 10^-6) | check |
|---|---|---|---|---|---|---|---|
| 2791/2500000 = 0.0011164 (table) | -7.79e-6 | PASS | PASS (<= -6.43e-6) | PASS (<= -7.75e-6) | certified | +7.83e-12 | PASS |
| 0.0011210 (just below the cap) | -1.23e-7 | PASS | (single box too coarse; not used) | PASS (<= -8.79e-8) | not run | | PASS (a), (c) |
| 0.0011212 (perturbed) | +2.11e-7 | PASS | FAIL (<= +1.57e-6) | FAIL (<= +2.45e-7) | not certified | -1.66e-13 (refuted) | FAIL |

## How to run

From this directory, in the layout `computations/bg_rate/negative_controls/` (the script imports from
`../` and `../../bg_rate_zeros/`):

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 nc_rate_potential.py
```

## Expected output

`expected_output.txt`, ending with

    unperturbed eta = 0.0011164: check PASS (expected PASS)
    near cap    eta = 0.0011210: convexity and local step (c) PASS (expected PASS)
    perturbed   eta = 0.0011212: check FAIL (expected FAIL); local steps fail: True; refuted: True
    ...
    ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED

(exit code 0). The two lines of (d) also print their own wall-clock times, which vary from run to run.

## Runtime and memory (measured here, one core)

About 46 s (23 s for each of the two runs of (d)), 54 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, mpmath 1.3.0, sympy 1.14.0, python-flint 0.6.0).

## Dependencies

Python 3.9 or later, `mpmath` (>= 1.3), `sympy` and `python-flint` (>= 0.6; needed by `rate_zeros.py`);
the files `ivtools.py`, `core.py` of `../` and `rate_zeros.py` of `../../bg_rate_zeros/`.
