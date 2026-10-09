# bg_nonatom_gap/negative_controls: the non-atom gap must reject delta_0 = 0.0143

**What it checks:** the check of the non-atom gap at lambda = 1, with delta_0 = 0.01426.
Role: negative control (a deliberately wrong input that the check must reject); no proof uses it.

## What is checked

`nc_nonatom_gap.py` re-runs the check of the gap, section B of `../../bg_rate/certify.py`, with
the same routines (`ivtools.py` and `core.py` of `../../bg_rate/`, imported unchanged; `mpmath.iv`,
120 bits, outward rounding): for each child count c of a minimal non-atom it computes the rigorous lower
bound of sigma_v + sum sigma(children) (c = 1: Phi_1(3/7); 2 <= c <= 9: m_c + min_a (w_c(y_a) + sigma(a))
over a in {leaf, A_1, ..., A_30} and the tail A_{>30}; c = 10, 11, 12: branch-and-bound of min Phi_c on
[0, c]; c >= 13: Q(13)). A value delta_0 is accepted iff every one of these bounds is >= delta_0, decided
on interval endpoints.

- Positive control: delta_0 = 0.01426 (the stated value) is accepted.
- Negative control: delta_0 = 0.0143 is rejected. The failing row is c = 6, a = A_4, whose enclosure
  [0.014273396, 0.014273396] lies entirely below 0.0143; no other row fails.

The rejection is a rejection of the method, not of the statement: the true infimum over non-atoms is
about 0.014465, so "sigma(b) >= 0.0143 per minimal non-atom" may well be
true; the per-child bound m_c + w_c(y) + sigma(a) used by the proof cannot certify it, and the control
shows that the check notices.

## How to run

From this directory, in the layout `computations/bg_nonatom_gap/negative_controls/` (the script imports
from `../../bg_rate/`):

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 nc_nonatom_gap.py
```

## Expected output

`expected_output.txt`: the thirteen lower bounds (the same values as section B of
`../../bg_rate/expected_output.txt`), then

    unperturbed delta_0 = 0.01426: PASS (expected PASS)
    perturbed   delta_0 = 0.01430: FAIL (expected FAIL)  failing rows: c=6 (A4): 0.014273 < 0.0143

ending with `ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED` (exit code 0).

## Runtime and memory (measured here, one core)

About 4 s, 19 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, mpmath 1.3.0).

## Dependencies

Python 3.9 or later, `mpmath` (>= 1.3); the files `ivtools.py`, `core.py` of `../../bg_rate/`.
