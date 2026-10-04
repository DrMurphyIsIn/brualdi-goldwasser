# lam_breakpoints -- breakpoint enclosures lambda_3, ..., lambda_6 (and up to lambda_30)

**Paper item:** Lemma `lem:lam-bp` (computer-verified) and Remark `rem:lam-bp`, in the section on the family
pi_lambda (the arm ladder). Role: part of a proof.

## What is checked

`f_j(lambda) = [ j log(1+lambda/2) + log(1 + lambda j y_c/(j+1)) ] / (2j+1)`, `y_c = 1/(2+lambda)`, is the
per-vertex log-weight of the arm `A_j`; `lambda_j` is the activity where `A_j` and `A_{j+1}` tie.

* `lemma_signs.py` -- the statement of the lemma: for
  `(j,p,q) = (3,0.43050,0.43051), (4,0.87247,0.87248), (5,1.19239,1.19240), (6,1.43559,1.43560)`
  it checks `f_{j+1}(p) < f_j(p)` and `f_{j+1}(q) > f_j(q)` in Arb ball arithmetic (python-flint, 256 bits) at
  the exact rational endpoints, and prints the smallest modulus (paper: `6.8e-12`).
  This short script was written for this release to check the lemma exactly as stated; the original Arb
  check of the endpoints was not preserved as a separate program.
* `breakpoints.py` (with `rates.py`) -- the remark: for `3 <= j <= 30` it encloses `lambda_j` to width
  `2e-18` by a sign change of `f_j - f_{j+1}` in `mpmath.iv` (outward rounding, 50 digits). The approximate
  breakpoint comes from a floating-point root finder (`rates.py`), which is untrusted; only the interval sign
  test certifies. By the single-crossing lemma there is exactly one sign change, so this encloses `lambda_j`.

## How to run

    python3 lemma_signs.py
    python3 breakpoints.py

## Expected output

See `expected_output.txt`. `lemma_signs.py` prints `OK` for all eight endpoint signs, smallest modulus
`6.83e-12` (at `j=6`, `p=1.43559`), and `ALL SIGNS VERIFIED`. `breakpoints.py` prints `VERIFIED` for every
`j = 3..30`, e.g. `lambda_3 = 0.43050185...`, `lambda_7 = 1.62691...`, `lambda_30 = 2.76856...`.

## Runtime (single thread, one core)

`lemma_signs.py` under 0.1 s, 17 MB; `breakpoints.py` 3.5 s, 17 MB.

## Dependencies

Python 3.9+, `mpmath` (1.3.0 tested), `python-flint` (0.6.0 tested).
