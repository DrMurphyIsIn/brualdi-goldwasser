# bg_rate_zeros: the two exact zeros of the rate lemma

**Paper item:** Lemma `lem:bg-rate` (rate potential), the paragraph on the two points (c, S) = (5, 5/3) and
(1, 1) where Phi~_c vanishes, and Appendix C, item C4. Role: part of the proof (it supplies, with
exact endpoints, the local step of the branch-and-bound of `../bg_rate/certify.py`, and certifies the
numbers quoted in the lemma).

## What is checked

`rate_zeros.py`:

- **[A] symbolic (sympy).** With h~ = h - eta z, the one-sided derivatives of Phi~_5 at S = 5/3 are
  D^- = s + (621/14) eta (1 + q^2) - q and D^+ = gamma + (3/2) eta + (621/14) eta q^2 - q (s = 2 kappa (1/3 - q));
  Phi~_5(5/3) = 0 and Phi~_1(1) = 0 exactly for every eta (from F* + 5 beta = log(23/18),
  2F* - log(3/2) = beta, 1 + z(1) = z(1/3) and 1 + 5 z(1/3) = z(q)); on [1/3, 1],
  Phi~_1'(S) = (gamma + 3/2 eta)(1 + r^2) - r with r = 1/(2+S).
- **[B] the numbers quoted in the lemma**, for each of the 22 rates eta_K of table `tab:bg-rate` (which
  are compared with `../bg_rate/certify_out.json`), in `mpmath.iv` (256 bits) and Arb (300 bits):
  -0.041 < D^- < -0.004 (range [-0.040636, -0.004100]); D^+ rounds to 0.17 (range [0.168575, 0.170401]);
  (10/9)(gamma + 3/2 eta_K) - 1/3 < 0 for every K, equal to -7.789e-6 for K <= 5; the cap
  (3/10 - gamma)/(3/2) = 0.0011210... above 2791/2500000.
- **[C] the local argument with exact endpoints.** For every K >= 5 the derivative of Phi~_5, enclosed on
  64 sub-boxes, is <= 0 on [5/3 - 10^-4, 5/3] (pieces S/5 <= 1/3 and r <= 1/3) and >= 0 on
  [5/3, 5/3 + 10^-4] (pieces S/5 >= 1/3 and r <= 1/3); for every K the derivative of Phi~_1 is <= 0 on
  [1 - 10^-4, 1] (pieces S >= 1/3, r >= 1/3). The endpoints 5/3 and 1 enter as exact rationals. So
  Phi~_c >= Phi~_c(S_0) = 0 on every box of width <= 10^-4 containing the zero S_0.

**Why [C].** In `../bg_rate/certify.py` the branch-and-bound splits at a 50-digit floating-point value
of 5/3 (it exceeds 5/3 by about 9e-52) and applies the derivative of the left piece up to that value. On
the sliver between 5/3 and that value the left-piece derivative is not the derivative of Phi~_5. The
conclusion is unaffected (the second implementation in `../bg_rate/second_implementation/` encloses 5/3
as an interval), and [C] gives the local step with the exact endpoint, independently of how the
branch-and-bound places its boxes, as long as the boxes at the zero have width at most 10^-4 (the
tolerance `tol` of `ivtools.bb_min_ge0`).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 rate_zeros.py
```

It reads `../bg_rate/certify_out.json` if present (only to compare the rates).

## Expected output

`expected_output.txt`, ending with `ALL CHECKS PASSED`.

## Runtime and memory (measured here, one core)

About 1 s, 59 MB.

## Re-run status

PASS (Python 3.9.6, sympy 1.14.0, mpmath 1.3.0, python-flint 0.6.0).

## Dependencies

Python 3.9 or later, `sympy`, `mpmath`, `python-flint`.
