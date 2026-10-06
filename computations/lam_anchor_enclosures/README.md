# lam_anchor_enclosures: the constants of the anchor at lambda_c = 1 + sqrt 5

**Paper item:** Proposition `prop:lam-anchor` (the anchor; part (A) of `thm:lam-uniform`), the
enclosures `eq:lam-anchor-num` and every decimal in its proof. Role: part of the proof (numerical inputs
of a hand proof).

## What is checked

`anchor_enclosures.py`:

- **[A] exact identities (sympy):** the identities `eq:lam-anchor-id` (lambda_c = 2 phi,
  1 + lambda_c/2 = phi^2, 1 + lambda_c = phi^3, y_C = 1/(2 phi^2), lambda_c y_C = 1/phi, ...),
  2 phi^-2 = 3 - sqrt5, h(1/2) = f*/2, y_v(y_C) = phi^-2 and y_v(1/2) = 1/(2+phi) for m = 1,
  1 + lambda_c m y_C/(m+1) = (m phi + 1)/(m+1), the kink positions (1 + lambda_c - m)/(lambda_c m), the
  form of B_{0,1} in D = 2 + lambda_c ybar and its second derivative (D - 2 kappa)/D^3, and the
  derivative formula for B_{0,1}.
- **[B] every decimal**, from the exact expressions, in `mpmath.iv` (256 bits) and Arb (300 bits):
  log phi in [0.48121, 0.48122]; kappa in [0.77861, 0.77862]; 2 phi^-2 = 3 - sqrt5 in [0.76393, 0.76394];
  h(1) > 0.62; f* < 0.49; the k = 2 bound in [0.29389, 0.29390]; kappa < 1 (hence < 2 and D >= 2 > 2 kappa);
  kappa - 2 phi^-2 > 0.0146 (value 0.014685); the kink placements for m = 1..8 and m >= 5;
  log(3 phi^-2) in [0.13618, 0.13619], kappa(phi^-3 - phi^-2/2) in [0.03510, 0.03511], the m = 2 minimum in
  [0.10107, 0.10109] (0.1010847...); y_- in [0.32067, 0.32068], y_+ in [0.96365, 0.96366],
  1/(2+phi) in [0.27639, 0.27640], phi^-2 in [0.38196, 0.38197], their order, ybar* in [0.34562, 0.34563];
  at p = 216/625: both hinges active, B_{0,1}(p) in [0.056447, 0.056448] (0.0564478058...),
  B_{0,1}'(p) in [-1.3e-5, 0] (-1.25699e-5), p - y_C < 0.155, 1/2 - p < 0.155, and the tangent bound
  0.056447 - 0.155 * 1.3e-5 = 0.056444985 > 0.05644.
- **[C]** an interval branch-and-bound confirms min of B_{0,1} over [0, 1/2] > 0.05644 directly (both
  arithmetics).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 anchor_enclosures.py
```

## Expected output

`expected_output.txt`, ending with `ALL CHECKS PASSED`.

## Runtime and memory (measured here, one core)

About 1 s, 60 MB.

## Re-run status

PASS (Python 3.9.6, sympy 1.14.0, mpmath 1.3.0, python-flint 0.6.0). All values agree with the text.
See also `../supp_cherry_checks/lamc_hand_check.py`, which encloses a subset of these constants in Arb
(a confirmation for the supplement).

## Dependencies

Python 3.9 or later, `sympy`, `mpmath`, `python-flint`.
