# lam_partB_rows/second_implementation: the 63 rows, P2 and P9 recomputed separately

**Paper item:** Lemma `lem:lam-polycert` (scalar conditions of part (B), computer-verified), parts (a)-(c), and
the monotonicity facts of table `tab:lam-atoms`; item C14 of the appendix on computations. Role: second
implementation of the checks done by `../lowdeg_tables.py`, `../bernstein.py`, `../polychecks.py` and
`../w2_poly.py`.

Both programs were written separately from the programs of `..`, from the statements: own atom enclosures,
own interval class, own transcription of the conditions. `rows_arb.py` reads the files `../lowdeg_tables.out`
(boxes and claimed lower bounds) and `../lowdeg_atoms.out` (tabulated atom values) only to compare with them.

Name dictionary (the programs use the older names that are also printed by `../lowdeg_tables.py`): C1, C2, C3,
C7, C8, C9, C10 = P1, P2, P3, P7, P8, P9, P10; C10 T1, ..., T8, T8b = P10 (U1), ..., (U8), (U8b); C4-C6 = P4-P6;
W* = W_1.

## What is checked

`rows_arb.py` (python-flint/Arb, 256 bits, for every point value; a hand-written interval class whose endpoints
are exact Arb points and whose operations take min/max over the rigorous endpoint balls):

- every one of the 63 rows of `../lowdeg_tables.out` (P1: 10, P3: 13, P7: 17, P8: 1, P10: 22): each atom is
  enclosed by its values at the two box ends, in the direction of its monotonicity, and the condition is bounded
  below; the lower bound must be positive, and is compared with the claimed one; the value of the condition at
  the box midpoint and the ratio "lower bound / midpoint value" (the 30% rule) are printed;
- coverage: the boxes of each certificate start and end at the stated range ends ([0, 6181/10000] for P1, P3;
  [3/43, 3229/10000] for P7; [1/2, 6181/10000] for P8; [0, 3/43] for each condition of P10) and consecutive boxes
  share their endpoints exactly (rational equality), so there are no gaps;
- the atom table `../lowdeg_atoms.out` against its own atom values.

`exact_checks.py` (exact rationals and sympy, Arb for two evaluations):

- P2: the polynomial P(t) is re-derived from (S3), its 7 Bernstein coefficients on [0, 6181/10000] are computed in
  exact rationals (own routine) and are positive (15, 9.5916, 4.6767, 1.4264, 0.8118, 2.3839, 1.5207);
- P4-P6 Bernstein coefficients; the identity e^{6 Dmax} = (4/3)^6 (2/3)^3 = 32768/19683 < 1.291^2;
- P9: G_3(3/43) = -0.0065184030... < 0 (Arb), and f_2, f_3, f_4, f_5 at lambda = 3/20;
- the monotonicity of every atom and helper of table `tab:lam-atoms`: exact derivative identities
  (kappa/t, delta_kappa/t, r-hat, Theta, kappa y_4, varkappa), the G_2 series coefficients c_k (exactly positive
  for k <= 400, with the bounds 7(2/3)^5 < 0.93 and 5(3/4)^6 < 0.9 used for larger k), and a floating-point
  derivative scan of each atom. For xi(s) = (e^s - 1)/s the scan reports `False`: near s = 1e-9 the derivative
  is evaluated with catastrophic cancellation; the monotonicity of xi rests on its power series
  sum s^k/(k+1)!, which has positive coefficients, as stated in the table. The scan is not a proof for any atom.

## How to run

From this directory, inside `computations/lam_partB_rows/`:

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 rows_arb.py
python3 exact_checks.py
```

## Expected output

`expected_output.txt`. Key lines:

    rows recomputed: 63; all lower bounds positive: True
    lowdeg_atoms.out: max |tabulated - recomputed| over all breakpoints, 7 atoms = 4.93e-12
    C2: Bernstein coeffs on [0,6181/10000]: ['15.0000', '9.5916', '4.6767', '1.4264', '0.8118', '2.3839', '1.5207']  all >0: True  min 0.8118
    C9: G3(3/43) = [-0.00651840301554908 +/- 1.59e-18]  <0: True ; t(3/20) == 3/43: True

No row is marked `**FAIL**`: every row keeps at least 30% of its midpoint value. The smallest ratios are 0.300
(rows of P1 and P3); among the 22 rows of P10 the smallest is 0.331 ((U5) on [0, 3/172]). Every recomputed lower
bound agrees with the claimed one to the printed digits, except the three rows of (U4), where this program
encloses kappa y_4 as one monotone atom (the first program multiplies t, kappa/t and y_4) and so gets slightly
larger lower bounds: 0.0088024, 0.015341, 0.0165096 against 0.008796, 0.01533, 0.01646.

## Runtime and memory (measured here, one core)

`rows_arb.py` under 0.1 s, 19 MB; `exact_checks.py` 2.5 s, 61 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, python-flint 0.6.0, sympy 1.14.0, mpmath 1.3.0). The output of
`exact_checks.py` is identical to that of the original run, and every row line of `rows_arb.py` is
identical to the original runs of this code on the same boxes.

## Dependencies

Python 3.9 or later, `python-flint`, `sympy`, `mpmath`.
