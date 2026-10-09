# supp_window: interval confirmation of the window checks on [3.22, 1+sqrt5)

**What this is.** An interval-arithmetic confirmation of the window checks: the sharp ceiling for lambda in
[3.22, 1+sqrt5), uniformly as lambda -> 1+sqrt5.

**Role.** Confirmation only. The window checks (C2)-(C4) are proved by hand, with the
single numerical input e^0.4796 <= 1.6155; this program is not used in any proof.

## What is checked

With eta = lambda_c - lambda, lambda_c = 1 + sqrt5, the program splits eta in [0, lambda_c - 3.22] into
boxes of width 5e-4 and works in `mpmath.iv` at 30 digits. On each box it encloses the mean-value factors
omega_1, omega_2 on the hull [lambda_c - eta_1, lambda_c], cancels the powers of eta, and checks

- "(C1)": 3 f_cherry - log(1 + 2 lambda/3) >= eps^+ and 2 log(1 + lambda/2) - log(1 + lambda) >= eps^+
  (stronger than the hand proof needs);
- (C2): k = 0, 1 <= m <= 7, by bisection of ybar in [0, 1/2] (1 584 ybar-cells in all);
- (C3): single interval evaluations, with lambda*y_8 < kappa^- checked strictly (also y_8 <= ydag^-);
- (C4): single interval evaluations.

The program's docstring gives the enclosures and the checks in full. It prints `window checks (C1)-(C4): ...`.

## How to run

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 certify_L3.py 0.0005
```

The argument is the eta-box width (default 0.0005).

## Expected output

The last line must read
`window checks (C1)-(C4): ALL PASSED on delta in [0, 0.016068] (lam in [3.22, lam_c]); C2 boxes 1584; ...`
(see `expected_output.txt`). The accompanying text states 1 584 cells for (C2) and a run time under a second.

## Runtime and memory (measured here)

Measured here: 0.3 s, 16 MB. Re-run result: PASS (ALL PASSED; 1 584 C2 cells).

## Dependencies

Python 3.9 or later, `mpmath` (tested with 1.3.0).
