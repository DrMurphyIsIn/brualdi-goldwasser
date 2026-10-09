# supp_highdeg: the high-degree certificates of part (B)

**Paper item.** Lemma `lem:lam-polycert-hd` ("High-degree certificates: an independent confirmation",
computer-verified; in the supplement from v21) and Remark `rem:lam-polycert-hd`. **Role: supplement proof route, a confirmation** of `lem:lam-polycert`
(the proof of part (B) does not use it); on [0.1282, 3/20] it also shows that W_1 is a witness there.

## What is checked

The same conditions P1-P10 as in `../lam_partB_rows/`, each written (through explicit Taylor bounds with
remainders of known sign) as the positivity of an explicit rational function of one variable with rational
coefficients, of degree up to 77. The shared routine `cert.py`:

1. writes the function exactly as P/Q over Q (sympy) and, when the interval starts at 0, removes the common
   power of the variable;
2. (i) counts the real roots of P and Q in the interval exactly (Sturm sequences over Q, `Poly.count_roots`)
   and checks the sign at the left end exactly; (ii) as a second check, encloses all complex roots of the
   integer polynomials in Arb ball arithmetic (python-flint) and checks that no enclosure meets the interval;
3. evaluates the function at 2001 points as a sanity check.

| program | certificates | paper |
|---|---|---|
| `polychecks.py` | P1 (S2, degree 13), P2 (S3, degree 9; and 1 - kappa y4 > 0), P3 (S4 in s = sqrt(1-t), degree 51, with the auxiliary facts on rhohat and Theta'), P4-P6 (S5), P8 (S6, lambda >= 2, degree 6); also the exact identity e^{6 Dmax} = 32768/19683 < 1.291^2 | Table `tab:lam-polycert-hd` |
| `s6_hand.py` | P7: (S6) at f* = f_3 on lambda in [0.1282, 0.9537] (t <= 0.3229, that is lambda <= 0.95377), Taylor order 5, numerator degree 77; also D(3) > 0 and u_3^hi > 0 (degrees 7, 24) | |
| `w2_poly.py` | P9: G_3(3/43) <= -0.0065183... < 0 by an exact rational upper bound; P10: the 28 statements (U1)-(U8), N^2_m and N^C_m for 5 <= m <= 13, on (0, 3/43] | |

Program output labels: T1, T2, T4, T5, T6 are (U1), (U2), (U4), (U5), (U6); the four `aux:` lines are the facts
of (U3); `T7: N2(m)` and `T8: NC(m)` are N^2_m and N^C_m.

## How to run

```
python3 polychecks.py
python3 s6_hand.py            # optional args: lambda_a (default 641/5000 = 0.1282) and Taylor order (default 5)
python3 w2_poly.py            # optional arg: Taylor order (default 5)
```

`s6_hand.py 641/5000 6` runs Taylor order 6 (numerator degree 79), which the paper notes also passes.

## Expected output

`expected_output.txt`. Every certificate line ends in `sturm=True flint=True -> OK`; the final lines are
`ALL POLYNOMIAL CHECKS PASSED`, `RESULT: PROVED (Taylor order 5)` and
`RESULT: ALL CERTIFIED (Taylor order 5, lam_K = 3/20, theta2 = 4/5)`.

## Re-run here

PASS (2026-10-04): all certificates pass; degrees agree with the paper's table (P1 13, P2 9, P3 51, P7 77,
P10 2-42, P8 6). Runtimes: `polychecks.py` 2.2 s (63 MB), `s6_hand.py` 9.9 s (103 MB), `w2_poly.py` 5.6 s
(73 MB); the paper states about 2, 10 and 6 seconds.

## Dependencies

Python 3.9+, sympy (tested 1.14.0), python-flint (tested 0.6.0), mpmath (tested 1.3.0).
