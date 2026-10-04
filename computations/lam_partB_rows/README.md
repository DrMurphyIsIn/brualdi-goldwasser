# lam_partB_rows: the low-degree certificates of part (B)

**Paper item.** Lemma `lem:lam-polycert` (Appendix B, "Low-degree certificates", computer-verified),
with Remark `rem:lam-polycert` (programs and independent check). **Role: proof.**
Part (B) of the uniform-ceiling theorem reduces, by hand, to the scalar conditions (U1)-(U8) and (S1)-(S6),
and those not settled in the text to the certificates P1-P10. This folder certifies the rows of
part (a) of the lemma and the Bernstein coefficients of part (b).

## What is checked

(a) **The 63 rows.** Each condition, divided by the power of t at which it vanishes, is written in terms of
monotone one-variable *atoms* (`handatoms.py`). On a box [t1, t2] each atom is enclosed by its two endpoint
values (monotonicity only), and the condition is bounded below in `mpmath.iv` (30 digits, outward rounding).
A row is accepted only if its lower bound is positive and at least 30% of the value at the box midpoint.
Tables are built greedily on a mesh of 1/2000; for P10 from the two boxes [0, 3/86], [3/86, 3/43], halving any
box that fails the 30% rule.

| paper name | name in program output | t-range | rows | smallest lower bound |
|---|---|---|---|---|
| P1 (S2) | `C1 (S2)` | [0, 0.6181] | 10 | 0.0134 |
| P3 (S4) | `C3 (S4)` | [0, 0.6181] | 13 | 0.065 |
| P7 (S6), lambda in [3/20, 0.954] | `C7 (S6), W*` | [3/43, 0.3229] | 17 | 0.000547 |
| P8 (S6), lambda >= 2 | `C8 (S6)` | [1/2, 0.6181] | 1 | 0.062 |
| P10 (U1)...(U8b) | `C10 T1` ... `C10 T8b` | [0, 3/43] | 22 | 0.0088 (U4) |
| total | | | 63 | 0.000547 |

The program names T1, T2, T3a, T4, ..., T8, T8b correspond to the paper's (U1), (U2), (U3a), (U4), ..., (U8),
(U8b). The witness called W_1 in the paper is printed as `W*` (older notation). The program also prints a 24-row
table `C2 (S3)`: that is the alternative table for P2 mentioned in the remark; it is **not used** (the proof uses
the polynomial of (b) instead).

(b) **Bernstein coefficients** (`bernstein.py`, exact rationals via sympy): P2, the degree-6 polynomial on
[0, 0.6181], has Bernstein coefficients 15, 9.59, 4.68, 1.43, 0.81, 2.38, 1.52 (all positive, no subdivision);
P4-P6 (`C4`, `C5 cubic`, `C6 cubic` in the output) are positive on [0, 3.2361] resp. [0, 0.6181].

(c), (d) The exact identity e^{6 Dmax} = (4/3)^6 (2/3)^3 = 32768/19683 < 1.291^2 is printed by `polychecks.py`
(line `e^{6Dmax} = 32768/19683 = ... True`), and P9, G_3(3/43) = -0.00652... < 0, by `w2_poly.py` (line
`G_3(t_K) <= -0.0065183678167694235 -> lam_K < lam_3: True`, an exact rational upper bound from Taylor bounds).
These two programs, with their shared routine `cert.py`, are identical copies of those in `../supp_highdeg/`,
where the rest of their output (the high-degree certificates, a confirmation) is described.

## How to run

```
python3 lowdeg_tables.py     # writes lowdeg_tables.out, lowdeg_summary.tex, lowdeg_atoms.out
python3 bernstein.py
python3 polychecks.py        # for (c)
python3 w2_poly.py           # for (d) = P9 (first line of output)
```

## Expected output

`expected_output.txt` (standard output of `lowdeg_tables.py`, `bernstein.py`, `polychecks.py` and `w2_poly.py`). `lowdeg_tables.out` lists every row (box and lower
bound, 4 digits) and agrees with the rows printed in Appendix B; `lowdeg_atoms.out` tabulates the atom values at
every breakpoint (12 digits) for checking rows by hand; `lowdeg_summary.tex` is the summary table. The last
lines of the standard output are `ALL ROWS CERTIFIED` and `wrote lowdeg_atoms.out with 67 breakpoints`.

## Re-run here

PASS (2026-10-04): all 63 rows and their lower bounds agree with the paper's Table and row listing, and the
Bernstein coefficients agree. Runtime: `lowdeg_tables.py` 1.2 s, 17 MB peak RSS; `bernstein.py` 0.5 s, 55 MB; `polychecks.py` 2.2 s; `w2_poly.py` 5.6 s. The exact identity (c) and G_3(3/43) <= -0.0065184 (d) agree with the paper.

## Dependencies

Python 3.9+, mpmath (tested 1.3.0), sympy (tested 1.14.0); python-flint (tested 0.6.0) for `cert.py`.

## Note

The rows are also proved in Lean 4 (kernel-checked exact-rational interval checks over proved monotone atom
enclosures), so the correctness of these scripts is not needed for the formal proof.
