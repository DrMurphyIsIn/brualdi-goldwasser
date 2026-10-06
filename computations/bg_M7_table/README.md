# bg_M7_table: the exchange polynomials of the local-structure lemma

**Paper items:** Lemma `lem:bg-moves` (exchanges (M1)-(M7)) and table `tab:bg-M7` (exchanges (M7)(ii),
(iii) and the 13 exchanges of (M7)(vi)), with the positive factors and the (M3) corner polynomials listed
in its proof. Role: part of the proof (exact symbolic inputs of a hand proof).

## What is checked

`m7_table.py` (sympy, exact rational arithmetic). The weights T and messages y of all branches are
computed from the cavity recursion (a root with c children has degree c+1, T = (prod T_i)(c+1+R)/(c+1),
y = 1/(c+1+R)), not from closed forms, and the exchange quantity is
E(D_0, R_0) = P_N (m_N + D_0 + R_N + R_0)(m_O + D_0) - P_O (m_O + D_0 + R_O + R_0)(m_N + D_0).

- **[A] table `tab:bg-M7`.** For each of the 15 rows: E is affine in R_0 and quadratic in D_0; one
  positive rational c gives E(D_0, 0) = c * (column 1) and 2 E(D_0, (D_0+1)/2) = c * (column 2) as
  polynomial identities; after D_0 = 1 + t both columns have nonnegative coefficients and a positive
  constant term, so they are positive for every integer D_0 >= 1 (the real roots of column 2 are printed;
  all lie below 1).
- **[B] the proof of `lem:bg-moves`.** The stalk values T(P_4) = 17/8, y(P_4) = 7/17, T(P_5) = 41/16,
  y(P_5) = 17/41, and E = factor * (displayed polynomial) for (M1), (M2), (M5), (M6) (D_0 = 1,
  j = 5..12, with the value 2J^2 + (25/2)J + 15/2 at R_0 = 1/2), (M7)(i) (i = 0..10), (M7)(iv) (j = 2, 3, 4,
  symbolic i, via the closed forms of the arm values, themselves compared with the recursion), (M7)(v)
  (j = 1..4) and (M4) (2 <= i <= 8, 0 <= j <= i - 2).
- **[C] (M3).** The displayed bilinear expression equals 2(m+1)E, and its eight corner values are the
  displayed polynomials in t = D_0 - 1 and M = m - 2 (or m = 1), with nonnegative coefficients and
  constant terms 6, 9, 3, 9/2 and 13, 29/2, 11/2, 1.

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 m7_table.py
```

## Expected output

`expected_output.txt`, ending with `ALL CHECKS PASSED`.

## Runtime and memory (measured here, one core)

About 4 s, 66 MB.

## Re-run status

PASS (Python 3.9.6, sympy 1.14.0). All 15 rows, all factors and all corner values agree with the text.

## Dependencies

Python 3.9 or later, `sympy`.
