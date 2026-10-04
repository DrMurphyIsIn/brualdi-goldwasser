# bg_constants: the constants of the potential at lambda = 1

**Paper item:** Lemma `lem:bg-constants` (computer-verified), with the junction data of its table
(Table "Junction data for 2 <= c <= 9"). Role: part of the proof.

## What is checked

`verify_lemma51.py` checks, in rational interval arithmetic (every logarithm of a rational number is
enclosed by the atanh series with an explicit remainder, `core.log_encl`):

- (a) the enclosures of F* (printed as `lambda`), beta, kappa (and kappa < 1/5) and gamma;
- (b) the four inequalities (10/9)gamma - 1/3 < -0.0018, s - 3/7 + gamma(3/7)^2 < -0.297,
  1 - (2 kappa/3)(1 - 2q) > 0.907 and gamma - 3/43 - 2 kappa q (3/43)^2 > 0.228;
- (c) for 2 <= c <= 9, that D_c^-, D_c^+ and m_c = Phi_c(c/3) lie in the intervals of the table, and that
  r_5 = q (so m_5 = 0 exactly);
- (d) 0.0030 < Q(10) < 0.0033, the exact polynomial identity behind Q'(c) > 0 for c >= 10, and the
  formula for Phi_c'';
- the junction inequality s = 2 kappa (1/3 - q) < gamma (so h is convex);
- in addition, by interval branch-and-bound with one-sided derivative checks at the two exact zeros
  (c, S) = (1, 1) and (5, 5/3), that Phi_c(S) >= 0 on [0, c] for 1 <= c <= 60 (the Bellman inequality
  for h, used in the same section).

Each line is printed as `PASS ...`; the run ends with `ALL CHECKS PASSED`.

## How to run

    python3 verify_lemma51.py

Requires Python 3 with `mpmath` and `sympy`. `core.py` (in this folder) provides the rational log
enclosures and the constants.

## Expected output

`expected_output.txt` (this run). Runtime here: under 1 s, peak memory about 60 MB (one core).

## Re-run status

PASS: every enclosure and inequality of the lemma and every interval of the junction table is
reproduced (2026-10-04, Python 3.9.6, mpmath 1.3.0, sympy 1.14.0).

An independent implementation of the same constants is in `../bg_nonatom_gap/gapcheck.py`.
