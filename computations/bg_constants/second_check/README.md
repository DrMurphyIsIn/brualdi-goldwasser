# bg_constants/second_check -- Lemma bg-constants (a)-(d) and the junction table, in ball arithmetic

**Paper item:** Lemma `lem:bg-constants` (constants at lambda = 1) and table `tab:bg-junction`; Appendix C,
item C1. Role: a second check of all of (a)-(d). The first program is `../verify_lemma51.py` (exact rationals
and the atanh series); `../../bg_nonatom_gap/gapcheck.py` confirms the junction table, the third inequality
of (b) and (d), but does not print (a) or the other three inequalities of (b).

`constants_ball.py` was written in October 2026 as an additional check, from the definitions in the text.

## What is checked

In Arb ball arithmetic (python-flint, 256 bits), from
F* = log(621/64)/11, q = 3/23, beta = 2F* - log(3/2), kappa = beta/(1/3 - q)^2, gamma = (3/2)(F* - beta),
s = 2 kappa (1/3 - q), r_c = 3/(4c+3), p = 1 + q:

* (a) the enclosures of F*, beta, kappa, gamma, and kappa < 1/5;
* (b) the four inequalities, and gamma > s;
* (c) D_c^-, D_c^+ and m_c for 2 <= c <= 9 inside the open intervals of `tab:bg-junction`; m_5 = 0 is exact
  (F* + 5 beta = log(23/18)), and the program checks that its ball contains 0 (radius below 1e-70);
* (d) 0.0030 < Q(10) < 0.0033, Q(c) = F* - kappa q^2 - log((1+pc)/(c+1)) - c/(4 kappa (1+pc)^2).

Each strict inequality is decided on the balls; a ball that meets the bound counts as a failure.

## How to run

    python3 constants_ball.py

## Expected output

`expected_output.txt`, ending with `Lemma bg-constants (a)-(d): OK`. For example
F* = 0.206586181689..., beta = 0.00770725526889..., kappa = 0.187215522118..., gamma = 0.298318389629...,
(10/9)gamma - 1/3 = -0.0018684..., Q(10) = 0.0031411....

## Runtime and memory (one core, measured here)

0.1 s, 18 MB.

## Dependencies

Python 3.9+, python-flint (0.6.0 tested).
