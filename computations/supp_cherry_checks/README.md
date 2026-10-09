# supp_cherry_checks: checks of the anchor at 1+sqrt5 and of the unmatched-vertices lemma

**What this is.** Checks of the hand proof of the sharp ceiling at the single activity lambda_c = 1+sqrt5
(the anchor), and of the unmatched-vertices lemma (for lambda >= 2, the expected number of unmatched
vertices of a planted branch on n vertices is at least 2n/(2+lambda)) and of the monotonicity in lambda
that follows from it.

**Role.** Confirmations of statements proved by hand; no proof uses them.

## What is checked

- `lamc_hand_check.py 16`: (1) the exact identities of the anchor proof at lambda_c = 1+sqrt5 (`sympy`),
  including 1 + lambda_c m y_cherry/(m+1) = (m phi + 1)/(m+1); (2) every constant of the proof in Arb ball
  arithmetic (`python-flint`): kappa - lambda_c/phi^3 > 0, kappa < 2, 1 + (2/3)lambda_c - phi^3 < 0, the
  m = 2 kink value, the placement of the m = 1 critical points and the m = 1 maximum, and f_j < log phi for
  j <= 2000; (3) g(b) >= h(y_b) on every non-leaf planted branch with at most 16 vertices (376 463
  branches), with equality only at the cherry.
- `lemma_M_check.py`: the group identity and inequality of Case 2 of the proof of the unmatched-vertices lemma on 200 000 random
  parameter values (lambda >= 2), and the lemma on all planted branches with at most 12 vertices at
  lambda in {2, 3.236, 10, 1e3, 1e5}.
- `monotone_ratio.py`: the monotonicity of T_b(lambda)/(2+lambda)^{n/2} (elasticity <= n/2) on all planted
  branches with at most 16 vertices at lambda in {100, 300, 1000, 2000, 1e4, 1e5, 1e7}.

`small_lambda_monotone.py`, `monotone_ratio.py` and `exp1_ceiling.py` also provide the rooted-tree
enumeration and polynomial routines that the other scripts load.

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 lamc_hand_check.py 16
python3 lemma_M_check.py
python3 monotone_ratio.py
```

## Expected output

See `expected_output.txt`. In particular: `(3) brute force 2 <= n <= 16: 376463 non-leaf branches; max (l - U(y)) = ... (must be <= 0); l = 0 exactly for: [((),)]`;
`group inequality violations: 0  min slack: 0.0`; `Lemma M violations ...: 0`; all elasticities minus
n/2 are <= 0 (0 up to rounding at the cherry).

## Runtime and memory (measured here)

Measured here: `lamc_hand_check.py 16` 2.8 s, 98 MB; `lemma_M_check.py` 1.9 s; `monotone_ratio.py`
33 s, 53 MB.

Re-run result: PASS. 376 463 non-leaf branches with equality only at the cherry; 0 violations of the
group inequality and of the lemma; all elasticities minus n/2 are <= 0.

## Dependencies

Python 3.9 or later, `sympy` (1.14.0), `python-flint` (0.6.0).

## Subfolder added in October 2026

- [`lemma_exact/`](lemma_exact/): the unmatched-vertices lemma checked in exact rational arithmetic, by a program
  written in October 2026 with its own enumeration of rooted trees: all 53,272 planted branches with at most
  14 vertices at lambda in {2, 3, 10, 100, 10^6} (slack exactly 0 only at the cherry), and all 7,813 branches
  with at most 12 vertices at lambda in {1/2, 7/10, 4/5, 1} (the lemma holds at 4/5 and 1 and fails at 7/10
  and 1/2). Confirmation only.
