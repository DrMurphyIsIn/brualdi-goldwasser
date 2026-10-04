# supp_hinge_chain: the hinge on [1+sqrt5, 100] and the chain route on [100, 2000]

**Paper items.** Supplement: the cells of the hinge witness on [1+sqrt5, 100] (paragraph "Cells" of
`sec:lam-covers`, and `rem:lam-uniform`), and the remark "what the chain route certified"
(`rem:lam-large-check`).

**Role.** Confirmations. Part (A) of the uniform ceiling theorem is proved by hand (the anchor
`prop:lam-anchor` at 1+sqrt5 and the monotonicity argument beyond); these computations enter no proof.

## What is checked

- `certify_L5.py`: for the hinge witness U(y) = -kappa (y - y_cherry)^+, kappa = (8/5) F*, and every
  m with 1 <= m <= 101 (the non-tail range for lambda <= 100), the k = 0 Bellman inequality
  Phi_m(lambda, ybar) <= 0 on ybar in [0, 1/2], with lambda an interval variable on
  [3.236067977, 100]; `mpmath.iv` with outward rounding, bisection of (lambda, ybar) boxes. The paper
  states 20 564 boxes.
- `certify_large.py`: on [100, 2000], the induction with expanded chains (`prop:lam-large-ind`): for each
  lambda-box a witness U = min(0, l_1, ..., l_n) is read off an untrusted linear program (`scipy`), and the
  remaining instances of the checks (B), (R) and (T) are verified with lambda and the messages as interval
  variables (`mpmath.iv`, 30 digits). The paper states 57 lambda-boxes, 516 062 cells, every inequality
  strict, about nine minutes. The program prints `THEOREM D: ...`, its internal name for this check.

## How to run

```sh
sh run_all.sh
```

or individually: `python3 certify_L5.py 100`, and `python3 certify_large.py LAM0 LAM1 1.1` for
(LAM0, LAM1) in (100, 300), (300, 700), (700, 1300), (1300, 2000).

## Expected output

- `certify_L5.py 100`: last line `ALL m in 1..101 certified on lam in [3.236067977, 100.0], yb in [0, 1/2]: 20564 boxes, ...`
- `certify_large.py`: each chunk ends `THEOREM D: lam in [a, b] CERTIFIED; N boxes; ...`, with
  N = 14 336, 30 871, 147 625, 323 230 (sum 516 062).

See `expected_output.txt`.

## Runtime and memory (measured here)

Measured here (one thread each): `certify_L5.py 100` 4.7 s, 15 MB; `certify_large.py` chunks 24 s,
51 s, 247 s and 539 s (about 14 min in all), peak memory 73 MB.

Re-run result: PASS. Hinge: 20 564 boxes. Chain route: 14 336 + 30 871 + 147 625 + 323 230 = 516 062
boxes, every chunk CERTIFIED, as stated in the paper.

## Dependencies

Python 3.9 or later, `mpmath` (1.3.0), and for `certify_large.py` also `numpy` (1.23.5) and `scipy`
(1.13.1; used only to propose the witness lines, which are then re-checked rigorously).
