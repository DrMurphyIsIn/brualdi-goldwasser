# supp_band: typed band certificate on [0.1, 2.85]

**What this is.** A second certificate for the middle activity range: the sharp ceiling
log T_b(lambda) <= |b| F*(lambda) for every planted branch b, for lambda in [0.1, 2.85], by a typed induction.

**Role.** Confirmation of part (B) of the uniform ceiling theorem on [0.1, 2.85]; not used in its proof.

## What is checked

A typed induction (the docstring of `certify_band.py` states it in full): the exact types are the leaf,
the cherry and the arms A_2, ..., A_59; a general branch of root degree d <= 60 is typed by d and by which
of eight equal bins of [0, d-1] contains the sum of its children's messages; pooled types cover longer
arms and higher degrees; parents up to degree 1200 are checked explicitly and beyond by an analytic tail.
F* is replaced from below by the rate f_J of one arm J per lambda-box. The witness bounds come from an
untrusted value iteration plus a slack DELTA (2e-4 below 0.5, 3e-4 above); the trusted check re-verifies
every inequality. Transcendental inputs are enclosed in `mpmath.iv` and rounded outward; the separable
stage runs in double precision with a cushion PAD = 1e-9.

`run_band.py` is the adaptive driver: it tries a box of width w, halves it on failure, and grows it by
1.5 after a pass (capped at WMAX); it prints `PASS [a, b] ...` for every accepted box and ends
`BAND [a, b]: CERTIFIED; N boxes; ...` only if the whole range is covered contiguously.

Supporting checks:
- `band_hyp_check.py a b DELTA [NMAX]`: the typed hypothesis on every planted branch with at most 13
  vertices (60 897 evaluations with NMAX = 13; the default NMAX is 14) on one box. Needs `small_lambda_monotone.py`, `monotone_ratio.py`,
  `exp1_ceiling.py` (rooted-tree enumeration and cavity values).
- `band_negctl.py`: negative controls on the box [1.0, 1.01]; the baseline passes and every broken
  variant fails.

## How to run

```sh
sh run_all.sh                                  # the eight chunks, 167 boxes in all
python3 band_hyp_check.py 0.1 0.1005 0.0002 13  # n <= 13 as in the paper; also 0.429 0.439 0.0002 13, 2.815641 2.85 0.0003 13
python3 band_negctl.py
```

## Expected output

Box counts per chunk 31, 19, 22, 22, 19, 14, 14, 26 (total 167, contiguous on [0.1, 2.85]); best arm J
from A_3 to A_36. See `expected_output.txt`.

## Runtime and memory (measured here)

Measured here (one thread per chunk): 8 chunks, 2 757 s in all (about 46 min sequentially; chunks are
independent), longest 550 s; peak memory 33 MB. `band_hyp_check.py` about 5 s per box with NMAX = 13
(about 14 s with the default NMAX = 14); `band_negctl.py` 74 s.

Re-run result: PASS. Box counts 31, 19, 22, 22, 19, 14, 14, 26 (total 167). The hypothesis check passes
on the three recorded sample boxes with 60 897 evaluations each (n <= 13). The paper speaks of five
sample boxes; only these three were recorded with the program, so `expected_output.txt` contains three.
The margins printed for the boxes at 0.429 and 2.8156 (-2.013e-4, -3.054e-4) differ slightly from an
earlier log (-2.026e-4, -3.085e-4), made before the curvature-term correction described in the paper;
both are negative, as required. Negative controls: the baseline passes and every broken variant fails.

## Dependencies

Python 3.9 or later, `mpmath` (1.3.0), `numpy` (1.23.5).
