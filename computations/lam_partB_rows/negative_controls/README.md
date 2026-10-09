# lam_partB_rows/negative_controls: negative controls of the row check, and a sensitivity test

This folder has two programs.

* `row_checker_controls.py` (written in October 2026 as an additional check): **negative controls of the row
  check itself.** It runs the code of `../lowdeg_tables.py` on deliberately wrong inputs, each of which must be
  rejected. Described in the first section below.
* `sanity_and_controls.py`: a separate 30-digit floating-point program (a sensitivity test and a numerical
  sanity test, not the row check). Described in the second section below.

## row_checker_controls.py

**What it checks:** that the row check of the 63 low-degree rows of part (B) rejects deliberately wrong
conditions. Role: negative control.

The program executes, unchanged, the definitions of `../lowdeg_tables.py` up to the point where that program
starts writing its output (the row test `okrow`, the greedy table builder `greedy`, the conditions `S2`, `S4`,
`S6`, `S6hi` and, through `../w2_table.py`, the nine conditions of P10), and the P10 halving loop of
`../lowdeg_tables.py` as a function. It then runs:

1. a positive control: the unchanged conditions give the 63 stated rows;
2. 39 negative controls: each of the 13 conditions used in the proof (P1 (S2), P3 (S4), P7 (S6) for W_1,
   P8 (S6) for lambda >= 2, and the nine conditions of P10) is lowered by a constant c slightly above its value at a
   point t* of its range, so that the lowered condition is negative at t*; three points t* per condition (one
   quarter, one half and three quarters of the range). Each lowered table must be rejected: the greedy builder
   stops with `cannot start at ...`, and the P10 halving stops at the minimum box width 1e-6.

Run (from this folder): `python3 row_checker_controls.py`. Expected output: `row_checker_controls_output.txt`,
which begins `positive control: unchanged conditions give 63 rows (expected: 63)`, has one `rejected` line per
control, and ends

    39 negative controls run
    ALL NEGATIVE CONTROLS REJECTED

Runtime and memory (one core, measured here): 3.2 s, 17 MB. Dependencies: Python 3.9+, mpmath.

## sanity_and_controls.py


**What it checks:** that a floating-point evaluation of condition (S6) for the witness W_1 (used from
lambda = 3/20 on) detects the failure below lambda_{A_2}, and numerically that the witnesses W_1, W_2 satisfy
the Bellman inequality. Role: a sensitivity test (a deliberately wrong input that a separate
floating-point test must reject; it does not run the row check) plus a numerical sanity test; no proof uses this
program.

`sanity_and_controls.py` was written from the definitions in the text, separately from the other programs of this
folder, in `mpmath` at 30 digits (floating point, not interval arithmetic). The program calls W_1 `W*` and W_2 `W2`.

### What is checked

1. **Sensitivity test (last three lines of the output).** The witness W_1 is built at lambda = 0.10, 0.12 and
   0.128, all below lambda_{A_2} = 0.1281277..., where a linear ramp must fail at the arm A_2. The program evaluates
   condition (S6), g(A_2) - W_1(y_2), with g(A_2) = 5F - log T(A_2) from the cavity recursion, and finds it negative
   each time (-8.2e-5, -2.8e-5, -4.7e-7), as it must: the test is not blind to a failure of (S6).
2. **Sanity test (not a proof).** For 22 activities in (0, 1 + sqrt 5) (random ones with a fixed seed, plus 3/20,
   0.13, 0.1282, 0.43050..., 2 and 1 + sqrt 5 - 10^-6) and the witness used there (W_2 up to 3/20, W_1
   from 3/20; both at 0.1282 and 0.13): the Bellman margins on a grid of messages (with every kink and its
   preimages), apart from the designed equalities, are positive; on 1,500 random planted branches and the arms,
   log T_b <= |b| F, and g(b) >= h(y_b) with equality only where designed. Then the unscaled conditions (U1)-(U8)
   of W_2 (printed as T1-T8) and (S1), (S2) are evaluated on 60 values of lambda in (0, 3/20]; all are positive.

### How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 sanity_and_controls.py
```

### Expected output

`expected_output.txt`; it ends with

    sensitivity: W* at lam=0.10: g(A2)-h(y2) = -8.239e-5 (negative expected below 0.12813)
    sensitivity: W* at lam=0.12: g(A2)-h(y2) = -2.806e-5 (negative expected below 0.12813)
    sensitivity: W* at lam=0.128: g(A2)-h(y2) = -4.672e-7 (negative expected below 0.12813)

### Runtime and memory (measured here, one core)

165 s, 18 MB.

### Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, mpmath 1.3.0). The output is identical to that of the original run.

### Dependencies

Python 3.9 or later, `mpmath`.
