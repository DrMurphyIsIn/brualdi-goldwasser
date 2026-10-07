# lam_partB_rows/negative_controls: W_1 must fail at A_2 below lambda_{A_2}

**Paper item:** Lemma `lem:lam-polycert` and Theorem `thm:lam-B-wstar` (the witness W_1, used from lambda = 3/20 on);
item C14 of the appendix on computations. Role: negative control (a deliberately wrong input that the test must
reject) plus a numerical sanity test; no proof uses this program.

`sanity_and_controls.py` was written from the definitions in the text, separately from the other programs of this
folder, in `mpmath` at 30 digits (floating point, not interval arithmetic). The program calls W_1 `W*` and W_2 `W2`.

## What is checked

1. **Negative controls (last three lines of the output).** The witness W_1 is built at lambda = 0.10, 0.12 and
   0.128, all below lambda_{A_2} = 0.1281277..., where a linear ramp must fail at the arm A_2. The program evaluates
   condition (S6), g(A_2) - W_1(y_2), with g(A_2) = 5F - log T(A_2) from the cavity recursion, and finds it negative
   each time (-8.2e-5, -2.8e-5, -4.7e-7), as it must: the test is not blind to a failure of (S6).
2. **Sanity test (not a proof).** For 22 activities in (0, 1 + sqrt 5) (random ones with a fixed seed, plus 3/20,
   0.13, 0.1282, 0.43050..., 2 and 1 + sqrt 5 - 10^-6) and the witness the paper uses there (W_2 up to 3/20, W_1
   from 3/20; both at 0.1282 and 0.13): the Bellman margins on a grid of messages (with every kink and its
   preimages), apart from the designed equalities, are positive; on 1,500 random planted branches and the arms,
   log T_b <= |b| F, and g(b) >= h(y_b) with equality only where designed. Then the unscaled conditions (U1)-(U8)
   of W_2 (printed as T1-T8) and (S1), (S2) are evaluated on 60 values of lambda in (0, 3/20]; all are positive.

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 sanity_and_controls.py
```

## Expected output

`expected_output.txt`; it ends with

    sensitivity: W* at lam=0.10: g(A2)-h(y2) = -8.239e-5 (negative expected below 0.12813)
    sensitivity: W* at lam=0.12: g(A2)-h(y2) = -2.806e-5 (negative expected below 0.12813)
    sensitivity: W* at lam=0.128: g(A2)-h(y2) = -4.672e-7 (negative expected below 0.12813)

## Runtime and memory (measured here, one core)

165 s, 18 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, mpmath 1.3.0). The output is identical to that of the original run.

## Dependencies

Python 3.9 or later, `mpmath`.
