# supp_partB_numerics: numerical confirmations of the witnesses W_1 and W_2

**Paper item.** Remark `rem:lam-B-check` ("numerical confirmations"). **Role: confirmation only**; none of
this is used in any proof. These are floating-point scans and enumerations, not certificates.

## What is checked

- `verify_bellman.py`: dense scan of the leaf-exempt Bellman inequality for the witness W_1 (called W* in the
  code comments, older notation) at 72 activities in [0.1282, 3.2359] (including the breakpoints
  lambda_3..lambda_6), over k <= 8, m <= 6000 (m <= 200 for k >= 1) and a grid of ybar containing all nodes of h
  and their preimages; every near-minimum is refined in 50-digit mpmath by golden section. The two designed
  equalities (the cherry and the best arm at y_C) are excluded and the best-arm margin is reported separately.
- `verify_bellman_w2.py`: the same scan for the kinked witness W_2 (theta_2 = 4/5) at 16 activities in
  [0.0005, 0.15].
- `brute.c` with drivers `run_brute.py` (W_1, 15 activities) and `run_brute_w2.py` (W_2, 7 activities):
  exhaustive enumeration of all 20,247,374 planted branches with at most 20 vertices (cavity recursion in double
  precision), reporting max_b (log T_b - |b| f*) (the ceiling) and min (g(b) - h(y_b)) over non-leaf branches
  other than the cherry and the best arm.

Paper claims reproduced: no violation in either scan; 20,247,374 branches at 22 activities; the ceiling holds
with near-equality (|value| < 1e-15) only at the best arm; for W_1 the smallest g - h is 2.6e-7, at A_2
(size 5) at lambda = 0.1282.

## How to run

```
cc -O2 -o brute brute.c -lm        # the drivers call ./brute
python3 verify_bellman.py          # optional arg: number of grid activities (default 60, plus 14 fixed ones)
python3 verify_bellman_w2.py       # optional args: list of activities
python3 run_brute.py 20            # args: N [activities...]
python3 run_brute_w2.py 20
```

## Expected output

`expected_output.txt`. Both scans end with `violations: 0`; every `run_brute*` line reports
`branches=20247374`.

## Re-run here

PASS (2026-10-04): all four outputs are byte-identical to the original runs. Runtime / peak memory (one core):
`verify_bellman.py` 386 s, 45 MB; `verify_bellman_w2.py` 109 s, 34 MB; `run_brute.py 20` 3.6 s, 407 MB;
`run_brute_w2.py 20` 1.7 s, 407 MB (brute.c allocates arrays for 4e7 branches).

## Dependencies

Python 3.9+, numpy, mpmath (tested 1.3.0); a C compiler with the math library.
