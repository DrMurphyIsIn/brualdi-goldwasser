# lam_plain_obstruction/second_implementation: a second cover of [79/20, 10^6] in ball arithmetic

**What it checks:** that there is no plain witness for lambda in [79/20, 10^6] at the cherry rate, via the
two-point margin mu. Role:
second implementation **of the conclusion only**. It confirms that for every lambda in [79/20, 10^6] some pair
(a, b) with y_2(a) < a < b < 1 gives mu(lambda; a, b) > 0, which is what the proof that plain witnesses fail
needs; it does **not** re-check the ten-pair cover as stated, because it chooses its own pair on each cell instead
of using the ten fixed pairs (and its pairs need not have a > 1/2).

`cover_arb.py` was written separately from `../obstruction.py` and shares no code with it.

## What is checked

With F = (1/2) log(1 + lambda/2), y_2(a) = 1/(2 + lambda a), L_x = log(1 + lambda x/2), the margin is
mu(lambda; a, b) = L_b + ((1 - b)/(a - y_2(a))) (L_a - F) - 2F.

- The interval [79/20, 10^6] is split into 400 cells with rational endpoints on a geometric grid.
- On each cell, lambda is the Arb ball (python-flint, 256 bits) spanning the two exact rational endpoints.
- A pair (a, b) is chosen by an untrusted float search at the midpoint (a maximizing (L_a - F)/(a - y_2(a)), then
  b maximizing mu) and rounded to rationals with denominators at most 10^6 and 10^7.
- mu is evaluated in ball arithmetic on the whole cell (asserting y_2(a) < a < b < 1); the cell is accepted if
  the ball is positive, and otherwise bisected (cells narrower than 10^-15 would abort the run).
- It also prints mu at lambda = 79/20 for the fixed pair (161/200, 999/1000) and for (4/5, 59/60).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 cover_arb.py
```

## Expected output

`expected_output.txt`:

    point 79/20 with (161/200,999/1000): [1.74002389326e-7 +/- 4.12e-19]
    point 79/20 with (4/5,59/60): [-5.53134824409e-5 +/- 1.82e-17]
    cells: 19776 min lower bound: (1.5662575725932046e-11, 3.9629447341402066, 3.9629485425350697, Fraction(217729, 270218), Fraction(5878208, 5888217)) smallest cell width: 9.520987158139517e-07

that is, 19,776 accepted cells covering [79/20, 10^6], smallest lower bound 1.6e-11 (on a cell near
lambda = 3.963), and mu(79/20; 161/200, 999/1000) = 1.740e-7 as in `../expected_output.txt`. (The pair
(4/5, 59/60) used in the analytic tail beyond 10^6 is negative at 79/20, as expected.) The pairs come from a
floating-point search, so the cell count could differ on another platform; the conclusion (every cell
accepted) is what is checked.

## Runtime and memory (measured here, one core)

12 s, 40 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, python-flint 0.6.0, numpy 1.23.5).

## Dependencies

Python 3.9 or later, `python-flint` (tested 0.6.0), `numpy`.
