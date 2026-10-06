# bg_best_spider/negative_controls: the count exchanges must reject xi = Xi + 10^-3

**Paper item:** Lemma `lem:bgx-counts` (count exchanges; computer-verified), the table of twelve exchanges.
Role: negative control (a deliberately wrong input that the check must reject); no proof uses it.

## What is checked

For each of the twelve rows, `nc_count_exchanges.py` calls the function `row` of `../tab.py`, imported
unchanged, which computes the exact ratio Xi, asserts xi <= Xi in exact rational arithmetic and expands
the two quadratics Delta_xi(X, y_lo X), Delta_xi(X, y_hi X). It then checks the sign statements of the
lemma: both quadratics positive for every real X >= 0 in the first ten rows, and for X >= 15 resp. X >= 16
in the rows 11 A_4 -> 9 A_5 and 9 P -> 2 A_4. A row passes iff both hold.

- Positive control: xi = the exact decimal of the table; all twelve rows pass.
- Negative control: xi = Xi + 1/1000 (exact rational); all twelve rows fail, at the comparison xi <= Xi.

The sign statements still hold for the perturbed xi (column `signs` is `True` on both sides). This is
expected: Delta_xi is increasing in xi, since its xi-term carries the positive factor
(m_N + D_0 + R_N + R_0)(m_O + D_0). So a larger xi only makes the quadratics larger, and the error is
caught by the exact comparison xi <= Xi alone; the sign statements cannot catch an overestimate of Xi.

## How to run

From this directory, in the layout `computations/bg_best_spider/negative_controls/` (the script imports
`../tab.py`):

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 nc_count_exchanges.py
```

## Expected output

`expected_output.txt`: one line per exchange (Xi, the table xi, `True True PASS`; then Xi + 1/1000,
`False True FAIL`), ending with `ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED` (exit code 0).

## Runtime and memory (measured here, one core)

Under 1 s, 57 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, sympy 1.14.0).

## Dependencies

Python 3.9 or later, `sympy` (>= 1.12); the file `tab.py` of `../`.
