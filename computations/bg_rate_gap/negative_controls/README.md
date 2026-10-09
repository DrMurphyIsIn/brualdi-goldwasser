# bg_rate_gap/negative_controls: the rate gaps must reject Gamma_K + 10^-5

**What it checks:** the check of the rate gaps Gamma_K at lambda = 1, K = 1..22, with their minimizing
shapes. Role: negative control (a deliberately wrong input that the check
must reject); no proof uses it.

## What is checked

`nc_rate_gap.py` calls the function `gamma` of `../../bg_spider_comparison/conc.py` (the program that
certifies the rate gaps), imported unchanged, with the certified rates of
`../../bg_spider_comparison/certify_out.json`. For each cap K = 1, ..., 22 (k = K + 1) it returns the
interval enclosure of sigma~(B) at the minimizing stalk or end hub, and that shape. A tabulated value G is
accepted iff the lower end of the enclosure is >= G.

- Positive control: G = the tabulated value; accepted for all 22 caps, and the minimizing shape is the one
  of the table ([A_1] for k = 2, 3; [C^2 A_3], [C^3 A_4], [C^4 A_4], [C^5 A_4] for k = 4..7; [C^6 A_4] for
  k >= 8).
- Negative control: G + 10^-5; rejected for all 22 caps. Moreover the upper end of the enclosure at the
  minimizing shape is below G + 10^-5 (column `refuted`): that single shape shows the perturbed bound is
  false, not merely uncertified. (The tabulated values are the certified ones rounded down in the sixth
  decimal, so the margin is below 10^-6 in every row.)

## How to run

From this directory, in the layout `computations/bg_rate_gap/negative_controls/` (the script imports from
`../../bg_spider_comparison/`):

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 nc_rate_gap.py
```

## Expected output

`expected_output.txt`: one line per k = 2..23 with the shape, the enclosure, the table value, `PASS` for
the table value, `FAIL` for the value + 10^-5 and `True` in the column `refuted`; then
`ALL NEGATIVE CONTROLS BEHAVED AS EXPECTED` (exit code 0).

## Runtime and memory (measured here, one core)

About 33 s, 18 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, mpmath 1.3.0).

## Dependencies

Python 3.9 or later, `mpmath` (>= 1.3); the files `conc.py`, `core.py`, `ivtools.py`, `spider_table.py`,
`table_maximizers.tex`, `certify_out.json` of `../../bg_spider_comparison/`.
