# bg_spider_comparison: comparison with explicit spiders, 108 <= n <= 315, and the rate gaps

**What it checks:**
- the comparison with explicit spiders, parts (i) and (iii): for 3 <= k <= 23 and 108 <= n <= 315,
  V_k(n) - eta_{k-1}(n-1) < Lambda^*(n), where n-bar(k) is the first size from which this holds
  (max_k n-bar(k) = 108); Lambda^*(n) >= 0.1206255 for 25 <= n <= 315 and
  log(26/23) - 0.012445 < 0.1101574;
- the rate gaps Gamma_K, with their minimizing shapes (see `../bg_rate_gap/`).

Part (ii) of the comparison (n >= 316) and the bounds Psi_k are certified by `../bg_rate/certify.py`
(sections E and G of its output). Role: part of the proof.

## What is checked

`conc.py` uses `mpmath.iv` (outward rounding, 120 bits) on rational enclosures of the constants, and the
certified rates eta_K of `certify_out.json` (a copy of the file written by `../bg_rate/certify.py`).
For each maximum degree k (cap K = k - 1):
- `gamma`: the rate gap Gamma_K (see `../bg_rate_gap/README.md`);
- `Psi`: Psi_k = max_{y in [0,1]} (log(1+y) - k H(y)) by interval branch-and-bound (upper bound);
- `PsiB`: the root bound with j_n >= 1 non-atom branches. All admissible atom configurations at the root
  (cherries and balanced arms A_s, A_{s+1}, s <= 18) are enumerated; configurations with a longer arm are
  covered by Psi_k minus the tail bound for delta^H(A_19). The increasing map
  U(S) = max_{x in [0,1/2]} [log(1 + (S + j_n x)/k) - j_n H(x)] is bounded by branch-and-bound at the 401 grid
  points S_i = S_max i / 400, and each configuration uses the grid point ceil(400 S_A / S_max) at or above its
  message sum S_A; atom costs are interval enclosures;
- for each 7 <= n <= 315, the resulting upper bound minus eta_{k-1}(n-1) is compared, on interval endpoints,
  with the lower bound Lambda^*(n) = log pi - (n-1) F^* of the spider listed for n in the table of maximizers
  (`table_maximizers.tex`, the table of Appendix A of the preprint `paper/paper.tex`; pi exact, log by interval). The output column `n0` is one more than the largest
  failing n (n-bar(k); `n0=7` means no failure).
- Finally, min Lambda^*(n) over 25 <= n <= 315 and log(26/23) - 12445/10^6 are printed and compared.

## How to run

    python3 conc.py            # all k = 2..23 (sequentially; several hours on one core)
    python3 conc.py K1 K2      # only K1 <= k <= K2; writes conc_out_K1_K2.json

Requires Python 3 with `mpmath`. Files: `conc.py`, `core.py`, `ivtools.py`, `spider_table.py`,
`table_maximizers.tex` (the table of maximizers; same file as `paper/table_maximizers.tex` of this repository),
`certify_out.json`.

## Expected output

`expected_output.txt`. Each line `k eta=... gamma>=... (shape) Psi<=... Vmax<=... n0=...`, then the overall
`N0 = 108` and

    high degree: ceiling <= 0.1101573 < min table Phi*_lo(25..315) = 0.1206255 : True

## Runtime measured here (one core per process)

The run time grows with k: about 2-3 min per k for k <= 11 (about 25 min for k = 2..11 together), and
406 s (k = 12) up to 778 s (k = 23) per k; about 2.5 hours for the whole range on one core, peak memory under
40 MB. Here it was run as `python3 conc.py` for k = 2..11 and as twelve parallel processes
`python3 conc.py k k`, k = 12..23; `expected_output.txt` is the concatenation of their per-k lines, followed
by the overall `N0` (the maximum of the per-k `n0`) and the `high degree` line, which every run prints
identically. It is line-for-line identical to the output of an earlier single sequential run.

## Re-run status

PASS (2026-10-04): the `n0` column equals the stated thresholds n-bar(k) for every k (101, 22, 66, 77, 79,
99, 106, 108, 108, 99, then 7 for k >= 12), so max_k n-bar(k) = 108 for 3 <= k <= 23 as in part (i);
`min table Phi*_lo(25..315) = 0.1206255` and `ceiling <= 0.1101573 < ...` give part (iii); the `gamma>=`
column and shapes give the stated rate gaps Gamma_K and their minimizing shapes (stated rounded down in the
last digit, e.g. 0.0150816 -> 0.015081). The rates `eta` are those certified
by `../bg_rate/certify.py`.

A second program (ball arithmetic, 200 bits) for the rate gaps, Psi_k and the size-root bound is in `second_implementation/`.

## Second check of part (ii) (added October 2026)

`part_ii_check/` checks part (ii) of the comparison a second time, in ball arithmetic, from the stated
values Psi_k, eta_{k-1} (as rounded for print) and the exact M_n of `../bg_hull_dp/results_dp_491.txt`
(smallest margin 3.13e-4, at k = 23, n = 317); see its README.
