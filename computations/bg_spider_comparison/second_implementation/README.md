# bg_spider_comparison/second_implementation: rate gaps, Psi_k and the size-aware root bound in ball arithmetic

**What it checks:** the rate gaps Gamma_K and their minimizing shapes, the constants
Psi_k = max_y (log(1+y) - k h_eta(y)), and the size-aware root bound U(A, j) - j Gamma_{k-1} evaluated at the
exact message sum S_A of each root configuration (sharper than the grid used by `../conc.py`). Role: second implementation of the checks done by `../conc.py`; the proof uses
the certified run of `../conc.py`, not this one.

These programs were written separately from `../conc.py`, `../core.py` and `../ivtools.py` and import none
of them. They use python-flint (Arb) balls at 200 bits for every logarithm and exact `Fraction`s for the
branch data (Z, message x, size). The rates eta_K are the exact rationals of the rate table, typed in
(`ind_common.py`, dictionary `ETA`).

## Files

| file | what it does |
|---|---|
| `ind_common.py` | Shared definitions: the constants F* (written `LAM`), beta, kappa, gamma, q = 3/23; the potential h and the weight w, h_eta = h - eta w; branches by the exact cavity recursion; the deficit g(b) and sigma~(b) = g(b) - eta|b| - h_eta(y_b); a rigorous upper bound `fmax_upper` for max_{0<=y<=Y} [log(1 + (S + j y)/k) - j h_eta(y)] (a float search locates the maximizer y0; the bound is the ball value at y0 plus the concave tangent bound from the one-sided derivatives at y0). |
| `ind_gamma.py` | Gamma_K for K = 1..22: the minimum of sigma~(B) over the stalks [A_j], j <= 4, and every end hub [C^c A_s^m1 A_{s+1}^m2] with at most K children at the root and s <= 40; arms longer than 40 are covered by the tail bound delta(A_j) >= j(beta - 2 eta) + F* - log(4/3) - kappa q^2 + 10 eta, which is asserted increasing and above the minimum. Prints the minimum and its shape (also restricted to arms of at most K children), the first j from which the tail bound exceeds the minimum, and the runner-up. Writes `ind_gamma.json`. |
| `ind_psi.py` | Psi_k = max_{y in [0,1]} (log(1+y) - k h_eta(y)), eta = eta_{k-1}, k = 2..23, as `fmax_upper(0, k, k, eta, 1)`. This small driver was added when the folder was assembled; the function it calls is that of `ind_common.py`. |
| `ind_spider.py` | For 7 <= n <= 491, the best balanced spider found by its own search (cherries and balanced arms A_s, A_{s+1}), with pi exact and Lambda = log pi - (n-1) F* as a ball lower bound. Writes `ind_spider.json`. (Any spider is a valid lower bound; for every 7 <= n <= 315 its pi equals that of the spider in the table of maximizers.) |
| `ind_root.py K1 K2` | For K1 <= k <= K2: the size-aware root bound, U(A, j) - j Gamma_{k-1}, for every admissible root configuration A = C^c A_s^m1 A_{s+1}^m2 (every s that fits in n <= 315, so no tail bound is needed) and every j, with U evaluated **at the exact message sum S_A** (no grid); then, for each 7 <= n <= 315, max over configurations with size <= n of the bound, minus eta_{k-1}(n-1), compared with Lambda of `ind_spider.json`. Prints n0 = 1 + the largest failing n (7 = no failure), the largest bound `Vmax`, the smallest margin over 108 <= n <= 315 and the number of failing n; `deg` repeats this with arm vertices restricted to at most k-1 children. Writes `ind_root_K1_K2.json`. |

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 ind_gamma.py
python3 ind_psi.py
python3 ind_spider.py          # must run before ind_root.py (writes ind_spider.json)
python3 ind_root.py 2 4
python3 ind_root.py 5 15
python3 ind_root.py 16 23
```

## Expected output

`expected_output.txt` (the six runs, in this order). The key facts:

- `ind_gamma.py`: the `gamma>=` column agrees with the stated values Gamma_{k-1} (k = K + 1) to
  the printed digits, the table rounding down in the last digit (0.039104, 0.039104, 0.026563, 0.015082 ->
  0.015081, 0.008501 -> 0.008500, ..., 0.011918), with the same minimizing shapes: `('stalk', 1)` = [A_1] for
  K = 1, 2; `('hub', (c, s, m1, m2))` = [C^c A_s^m1 A_{s+1}^m2], i.e. [C^2 A_3], [C^3 A_4], [C^4 A_4], [C^5 A_4]
  for K = 3..6 and [C^6 A_4] for K >= 7.
- `ind_psi.py`: Psi_2 <= 0.2998814, ..., Psi_23 <= 0.2176060; every value is below the stated bound Psi_k
  and agrees with it to the printed digits.
- `ind_root.py`: no failure for any n >= 106 and k >= 3 (the largest n0 is 106, at k = 9); the smallest margin
  for n >= 108 is 1.17e-03, at k = 9; no failure at all for k = 3 and k >= 12. (k = 2, paths, is not needed:
  its row fails up to n = 100.) The n0 values for 4 <= k <= 11 (59, 77, 77, 97, 101, 106, 101, 90) are at
  most the thresholds n-bar(k) (66, 77, 79, 99, 106, 108, 108, 99), which come from
  the 401-point grid of `../conc.py`; evaluating at the exact S_A is sharper.

## Runtime and memory (measured here, one core per process)

`ind_gamma.py` 30 s (100 MB); `ind_psi.py` under 1 s; `ind_spider.py` 4 s; `ind_root.py` 0.2 s (k = 2..4),
13 s (k = 5..15), 51 s (k = 16..23), each under 50 MB.

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, python-flint 0.6.0). The output of `ind_root.py` is
identical, line for line, to that of the original run of these programs.

## Dependencies

Python 3.9 or later, `python-flint` (tested 0.6.0).
