# bg_rate_gap: the rate gaps Gamma_K

**Paper item:** Lemma `lem:bg-Gamma` (rate gap; computer-verified): for 1 <= K <= 22, Gamma_K, the minimum of
delta^H(B) over the stalks [A_j], 1 <= j <= 4, and all end hubs with at most K children per vertex, is at least
the value in table `tab:bg-rate` (column Gamma_{k-1}, with its minimizing shape). Role: part of the proof.

## Where the certificate is

The rate gaps are computed by `../bg_spider_comparison/conc.py` (function `gamma`), in the same run that
certifies Lemma `lem:bg-compare`; run it there. For each maximum degree k = K + 1 its output line reads

    k eta=... gamma>=G (shape) Psi<=... Vmax<=... n0=...

where `G` is the certified lower bound for Gamma_{k-1} and `shape` is the minimizer: `('stalk', j)` = [A_j],
`('hub', (c, s, m1, m2))` = the end hub [C^c A_s^m1 A_{s+1}^m2].

## What is checked

delta^H(B) is evaluated in interval arithmetic (`mpmath.iv`, 120 bits, rational enclosures of F*, beta,
kappa) from the exact rational weight and message of B, for every stalk [A_j], j <= 4, and every end hub
whose arms have at most 18 cherries (24 if the bound below does not yet exceed the minimum, which happens
for K <= 2). Larger arms are covered by the proved bound
delta^H(A_j) >= j(beta - 2 eta_K) + F* - log(4/3) - kappa q^2 + 10 eta_K, evaluated in interval arithmetic
(`tail_lb`): the program asserts beta - 2 eta_K > 0 and that the bound at j = 19 (resp. 25) exceeds the
minimum found.

## Re-run status

PASS (2026-10-04); see `../bg_spider_comparison/README.md`. The certified bounds agree with the column
Gamma_{k-1} of table `tab:bg-rate` and its shapes ([A_1] for k = 2, 3; [C^2 A_3], [C^3 A_4], [C^4 A_4],
[C^5 A_4] for k = 4..7; [C^6 A_4] for k >= 8); the paper rounds the printed values down in the last digit
where needed (for example 0.0150816 -> 0.015081).
