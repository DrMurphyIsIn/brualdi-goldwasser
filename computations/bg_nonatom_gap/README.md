# bg_nonatom_gap: the non-atom gap at lambda = 1

**Paper item:** Proposition `prop:bg-gap` (non-atom gap; computer-verified): with delta_0 = 0.01426, every
planted branch b has delta(b) >= delta_0 times the number of its minimal non-atoms. Also the constants of
Proposition `prop:bg-high` (root degree >= 24). Role: part of the proof.

## Where the certificate is

The certifying program is `../bg_rate/certify.py` (sections B and C of its output), which also certifies
Lemma `lem:bg-rate`; run it there. Its sections B and C are copied in `expected_output_certify_B_C.txt`.
The computer-verified inputs of the proposition appear there as:

| input in the paper | line of the output |
|---|---|
| Phi_1(3/7) >= 0.01744 | `c=1: min over configs >= 0.017444` |
| 2 <= c <= 9: m_c + min_a (w_c(y_a) + delta(a)) >= 0.014273, attained at c = 6, a = A_4 | `c=6: min over configs >= 0.014273 (at A4)` (minimum over a in {leaf, A_1..A_30} and the tail A_{>30}) |
| min_{[0,c]} Phi_c >= 0.01783 for c = 10, 11, 12 | `c=10: ... >= 0.017838`, `c=11: ... 0.022008`, `c=12: ... 0.025662` |
| Q(13) >= 0.01860 | `c=>=13: ... >= 0.018608` |
| delta_0 = 0.01426 | `DELTA0 = 0.014273 >= 0.01426` (asserted) |

## Second implementation (this folder)

`gapcheck.py` (with `indep.py`, which imports nothing from `../bg_rate`) was written separately. It
recomputes m_c, D_c^-, D_c^+ and the per-c minimum over a in {leaf, A_1, ..., A_60} and the tail, Phi_1(3/7),
min Phi_c for c = 10..14 and 20 by its own branch-and-bound, Q(10), Q(13), and the constants of
`prop:bg-high` (atoms, delta_0 - mu_0^2/(4 kappa), the benchmark floor log(26/23) - 10/960 and the
non-spider ceiling).

    python3 gapcheck.py        # about 15 s, 19 MB; output in expected_output_gapcheck.txt

Requires Python 3 with `mpmath`.

## Re-run status

PASS (2026-10-04): both programs give the same per-c minima (0.037242, 0.031043, 0.020761, 0.016202,
0.014273, 0.014709, 0.016737, 0.019886 for c = 2..9), Phi_1(3/7) >= 0.017444, min Phi_10 >= 0.017838,
Q(13) >= 0.018608, all at least the values stated in the proposition. For `prop:bg-high` the interval
value of delta_0 - mu_0^2/(4 kappa) is 0.0124458, so the constant 0.012445 used in the paper is a valid
lower bound (the line printed by `certify.py`, `>= 0.012446`, is rounded to nearest).
