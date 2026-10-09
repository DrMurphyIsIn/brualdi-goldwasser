# computations/

The programs behind the computer-verified steps of the proofs of the results in this repository: the
answer to the Brualdi-Goldwasser question (lambda = 1), the weighted family pi_lambda, the matching-number
variant and the bounded-degree variant. An accompanying paper is in preparation; the main theorem itself is
stated and proved in the preprint `paper/paper.tex` and in Lean (`formalization/`). Each subfolder has the
program(s) for one set of checks, a README.md (what is checked, how to run it, expected output, runtime and
memory) and the output of a reference run (`expected_output*.txt`).

Role: **proof** = part of a proof; **route** = part of an alternative proof route that confirms a result
proved otherwise; **confirm** = a numerical confirmation that no proof uses.

Re-run status: each program was re-run from this directory, single-threaded
(`OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=VECLIB_MAXIMUM_THREADS=1`), and its output compared with
the numbers stated in the accompanying text: the folders of the first two tables below on 2026-10-04 (the
recovered checks of the additional table on 2026-10-06), and the checks added in October 2026 (last table)
on 2026-10-07 (the last three rows on 2026-10-09). See each README for details.

## Main checks

| what is checked | folder | role | re-run |
|---|---|---|---|
| Constants of the potential at lambda = 1 and the junction data for 2 <= c <= 9 | [bg_constants/](bg_constants/) | proof | PASS |
| Non-atom gap at lambda = 1: every planted branch gains at least 0.01426 per minimal non-atom | [bg_nonatom_gap/](bg_nonatom_gap/) | proof | PASS |
| Rate potential at lambda = 1: the rates eta_K and the 253 one-variable inequalities Phi~_c >= 0 on [0, c], 1 <= c <= K <= 22 | [bg_rate/](bg_rate/) | proof | PASS |
| Rate gaps Gamma_K, 1 <= K <= 22 | [bg_rate_gap/](bg_rate_gap/) | proof | PASS (program in bg_spider_comparison/) |
| Comparison with explicit spiders, 108 <= n <= 491, and the tails | [bg_spider_comparison/](bg_spider_comparison/) | proof | see folder README |
| Exact hull computation over all trees, n <= 491: the maximum is the spider of the table of maximizers (appendix of the preprint) | [bg_hull_dp/](bg_hull_dp/) | proof | PASS |
| Count exchanges, and the exact comparisons that identify the best spider and its limits | [bg_best_spider/](bg_best_spider/) | proof | PASS |
| Weighted family: enclosures of the arm-ladder breakpoints lambda_3, ..., lambda_6 | [lam_breakpoints/](lam_breakpoints/) | proof | PASS |
| Weighted family: the sharpest first-order degree potential (Randic limit) | [lam_first_order/](lam_first_order/) | confirm | PASS |
| Weighted family: no plain witness for lambda in [79/20, 10^6] (obstruction cover) | [lam_plain_obstruction/](lam_plain_obstruction/) | proof | PASS |
| Weighted family, part (B): the 63 low-degree rows, Bernstein coefficients, P9 | [lam_partB_rows/](lam_partB_rows/) | proof | PASS |
| Matching number: finite range of the stability comparison | [nu_stability/](nu_stability/) | proof | PASS |
| Matching number: exhaustive hull search, k <= 8, n <= 215 | [nu_hull_search/](nu_hull_search/) | proof | PASS |
| Bounded maximum degree: typed-potential certificates, Delta = 3, 4 and Delta = 5, 6, 7 | [deg_certificates/](deg_certificates/) | proof | PASS |

## Confirmation routes for the weighted family

The folders below hold the first implementations of programs of alternative proof routes for the weighted
family. Their second implementations were not archived; each README says so ("not archived").

| what is checked | folder | role | re-run |
|---|---|---|---|
| Certified rates at 26 activities (28 certificates) | [supp_certified_rates/](supp_certified_rates/) | route | PASS (recorded witnesses 28/28) |
| Witness covers of the activity range [0.1, 3.22] | [supp_covers/](supp_covers/) | route | PASS (9 091 058 cells) |
| Window [3.22, 1+sqrt5): interval confirmation of the window checks | [supp_window/](supp_window/) | confirm | PASS |
| Typed induction on (0, 0.1] | [supp_typed_induction/](supp_typed_induction/) | route | PASS |
| Monotonicity certificate on (0, 0.198] | [supp_small_monotonicity/](supp_small_monotonicity/) | route | PASS |
| Typed band certificate on [0.1, 2.85] | [supp_band/](supp_band/) | route | PASS |
| Hinge witness on [1+sqrt5, 100], chain route on [100, 2000] | [supp_hinge_chain/](supp_hinge_chain/) | route | PASS |
| High-degree certificates of part (B) (degree <= 77) | [supp_highdeg/](supp_highdeg/) | route | PASS |
| Numerical confirmations of the witnesses W_1, W_2 | [supp_partB_numerics/](supp_partB_numerics/) | confirm | PASS |
| Checks of the anchor at 1+sqrt5 and of the unmatched-vertices lemma | [supp_cherry_checks/](supp_cherry_checks/) | confirm | PASS |

The Lean formalization of the main theorem and of part (B) is in `formalization/`; the certificate
generators for it are in `certificates/`. Neither is needed to run the programs here.

## Requirements

- Python 3.9 or later (reference runs: CPython 3.9.6 on macOS).
- `mpmath` (>= 1.3; interval arithmetic `mpmath.iv`), `python-flint` (>= 0.6; Arb ball arithmetic),
  `sympy` (>= 1.12), `networkx` (>= 3.0; isomorphism tests in `bg_hull_dp/`).
- `numpy` and `scipy` only where a linear program proposes an untrusted witness that is then re-checked
  rigorously (`supp_certified_rates/run_all.sh`, `supp_hinge_chain/certify_large.py`, `supp_band/`,
  `deg_certificates/verify.py`).
- A C compiler for `supp_partB_numerics/brute.c` (`cc -O2 -o brute brute.c -lm`).

```sh
pip install "mpmath>=1.3" "python-flint>=0.6" "sympy>=1.12" "networkx>=3.0" numpy scipy
```

Most programs run in seconds to minutes on one core. The longest are noted in their READMEs: the cover
of [0.1, 3.22] (about 54 min in all, in independent chunks), the band and monotonicity certificates
(about 46 and 54 min, chunked), and `nu_hull_search/hulldp2.py` (about 16 min, 2.8 GB). Regenerating the
LP witnesses in `supp_certified_rates/run_all.sh` needs up to about 20 GB of memory; the recorded witnesses
are re-checked by `recheck_recorded.py` in under a minute.

## License

Apache License 2.0, like the rest of the mathematics in this repository (see `LICENSE` and `LICENSING.md`).

## Additional checks (inputs of the proofs written out by hand, and prefilter re-checks)

Several of these read files of existing folders through `../<folder>/`, so run them from inside `computations/`.

| what is checked | folder | role | re-run |
|---|---|---|---|
| The best-spider rule against the table of maximizers, 424 <= n <= 491, and the sizes where the rule fails | [bg_rule_vs_table/](bg_rule_vs_table/) | proof | PASS |
| Atom values and margins at lambda = 1 (root degree >= 24); g(A_4) < 1/960 | [bg_atom_margins/](bg_atom_margins/) | proof | PASS |
| The two exact zeros (c, S) = (1, 1), (5, 5/3) of the rate potential: one-sided derivatives and the local argument | [bg_rate_zeros/](bg_rate_zeros/) | proof | PASS |
| Exchange polynomials (M1)-(M7) of the local-structure lemma | [bg_M7_table/](bg_M7_table/) | proof | PASS |
| Re-check of the floating-point prefilters of the two hull searches | [hull_prefilter_check/](hull_prefilter_check/) | proof | PASS |
| Constants of the anchor at lambda = 1 + sqrt 5 | [lam_anchor_enclosures/](lam_anchor_enclosures/) | proof | PASS |
| Bounded degree: exact theta, rule enumeration and coverage | [deg_theta_exact/](deg_theta_exact/) | proof | PASS |

## Checks added in October 2026

These archive checks that had been run earlier but not kept, or replace them; each README says whether the
program was written in October 2026 or earlier. Run them from inside their folders.

| what is checked | folder | role | re-run |
|---|---|---|---|
| Constants at lambda = 1 and the junction data, in ball arithmetic | [bg_constants/second_check/](bg_constants/second_check/) | second check | PASS |
| Telescoping identity and the zero-slack branches on all rooted trees with <= 17 vertices | [bg_rate/rooted_trees/](bg_rate/rooted_trees/) | confirm | PASS |
| Comparison with explicit spiders, part (ii), from the printed table | [bg_spider_comparison/part_ii_check/](bg_spider_comparison/part_ii_check/) | second check | PASS |
| The exchanges (M1)-(M7) on all trees with n <= 18 | [bg_M7_table/exchange_test/](bg_M7_table/exchange_test/) | confirm | PASS |
| Direct sweep over spiders, 4 <= n <= 491 | [bg_hull_dp/spider_sweep/](bg_hull_dp/spider_sweep/) | confirm | PASS |
| Breakpoints lambda_3, ..., lambda_30 of the arm ladder, ball arithmetic | [lam_breakpoints/ball_check/](lam_breakpoints/ball_check/) | second check | PASS |
| Negative controls of the row check of part (B) | [lam_partB_rows/negative_controls/](lam_partB_rows/negative_controls/) (`row_checker_controls.py`) | negative control | PASS |
| Matching number: all k, n <= 120, and the second implementation for all k, n <= 60 | [nu_hull_search/all_k/](nu_hull_search/all_k/) | second check | PASS |
| Matching number: brute force over all trees with n <= 20 | [nu_hull_search/brute_force/](nu_hull_search/brute_force/) | second check | PASS |
| Tail values m_c + w_c(y(A_31)) of the non-atom gap, from the definitions of both programs | [bg_nonatom_gap/tail_values/](bg_nonatom_gap/tail_values/) | second check | PASS |
| The two-hub tree on 20 vertices beats every tree within three edge exchanges (local exchanges alone do not exclude two hubs) | [bg_two_hubs_n20/](bg_two_hubs_n20/) | confirm | PASS |
| Unmatched-vertices lemma in exact arithmetic: <= 14 vertices at lambda >= 2; <= 12 vertices at lambda = 1/2, 7/10, 4/5, 1 | [supp_cherry_checks/lemma_exact/](supp_cherry_checks/lemma_exact/) | confirm | PASS |
