# computations/

The programs behind the computer-verified lemmas of the paper "The maximum Laplacian ratio of a tree" and
its supplement. Each subfolder has the program(s) for one paper item (or one
set of checks), a README.md (what is checked, which paper item, how to run it, expected output, runtime
and memory) and the output of a reference run (`expected_output*.txt`).

Role: **proof** = part of a proof in the main paper; **supp-proof** = part of a proof in the supplement (a
confirmation route); **confirm** = a numerical confirmation that no proof uses.

Re-run status: each program was re-run from this directory, single-threaded
(`OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=VECLIB_MAXIMUM_THREADS=1`), and its output compared with
the numbers stated in the paper: the folders of the two tables below on 2026-10-04 (the recovered checks of the
additional table on 2026-10-06), and the checks added in October 2026 (last table) on 2026-10-07. See each
README for details. Paper items are cited by label and, for the computations, as "Appendix C, item Ck".

## Main paper

| paper item | label | folder | role | re-run |
|---|---|---|---|---|
| Constants at lambda = 1 and the junction table | `lem:bg-constants` | [bg_constants/](bg_constants/) | proof | PASS |
| Non-atom gap | `prop:bg-gap` | [bg_nonatom_gap/](bg_nonatom_gap/) | proof | PASS |
| Rate potential (253 one-variable checks) | `lem:bg-rate` | [bg_rate/](bg_rate/) | proof | PASS |
| Rate gap Gamma_K | `lem:bg-Gamma` | [bg_rate_gap/](bg_rate_gap/) | proof | PASS (program in bg_spider_comparison/) |
| Comparison with explicit spiders, 108 <= n <= 491, and tails | `lem:bg-compare` | [bg_spider_comparison/](bg_spider_comparison/) | proof | see folder README |
| Exact hull computation, n <= 491 (and the table of the appendix) | `thm:bg-small` | [bg_hull_dp/](bg_hull_dp/) | proof | PASS |
| Count exchanges; exact comparisons in `thm:bg-bestspider`, `cor:bgx-limits` | `lem:bgx-counts` | [bg_best_spider/](bg_best_spider/) | proof | PASS |
| Breakpoint enclosures | `lem:lam-bp` | [lam_breakpoints/](lam_breakpoints/) | proof | PASS |
| Sharpest first-order degree potential | remark after `thm:lam-randic` | [lam_first_order/](lam_first_order/) | confirm | PASS |
| Plain-form obstruction cover of [79/20, 10^6] | `lem:lam-cover` | [lam_plain_obstruction/](lam_plain_obstruction/) | proof | PASS |
| 63 low-degree rows, Bernstein coefficients, P9 | `lem:lam-polycert` | [lam_partB_rows/](lam_partB_rows/) | proof | PASS |
| Matching number: finite range of the stability comparison | `lem:nu-stab-cv` | [nu_stability/](nu_stability/) | proof | PASS |
| Matching number: exhaustive hull search, k <= 8, n <= 215 | `lem:nu-small-cv` | [nu_hull_search/](nu_hull_search/) | proof | PASS |
| Bounded degree certificates, Delta = 3, 4 and Delta = 5, 6, 7 | `lem:deg-cert34`, `lem:deg-cert567` | [deg_certificates/](deg_certificates/) | proof | PASS |

## Supplement

| supplement item | label | folder | role | re-run |
|---|---|---|---|---|
| Certified rates at 26 activities (28 certificates) | `thm:lam-cert` | [supp_certified_rates/](supp_certified_rates/) | supp-proof | PASS (recorded witnesses 28/28) |
| Witness covers of [0.1, 3.22] | `sec:lam-covers`, `rem:lam-uniform` | [supp_covers/](supp_covers/) | supp-proof | PASS (9 091 058 cells) |
| Window [3.22, 1+sqrt5): interval confirmation | `rem:lam-window-cv` | [supp_window/](supp_window/) | confirm | PASS |
| Typed induction on (0, 0.1] | `lem:lam-small-cv` | [supp_typed_induction/](supp_typed_induction/) | supp-proof | PASS |
| Monotonicity certificate on (0, 0.198] | `rem:lam-smallmono` | [supp_small_monotonicity/](supp_small_monotonicity/) | supp-proof | PASS |
| Band certificate on [0.1, 2.85] | `rem:lam-band` | [supp_band/](supp_band/) | supp-proof | PASS |
| Hinge on [1+sqrt5, 100], chain route on [100, 2000] | `rem:lam-large-check` | [supp_hinge_chain/](supp_hinge_chain/) | supp-proof | PASS |
| High-degree certificates (degree <= 77) | `lem:lam-polycert-hd` | [supp_highdeg/](supp_highdeg/) | supp-proof | PASS |
| Numerical confirmations of the witnesses W_1, W_2 | `rem:lam-B-check` | [supp_partB_numerics/](supp_partB_numerics/) | confirm | PASS |
| Checks of the anchor and of the unmatched-vertices lemma | `rem:lam-anchor-check`, `rem:lam-cherry-check` | [supp_cherry_checks/](supp_cherry_checks/) | confirm | PASS |

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

## Additional checks (inputs of the proofs written out in the text, and prefilter re-checks)

Several of these read files of existing folders through `../<folder>/`, so run them from inside `computations/`.

| paper item | label | folder | role | re-run |
|---|---|---|---|---|
| Rule of the best spider against the appendix table, 424 <= n <= 491 | `thm:bg-main`, `rem:bgx-race` | [bg_rule_vs_table/](bg_rule_vs_table/) | proof | PASS |
| Atom values and margins; g(A_4) < 1/960 | `tab:bg-atoms`, `prop:bg-high` | [bg_atom_margins/](bg_atom_margins/) | proof | PASS |
| One-sided derivatives and local argument at the exact zeros of the rate lemma | `lem:bg-rate` | [bg_rate_zeros/](bg_rate_zeros/) | proof | PASS |
| Exchange polynomials of the local-structure lemma | `lem:bg-moves`, `tab:bg-M7` | [bg_M7_table/](bg_M7_table/) | proof | PASS |
| Re-check of the floating-point prefilters of the two hull searches | `thm:bg-small`, `lem:nu-small-cv` | [hull_prefilter_check/](hull_prefilter_check/) | proof | PASS |
| Constants of the anchor at 1 + sqrt 5 | `prop:lam-anchor` | [lam_anchor_enclosures/](lam_anchor_enclosures/) | proof | PASS |
| Exact theta, rule enumeration and coverage, bounded degree | `lem:deg-cert34`, `lem:deg-cert567` | [deg_theta_exact/](deg_theta_exact/) | proof | PASS |

## Checks added in October 2026

These archive checks that the paper cites and that had been run earlier but not kept, or replace them; each
README says whether the program was written in October 2026 or earlier. Run them from inside their folders.

| paper item | label | folder | role | re-run |
|---|---|---|---|---|
| Lemma bg-constants (a)-(d) and the junction table, ball arithmetic (item C1) | `lem:bg-constants` | [bg_constants/second_check/](bg_constants/second_check/) | second check | PASS |
| Telescoping identity and zero-slack branches on all rooted trees with <= 17 vertices (item C3) | `eq:bg-tele`, `prop:bg-zero` | [bg_rate/rooted_trees/](bg_rate/rooted_trees/) | confirm | PASS |
| Part (ii) of the comparison lemma, from the printed table (item C5) | `lem:bg-compare` | [bg_spider_comparison/part_ii_check/](bg_spider_comparison/part_ii_check/) | second check | PASS |
| The exchanges (M1)-(M7) on all trees with n <= 18 (item C7) | `lem:bg-moves` | [bg_M7_table/exchange_test/](bg_M7_table/exchange_test/) | confirm | PASS |
| Direct sweep over spiders, 4 <= n <= 491 (item C8) | `thm:bg-small` | [bg_hull_dp/spider_sweep/](bg_hull_dp/spider_sweep/) | confirm | PASS |
| Breakpoints lambda_3..lambda_30, ball arithmetic (item C11) | `lem:lam-bp` | [lam_breakpoints/ball_check/](lam_breakpoints/ball_check/) | second check | PASS |
| Negative controls of the row check of part (B) (item C14) | `lem:lam-polycert` | [lam_partB_rows/negative_controls/](lam_partB_rows/negative_controls/) (`row_checker_controls.py`) | negative control | PASS |
| Matching number: all k, n <= 120, and the second implementation for all k, n <= 60 (item C16) | `lem:nu-small-cv` | [nu_hull_search/all_k/](nu_hull_search/all_k/) | second check | PASS |
| Matching number: brute force over all trees with n <= 20 (item C16) | `lem:nu-small-cv` | [nu_hull_search/brute_force/](nu_hull_search/brute_force/) | second check | PASS |
