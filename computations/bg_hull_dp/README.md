# bg_hull_dp: the exact hull computation over all trees, n <= 491

**Paper item:** Theorem `thm:bg-small` (computer-verified): for 4 <= n <= 491, M_n equals the value of the
spider listed in the appendix table, every maximizer is a spider, and the maximizer is unique up to
isomorphism except at n = 21 (C^10 and C^3 A_3^2, M_21 = 19683/256). Also the programs of Remark
Appendix C, item C8 (programs (1) and (2), and the exhaustive search for n <= 18). Role: part of the proof
(needed for the spider property for n <= 107, and for identity and uniqueness of the maximizer for
n <= 456 and the appendix table).

## Files

| file | what it does |
|---|---|
| `dp.py` | The main program (Appendix C, item C8 (1)). Exact rational DP over planted branches H[m] and bundles B[s][c]; Ext computed exactly after a certified float prefilter; payloads carry every maximizing tree. For each n it reduces the maximizers modulo isomorphism (canonical form), tests each for being a spider, compares with the table entry up to isomorphism, and recomputes pi by an unrelated exact matching recursion (asserted equal to M_n). |
| `dp_check.py` | The second program (Appendix C, item C8 (2)): unbounded knapsack over branch sizes with value-graph backpointers, a different exact hull routine and float certificate, isomorphism by `networkx`, per L by an integer recursion. Shares only the table parser with `dp.py`. |
| `test_hull.py` | Randomized test (20,000 point sets with many collinear points) of both exact hull routines against the definition of Ext. |
| `brute.py` | Exhaustive search over all trees (`networkx.nonisomorphic_trees`) for n <= 18, compared with the output of `dp.py`. |
| `table_maximizers.tex` | The appendix table of the paper (same file as `paper/table_maximizers.tex` of this repository). |

## How to run

    OMP_NUM_THREADS=1 python3 dp.py 491 results_dp_491.txt     # writes results_dp_491.txt and results_dp_491_stats.json
    python3 test_hull.py
    python3 brute.py 18 results_dp_491.txt
    OMP_NUM_THREADS=1 python3 dp_check.py 400 results_check_400.txt

Requires Python 3 with `numpy` and `networkx` (and `fractions` from the standard library).

## Expected output

- `expected_output.txt`: the console output of the four runs.
- `results_dp_491.txt`: one line per n: exact M_n, number of maximizers, the maximizers as spiders,
  `table=MATCH`, |H_n|. `results_dp_491_stats.json`: hull sizes per n.
- `results_check_400.txt`: the output of `dp_check.py`.

The summary of `dp.py` must read:

    max |H_m| = 12  max |B[s][c]| = 24
    n with >1 maximizer: [21]
    n>=4 with a non-spider maximizer: []
    table mismatches: []  (table covers 488 values of n <= NMAX)

and the stats file gives max over s of sum_c |B[s][c]| = 1375.

## Runtimes measured here (one core)

| run | time | peak memory |
|---|---|---|
| `dp.py 491` | 148 s | 590 MB |
| `test_hull.py` | 8 s | 42 MB |
| `brute.py 18` | 8 s | 27 MB |
| `dp_check.py 400` | 1626 s | 335 MB |

## Re-run status

PASS (2026-10-04): `dp.py` reproduces, for every 4 <= n <= 491, the table spider (488 matches), only spider
maximizers, a unique maximizer except at n = 21 (two, M_21 = 19683/256), and the class sizes 12, 24, 1375
quoted in Appendix C, item C8. `results_dp_491.txt` is byte-identical to the earlier run.
`test_hull.py` and `brute.py 18` (123,867 trees at n = 18) pass. `dp_check.py 400` reproduces the exact
M_n and maximizer counts, only spiders, two maximizers only at n = 21, and 397/397 table matches
(n <= 400); its `results_check_400.txt` is identical to the earlier run.

The third implementation mentioned in Appendix C, item C8 (3) (pure rational, about two hours) and a
second exhaustive search are in `third_implementation/`.

## Direct sweep over spiders (added October 2026)

`spider_sweep/` confirms the table by enumerating the balanced spiders directly (4,961,739 for 4 <= n <= 491,
at most 30,135 for one n, and 15,617 spiders with D <= 2), with exact comparison of the near-best candidates;
see its README. It is a single-process version of `certificates/checks/bg_spider_opt.py` of this repository.
