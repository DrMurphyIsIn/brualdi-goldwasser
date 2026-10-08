# bg_hull_dp/third_implementation: the hull computation in pure rational arithmetic

**Paper item:** Theorem `thm:bg-small` (for 4 <= n <= 491, M_n is the value of the spider of the appendix
table, every maximizer is a spider, and the maximizer is unique up to isomorphism except at n = 21); the third
program of item C8 of the appendix on computations (Appendix C). Role: third implementation.
Because it has no floating-point step, it also independently reproduces the conclusions that the certification
of the floating-point prefilter of `../dp.py` (`../../hull_prefilter_check/`) protects.

`rational_dp.py` was written separately from `../dp.py` and `../dp_check.py`, from the statements alone, and
shares no code with them:

- every value is a Python `Fraction`; there is no floating-point filter;
- its own hull routine `K_giftwrap`: an exact strict-Pareto sweep followed by gift wrapping (largest slope from
  the current vertex, all collinear points kept, so ties survive); for every class with s <= NB it is also
  compared with `K_brute`, a direct test of the definition of Ext (p is kept iff some a = (1, t), t > 0, is
  maximized at p);
- the same planted-branch / bundle recursion as the paper (Z = P + Q/d, W = P/d, root value P + Q/k), with
  bundles B[s][c] built one child at a time and payloads that carry every multiset of children with a hull value;
- its own interning of rooted branches, its own centre/bicentre canonical form (AHU encoding) for counting
  maximizers up to isomorphism, and its own matching recursion `pi_tree` for pi, which is asserted to equal M_n
  for every maximizer;
- its own spider test and its own parser of the appendix table `../table_maximizers.tex` (every entry is asserted
  to have n vertices); for every n in the table the table spider is compared with the maximizers up to isomorphism.

`brute_matchings.py` is the second exhaustive search of item C8 (the first is `../brute.py`): for every tree on
n vertices (`networkx.nonisomorphic_trees`) it computes pi by enumerating all matchings directly, in exact
rationals, and reports the maximum, the number of maximizing trees and whether the table spider is one of them.

## How to run

From this directory, inside `computations/bg_hull_dp/` (the table is read from `../table_maximizers.tex`):

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 rational_dp.py 491 30 > out_491.txt      # about 2 hours; hull also checked against the definition for s <= 30
python3 brute_matchings.py 18                    # about 10 minutes
```

`python3 rational_dp.py 120` runs in about a minute and gives the first 119 lines.

## Expected output

`expected_output.txt`: the output of `rational_dp.py 491 30` (one line per n = 2..491) followed by that of
`brute_matchings.py 18`. Each line of the first part reads

    n=<n> M=<exact M_n> count=<number of maximizers up to isomorphism> allspider=True table=MATCH

(`table=` is empty for n = 2, 3, which the table does not list). The checks:

- the exact M_n equal those of `../results_dp_491.txt` for every 2 <= n <= 491;
- `count=1` for every n except n = 21 (`count=2`, M_21 = 19683/256);
- `allspider=True` for every n, and `table=MATCH` for all 488 values 4 <= n <= 491;
- no assertion fails (gift-wrap hull = definition of Ext on every class with s <= 30; pi of every maximizer and
  of every table spider equals M_n);
- `brute_matchings.py`: for 4 <= n <= 18 the same M_n, a unique maximizing tree, and it is the table spider.

## Runtime and memory (measured here, one core)

| run | time | peak memory |
|---|---|---|
| `rational_dp.py 491 30` | 7961 s (2 h 13 min) | 590 MB |
| `brute_matchings.py 18` | 627 s | 32 MB |

## Re-run status

PASS (2026-10-06, single-threaded; Python 3.9.6, networkx 3.2.1). For every 2 <= n <= 491 the exact M_n and the
number of maximizers equal those of `../results_dp_491.txt`; two maximizers only at n = 21; all maximizers are
spiders; 488/488 table matches. Both outputs are identical, line for line, to those of the original runs of these
programs.

## Dependencies

Python 3.9 or later; `rational_dp.py` uses the standard library only; `brute_matchings.py` needs `networkx`
(tested 3.2.1).
