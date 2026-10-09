# bg_hull_dp/spider_sweep -- direct sweep over spiders, 4 <= n <= 491

**What it checks:** the table of maximizers for 4 <= n <= 491 (the table of Appendix A of the preprint
`paper/paper.tex`), by enumerating spiders directly. Role: a confirmation of the table by a different method; no proof uses it.

`spider_sweep.py` was adapted in October 2026, as a single-process program, from the multi-process script
`certificates/checks/bg_spider_opt.py` of this repository (`search` subcommand: same closed form for pi of a
spider, same enumeration of configurations, same float prefilter). The counts of configurations, the
isomorphism test and the comparison with the table are new.

## What is checked

A spider has a center whose children are leaves (A_0), cherries and arms A_j. With C cherries and k_j arms A_j,
n = 1 + 2C + sum_j k_j (2j+1), D = C + sum_j k_j, and

    pi = (3/2)^C prod_j ((3/2)^j alpha_j)^{k_j} (1 + R/D),  alpha_j = (4j+3)/(3(j+1)),  R = C/3 + sum_j 3 k_j/(4j+3).

By the balance lemma (Section 6 of the preprint `paper/paper.tex`), a best spider with D >= 3 has all arm sizes (leaves counted as A_0) in {s, s+1}, so it is
determined by C and the number m of arms. For every n the program enumerates all configurations with D <= 2 and
all balanced configurations with D >= 3, selects by a floating-point log value the candidates within 1e-9 of
the maximum, evaluates those in exact Fraction arithmetic, groups the exact maximizers up to isomorphism
(canonical AHU encoding of the tree; a spider with one leaf and one arm can be read at two centers), and
compares the maximum value and the set of maximizers with `../results_dp_491.txt` (which agrees with the
table of maximizers). The float prefilter is not certified, so this is a confirmation, not a proof.

## How to run

    python3 spider_sweep.py 491        # from this folder; reads ../results_dp_491.txt

## Expected output

`expected_output.txt`: one line per n (numbers of configurations, the maximum, the maximizers, `MATCH`), then

    # balanced spiders with D>=3, 4<=n<=491: 4961739 (at most 30135 for one n, at n=491)
    # spiders with D<=2, 4<=n<=491: 15617
    # compared with ../results_dp_491.txt: 488 values of n, mismatches: 0
    # RESULT: PASS

## Runtime and memory (one core, measured here)

6 s, 36 MB.

## Dependencies

Python 3.9+ (standard library only).
