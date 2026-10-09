# bg_spider_comparison/part_ii_check -- second check of part (ii) of the comparison with explicit spiders

**What it checks:** part (ii) of the comparison with explicit spiders, Psi_k - eta_{k-1}(n-1) below the
spider lower bound for n >= 316 (and the first number of part (iii)). Role: a second check of part (ii). The first check is section G of `../../bg_rate/certify.py`.

`part_ii_check.py` was written in October 2026 as an additional check.

## What is checked

Part (ii): for 3 <= k <= 23,

    Psi_k - eta_{k-1} (n-1) < Lambda_sp(n)   for 316 <= n <= 491,
    Psi_k - eta_{k-1} (n-1) < 0.11218        for n >= 347,

where Lambda_sp(n) = log pi - (n-1) F*, F* = log(621/64)/11, for the spider listed for n in the table
of maximizers, whose pi is the exact maximum M_n. The program takes

* Psi_k (upper bounds) and the exact rates eta_{k-1} as printed in the rate table (typed into the program);
* M_n, as exact rationals, from `../../bg_hull_dp/results_dp_491.txt`;

and makes every comparison in Arb ball arithmetic (python-flint, 256 bits); a comparison whose ball contains 0
counts as a failure. The second inequality is checked at n = 347; since eta_{k-1} > 0 its left side decreases
in n. Given the printed table, part (ii) is exactly this finite comparison; the bounds Psi_k themselves are
certified by `../../bg_rate/certify.py` (section E) and by `../../bg_rate/second_implementation/`.
It also prints min Lambda_sp(n) over 25 <= n <= 315 (part (iii): at least 0.1206255).

## How to run

From this folder, inside `computations/`:

    python3 part_ii_check.py

## Expected output

`expected_output.txt`: for each k the smallest margin over 316 <= n <= 491 (always at n = 317) and the margin
against 0.11218 at n = 347, then

    smallest margin in (ii), 316 <= n <= 491: 3.1336e-04 at k=23, n=317
    (iii) min Lambda_sp(n), 25 <= n <= 315: [0.1206255240 +/- 3.07e-11] at n=313; >= 0.1206255: True
    comparison with explicit spiders, part (ii): OK

The smallest margin against 0.11218 is 6.19e-4, at k = 23.

## Runtime and memory (one core, measured here)

0.1 s, 18 MB.

## Dependencies

Python 3.9+, python-flint (0.6.0 tested).
