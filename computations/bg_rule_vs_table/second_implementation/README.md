# bg_rule_vs_table/second_implementation: a second check of the best-spider rule against the table of maximizers

**What it checks:** that the best-spider rule gives the table maximizer for every 424 <= n <= 491 (the
argument uses 424 <= n <= 456), and the list of sizes n >= 300 where the rule fails. Role: independent second implementation of
the comparison in `../rule_vs_table.py`.

`check_rule_table.py` was written separately from `../rule_vs_table.py`, from the statement of the
rule and the printed table of maximizers only, and shares no code with it. It does only the
comparison of rule and table (as multisets of center branches); it does not recompute the values pi or
check the table against the hull computation, which `../rule_vs_table.py` does.

## What is checked

`check_rule_table.py`, in integer arithmetic:

1. The rule, applied as stated to every n: with s = 6(n-1) mod 11, the center
   carries only arms, all A_5 except s arms A_6 if s in {1, 2}; eight A_4 (n <= 722) or three A_6
   (n >= 733) if s = 3; seven A_4 (n <= 2319) or four A_6 (n >= 2330) if s = 4; 11 - s arms A_4 if
   s >= 5. The number of A_5 is (n - 1 - 9 k_4 - 13 k_6)/11 (an integer for every n, asserted); if it
   is negative, the rule names no spider.
2. The table of maximizers (`../../bg_hull_dp/table_maximizers.tex`, the same rows as Appendix A of the
   preprint `paper/paper.tex`) is parsed into multisets of center branches (C = cherry, A_j = arm with j cherries); every
   entry is asserted to have n vertices (2 per cherry, 2j + 1 per A_j, plus the center), and the
   entries are asserted to be exactly n = 4..491.
3. Rule = table for every 424 <= n <= 456 and for every 424 <= n <= 491; n = 423 is a failure; the
   failures for n >= 300 are printed and must be exactly {300, 311, 322, 333} and every n = 5 (mod 11)
   from 302 to 423 (16 sizes). The number of failures for 4 <= n <= 299 is printed (240 of 296).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 check_rule_table.py
```

It reads `../../bg_hull_dp/table_maximizers.tex`, found relative to the script. Another copy of the
table can be passed as the first argument.

## Expected output

`expected_output.txt`. The run ends with `ALL CHECKS PASSED`; the key lines are

    failures for n >= 300: 16 sizes [300, 302, 311, 313, 322, 324, 333, 335, 346, 357, 368, 379, 390, 401, 412, 423]
    matches the stated list of 16 sizes: True
    rule == table for every 424 <= n <= 456: True
    rule == table for every 424 <= n <= 491: True
    n = 423 is a failure: True

These agree with `../expected_output.txt` (same 16 failures, same rule and table spiders at each of
them, 240 of 296 failures below 300, rule = table on 424..491).

## Runtime and memory (measured here, one core)

Under 0.1 s, about 12 MB.

## Re-run status

PASS (Python 3.9.6).

## Dependencies

Python 3.9 or later, standard library only.
