# bg_rule_vs_table: the best-spider rule against the table of maximizers, 424 <= n <= 491

**What it checks:** that the best-spider rule (the rule s = 6(n-1) mod 11 of the main theorem of the preprint
`paper/paper.tex`, stated there for n >= 492) already gives the maximizer for every 424 <= n <= 491, and the
exact list of sizes n >= 300 where it does not. Role: part of the proof (computer-verified).

For n >= 492 the rule follows from the structural argument for large n. For 424 <= n <= 491 the unique
maximizer comes from the hull computation (`../bg_hull_dp/`, the table of maximizers), and one needs that it
is the spider given by the rule. This folder does that finite comparison.

## What is checked

`rule_vs_table.py`, in exact arithmetic (integers and `fractions.Fraction`):

1. The rule, applied as stated to every n (s = 6(n-1) mod 11; s = 0: all A_5;
   s in {1, 2}: s arms A_6; s = 3: eight A_4 for n <= 722, three A_6 for n >= 733; s = 4: seven A_4 for
   n <= 2319, four A_6 for n >= 2330; s >= 5: 11 - s arms A_4; all other arms A_5) is computed in two
   ways, from this case list and from the two candidates X_s, Y_s (the two ways of absorbing the remainder), and the two agree for
   4 <= n <= 5000.
2. The table of maximizers (`../bg_hull_dp/table_maximizers.tex`, the same file as Appendix A of the
   preprint) is parsed: 488 entries, n = 4..491, each with n vertices.
3. The value pi of every table spider, computed exactly from the closed formula pi = (prod T)(1 + R/D) for a spider,
   equals the exact maximum M_n printed by the hull computation (`../bg_hull_dp/results_dp_491.txt`).
4. Rule = table (as multisets of center branches) for every 424 <= n <= 491, and not at n = 423. The
   full list of failures for n >= 300 is printed and compared with the stated list:
   {300, 311, 322, 333} and every n = 5 (mod 11) from 302 to 423 (16 sizes); also the number of
   failures below 300 (240 of 296), the last table maximizer with a cherry at the center (n = 333) and
   the table entry at n = 311 (C A_5^28).
5. At every failure the rule spider either does not exist (negative number of A_5, only for n <= 62)
   or has an exact value strictly below M_n.

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 rule_vs_table.py
```

It reads `../bg_hull_dp/table_maximizers.tex` and `../bg_hull_dp/results_dp_491.txt`.

## Expected output

`expected_output.txt`. The run ends with `ALL CHECKS PASSED`; the key lines are

    [4] rule = table for every 424 <= n <= 491: True
        rule != table at n = 423: True   (rule: A6^2 A5^36; table: A5^31 A4^9)
        failures for n >= 300 (16): [300, 302, 311, 313, 322, 324, 333, 335, 346, 357, 368, 379, 390, 401, 412, 423]

## Runtime and memory (measured here, one core)

Under 1 s, about 12 MB.

## Re-run status

PASS (Python 3.9.6).

## Dependencies

Python 3.9 or later, standard library only.
