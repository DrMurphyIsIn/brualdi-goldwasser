# bg_M7_table/exchange_test -- the exchanges (M1)-(M7) tested on all trees with n <= 18

**What it checks:** that each local exchange (M1)-(M7) strictly increases pi, tested on explicit trees.
Role: a test on explicit trees; the exchanges are proved by hand, with their polynomials checked by
`../m7_table.py`.

The program `exchange_test.py` was written in September 2026, and is archived here in October 2026,
with its docstring rewritten, its labels renamed to the current
(M1)-(M7) (an earlier draft numbered the exchanges differently) and a final line counting instances and
failures added. Its output below is from a run made here.

## What is checked

For every tree with 4 <= n <= NMAX vertices (`networkx.nonisomorphic_trees`) and every vertex p at which the
hypotheses of an exchange (M1)-(M7) hold, the exchange is carried out on the tree, the result is
checked to be a tree on n vertices, and pi is computed before and after by a matching DP on the tree (not by
the cavity formula used in the proof): in floating point, and in exact Fraction arithmetic whenever the
relative gain is below 1e-9. A `FAIL` line would be printed for an exchange that does not strictly increase
pi. Labels in the output:

| output label | exchange |
|---|---|
| M1, M2, M3, M5, M6 | (M1), (M2), (M3), (M5), (M6) |
| M4 (balance) | (M4) |
| M7(i), M7(ii), M7(iv), M7(v) | (M7)(i), (ii), (iv), (v) |
| M7(iii) and (vi), two stalks | (M7)(iii) and the exchanges {[A_j],[A_k]} -> N_jk of (M7)(vi) |
| M7(vi), stalk and cherry | the three exchanges {[A_j], C} of (M7)(vi) |

Counts are cumulative over n.

## How to run

    python3 exchange_test.py 18

## Expected output

`expected_output.txt`: per n the number of trees and, per exchange, the cumulative number of instances and
the smallest relative gain. The last line is

    total instances 929524 failures 0

## Runtime and memory (one core, measured here)

91 s, 30 MB.

## Dependencies

Python 3.9+, networkx (3.2.1 tested).
