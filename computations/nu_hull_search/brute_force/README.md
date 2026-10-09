# nu_hull_search/brute_force -- brute force over all trees with 4 <= n <= 20

**What it checks:** every M(n,k) (maximum of pi over trees with n vertices and matching number k) and the
number of extremal trees for 4 <= n <= 20, by enumerating all non-isomorphic trees. Role: a check of the values M(n,k) of the hull search, and of the number of extremal trees, by a
method that does not use the hull lemma.

`brute_force.py` was written in October 2026 as an additional check (a brute force over the same range had been
run earlier, but its program was not archived).

## What is checked

For every n with 4 <= n <= NMAX and every tree T on n vertices (`networkx.nonisomorphic_trees`): pi(T), the sum over
matchings of prod 1/(deg u deg v), by the two-state tree DP in exact Fraction arithmetic, and the matching number
nu(T) by the leaf-greedy rule. For each (n, k) it records M(n,k) = max pi over the trees with nu = k and the number of
non-isomorphic trees attaining it, and compares (value, number) with `../dpk215_8.txt` (k <= 8) and with
`../all_k/dp120_allk.txt` (all k, n <= 120), when present.

## How to run

From this folder (after `../all_k/dp120_allk.txt` exists, for the all-k comparison):

    python3 brute_force.py 20

## Expected output

`expected_output.txt`: one line `n=.. k=.. max=.. count=..` per pair, then

    # trees enumerated: 1346021; pairs (n,k): 98
    # compared with dpk215_8.txt (k<=8): 94 pairs; with all_k/dp120_allk.txt: 98 pairs
    # RESULT: PASS (values and numbers of maximizers agree)

Every extremal tree with n <= 20 is unique up to isomorphism (count=1 on every line).

## Runtime and memory (one core, measured here)

239 s, 35 MB.

## Dependencies

Python 3.9+, networkx (3.2.1 tested).
