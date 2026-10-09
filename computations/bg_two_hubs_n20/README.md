# bg_two_hubs_n20: the two-hub tree on 20 vertices

**Paper item.** Section 4, the paragraph after Corollary `cor:bg-shape` (local exchanges alone do not exclude
two hubs). **Role: confirmation only**; no proof uses it.

**Provenance.** Written in October 2026.

## What is checked

T0 is the tree made of two adjacent vertices, each carrying two cherries and one arm A_2 (n = 20). An *edge
exchange* deletes one edge of a tree and reconnects the two components by another edge. The claim is that T0
is not a maximizer, but beats (strictly) every other tree obtained from it by at most three edge exchanges.

1. pi(T) = per L(T) / prod deg(v) is computed exactly (Python fractions) by the matching-sum recursion; the
   recursion is first compared with the permanent itself (Ryser's formula, exact integers) on all 94 trees
   with 2 to 9 vertices.
2. All 823,065 trees on 20 vertices (`networkx.nonisomorphic_trees`) are evaluated exactly.
   pi(T0) = 124461/2048. Exactly three trees have a larger value, and no other tree has the same value.
3. The exchange ball of radius 2 around T0 (3,048 trees up to isomorphism) is disjoint from the exchange ball
   of radius 1 around each of the three better trees. So each better tree is at exchange distance at least 4
   from T0, and T0 beats every other tree within three exchanges.

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 two_hubs_n20.py > out.txt
diff out.txt expected_output.txt
```

The running time is printed on standard error and is not part of the expected output.

## Expected output

`expected_output.txt`. The last two lines are
`every better tree is at exchange distance >= 4 from T0: True` and
`T0 beats every other tree within three edge exchanges: True`.

## Runtime and memory (measured here)

128 s and 28 MB on one core (2026-10-09).

## Dependencies

Python 3.9 or later, `networkx` (tested 3.2.1).
