# supp_cherry_checks/lemma_exact: the unmatched-vertices lemma in exact arithmetic

**Paper items.** Lemma `lem:lam-monomer` (Section 7; the sentences after the proof of part (A) that report
checks), and the supplement remark `rem:lam-cherry-check`. **Role: confirmation only**; the lemma is proved by
hand and no proof uses this.

**Provenance.** Written in October 2026, from the statement of the lemma. It shares no code with
`../lemma_M_check.py` (it has its own enumeration of rooted trees and its own cavity computation).

## What is checked

For a planted branch b with n vertices (the root has one extra edge to its parent, so every vertex has degree
equal to its number of children plus one) and the monomer-dimer model with edge activities lam/(d_u d_v), the
lemma says

    S(b, lam) = sum over vertices v of P(v unmatched) >= 2n/(2+lam)    (lam >= 2).

The program computes S(b, lam) - 2n/(2+lam) exactly (Python fractions), by a downward and an upward pass of
the cavity recursion.

- Part 1: all 53,272 planted branches with at most 14 vertices at lam in {2, 3, 10, 100, 10^6}. No violation;
  the slack is exactly 0 only for the cherry (it is 0 for the cherry at every lam); the smallest slack of the
  other branches is attained at n = 4.
- Part 2: all 7,813 planted branches with at most 12 vertices at lam in {1/2, 7/10, 4/5, 1}. The lemma holds
  at 4/5 and 1 and fails at 7/10 (one branch, n = 11, slack -0.003948) and at 1/2 (four branches). So the
  lemma is a large-activity statement, as the paper says.

The branch counts are the numbers of rooted trees with at most 14 and at most 12 vertices
(sum of OEIS A000081).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 lemma_exact.py > out.txt
diff out.txt expected_output.txt
```

## Expected output

`expected_output.txt` (11 lines).

## Runtime and memory (measured here)

85 s and 21 MB on one core (2026-10-09).

## Dependencies

Python 3.9 or later, standard library only.
