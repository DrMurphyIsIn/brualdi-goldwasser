# bg_nonatom_gap/tail_values: the tail of the non-atom gap

**What it checks.** The non-atom gap at lambda = 1, the input m_c + w_c(y(A_31)) >= 0.028 for
2 <= c <= 9. **Role: prints a value that the certificates already use.**

**Provenance.** Written in October 2026.

## What is checked

Both certifying programs, `../../bg_rate/certify.py` (section B) and the second implementation
`../gapcheck.py`, take the minimum of m_c + w_c(y_a) + sigma(a) over the atoms a they list together with the
tail candidate m_c + w_c(y(A_{J+1})), with no slack (J = 30 in `certify.py`, 60 in `gapcheck.py`). Since w_c
decreases on [0, 1/3] and y(A_j) = 3/(4j+3) decreases in j, the tail candidate bounds every larger atom. The
programs do not print the tail value. This program runs the definitions of both programs unchanged (the
source of `certify.py` up to the line `J = 30`, and the source of `gapcheck.py` up to its first check), in
separate namespaces, and prints m_c + w_c(y(A_31)) for each c in interval arithmetic.

Result: the two programs agree; the values are 0.095207, 0.061707, 0.044136, 0.034826, 0.030314, 0.028829,
0.029372, 0.031340 for c = 2, ..., 9; the smallest is 0.028829, at c = 7.

## How to run

From this folder, inside `computations/` (it reads `../../bg_rate/` and `../`):

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 tail_values.py > out.txt
diff out.txt expected_output.txt
```

## Expected output

`expected_output.txt`, ending with `all tail values >= 0.028: OK`.

## Runtime and memory (measured here)

Under 1 s and 18 MB on one core (2026-10-09).

## Dependencies

Python 3.9 or later, `mpmath` (tested 1.3.0), as for the two programs it loads.
