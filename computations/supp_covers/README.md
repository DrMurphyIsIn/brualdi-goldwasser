# supp_covers: witness covers of the activity range [0.1, 3.22]

**Paper item.** Supplement, section "Witness covers on [0.1, 3.22]" (`sec:lam-covers`) and the remark
"programs and independent check" (`rem:lam-uniform`).

**Role.** Confirmation route for part (B) of the uniform ceiling theorem (`thm:lam-uniform`). The proof of
(B) in the main paper uses the two explicit witnesses W_1, W_2 (`sec:lam-partB`, certified in
`computations/lam_partB_rows/`) and none of these cells.

## What is checked

For every activity lambda in [0.08, 3.22] the programs exhibit a tight leaf-exempt (pooled) witness
`U_lambda` on [0, 1/2] and verify, in outward-rounded interval arithmetic (`mpmath.iv`), the Bellman
inequality

    Phi = -k F* + m U(ybar) + log(1 + lambda R/d) - F* - U(1/(d + lambda R)) <= 0,   d = k+m+1, R = k + m*ybar,

for every type (k leaf children, m non-leaf children, mean message ybar), other than the cherry, which
is exact. lambda and ybar are both interval variables; boxes are bisected on failure. Tails in k and m and
the arms covered by the arm lemma are discharged by exact lemmas whose hypotheses are checked on each
lambda-box. F* = max_j f_j(lambda) is enclosed on each box by `Fstar_point` and `eps_enclosure` in
`certify_arm.py` (shared by the other three programs).

| program | witness | lambda range used | cells (paper) |
|---|---|---|---|
| `certify_pow.py` | power shoulder (p = 3/2) | [0.1, 0.47] (also run on [0.08, 0.1]) | 1 169 430 |
| `certify_quad_t08.py` | quadratic shoulder, theta = 4/5 | [0.47, 0.8] | 736 140 |
| `certify_quad.py` | quadratic shoulder, theta = 7/10 | [0.8, 1.6] | 178 431 |
| `certify_arm.py` | three-piece linear witness | [1.6, 3.22] | 7 007 057 |

Total about 9.09 million cells. The [0.08, 0.1] chunk (707 714 cells) is extra overlap with the
typed induction on (0, 0.1] and is not counted in the paper's 9.09 million.

## How to run

Each program takes `LAM0 LAM1 STEP` (the lambda-range and the initial lambda-box width). Run from this
directory, single-threaded:

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
sh run_all.sh            # all 20 chunks, sequentially; writes logs/*.log
```

or one chunk, for example `python3 certify_arm.py 3.2 3.22 0.0005`. The chunks and step sizes are those
listed in `run_all.sh`. Each chunk ends with a line
`lam in [a, b]: CERTIFIED; N boxes; ...`; any failure is reported and the line says otherwise.

## Expected output

`expected_output.txt` holds the last line of each chunk from the run made for this directory, and the
full logs of that run are summarized there with runtimes. The box counts must sum to the numbers in the
table above.

## Runtime and memory (measured here)

Measured here (one thread per chunk, Apple M3 Ultra): 20 chunks, 3 230 s in all (about 54 min run
sequentially; the chunks are independent, so they can run in parallel). The longest chunk is
`certify_arm.py 3.2 3.22 0.0005` (933 s, 5 424 557 boxes). Peak memory under 31 MB per chunk.

Re-run result: PASS. Every chunk CERTIFIED with the same box counts as the original run; the sums are
1 169 430 (power, [0.1, 0.47]), 736 140 (theta = 4/5), 178 431 (theta = 7/10) and 7 007 057 (linear),
total 9 091 058, as stated in the paper (about 9.09 million).

## Dependencies

Python 3.9 or later, `mpmath` (tested with 1.3.0).
