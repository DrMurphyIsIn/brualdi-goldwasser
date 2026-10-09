# deg_certificates -- typed-potential certificates for bounded maximum degree

**What this is (proof):** typed-potential certificates for trees of bounded maximum degree:
- hand potentials for Delta = 3, 4, checked by computer, and
- linear-programming certificates for Delta = 5, 6, 7, checked in interval arithmetic.
Together they give the upper bound on the exact growth rate of trees with maximum degree at most Delta,
for 3 <= Delta <= 7.

## What is checked

For each Delta, branches are typed (leaf `L`, cherry `C`/`K`, for Delta >= 6 the branch `A5`/`C5`, and
intervals of the two message windows `I_Delta` (= `A`) and `J_Delta` (= `B`)), each type has a constant
theta (called `k` in the code), and every *rule* (a multiset of 1..Delta-1 child types with a possible
parent type) must satisfy the one-step Bellman inequality
`F + sum theta(children) - theta(parent) >= max over box corners of B_m`.

- identity rules (`L -> C`, `C^5 -> A5`) hold with equality;
- spine rules (Delta-2 cherries plus one further type) reduce, by the spine identity, to a comparison of
  two constants;
- generic rules are evaluated at every corner of the box in interval arithmetic and must have
  strictly positive slack.

| Delta | rules | smallest generic slack | paper |
|---|---|---|---|
| 3 | 14 (1 identity, 4 spine, 9 generic) | 1.0e-4 (`JJ -> J`) | as stated, with the full slack table |
| 4 | 34 (1 identity, 4 spine, 29 generic) | 3.1e-5 (`CJJ -> J`), then 4.8e-5, 9.4e-5; all others > 3.4e-3 | as stated |
| 5 | 1116 | 3.7e-4 | as stated |
| 6 | 4505 | 6.0e-4 | as stated |
| 7 | 12753 | 1.6e-4 | as stated |

Smallest nonzero slack overall: 1.0e-7 (a spine comparison).

## Files

| file | role |
|---|---|
| `explicit_small.py` | Delta = 3, 4: the hand potentials for Delta = 3, 4 (theta_I = -0.0813, -0.0391; theta_J = theta_C), all rules, mpmath interval arithmetic at 256 bits. Imports `verify.py`. |
| `cert34.py` | Delta = 3, 4: second interval check (mpmath `iv`, 60 digits) that prints every rule with its kind (identity / spine / generic) and slack, with the type labels `L, C, I, J`. This is the slack table of the Delta = 3, 4 certificates. |
| `verify.py`, `potential.py` | Delta = 5, 6, 7: builds the types (four intervals per window), solves the linear program for theta (untrusted, scipy), rationalizes, re-imposes the spine comparisons exactly, and verifies every rule in mpmath interval arithmetic at 256 bits. With `--save` it writes `out/cert_D<Delta>_K4.json`. |
| `certificates/cert_D{5,6,7}_K4.json` | the certificates (types with rational endpoints, rational theta). Re-running `verify.py D 4 --save` reproduces them exactly (checked here). |
| `indep_check.py` | independent checker, written from the mathematical statement only (does not import `verify.py`/`potential.py`): Arb ball arithmetic (python-flint) at 300 bits, its own rule enumeration under the typing stated in the paper, exact check that the target intervals cover the parent ranges, all box corners. Checks the Delta = 3, 4 hand potentials and reads the three JSON certificates. |

**Rule counts.** `verify.py` enumerates 4843 and 13115 rules for Delta = 6, 7: it adds redundant
targets `C`/`A5` whenever a parent range contains 1/3 or 3/23, and it types every branch with message
3/23 as `A5`. The paper types only the branch `C^5` itself as `A5`, so a branch such as `L L C C`
(message 3/23 as well) gets an interval type and the rule `LLCC -> tau` is needed. `indep_check.py`
uses exactly the paper's typing and finds 1116, 4505 and 12753 rules, the numbers stated for the
Delta = 5, 6, 7 certificates, all of which hold. For Delta = 5 both counts are 1116.

The optional mode `python3 indep_check.py upper` also checks the upper-bound certificates for
Delta = 8..12 (two-sided brackets for the growth rate, not used in any proof); those certificate files are
not included here.

## How to run

```
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 explicit_small.py
python3 cert34.py
python3 verify.py 5 4        # add --save to rewrite out/cert_D5_K4.json
python3 verify.py 6 4
python3 verify.py 7 4
python3 indep_check.py
```

Expected output: `expected_output.txt` (all six commands in this order). Each `verify.py` run ends with
`RESULT: VERIFIED`; `indep_check.py` ends with `TOTAL FAILS 0`.

## Runtime (one core, measured here)

`explicit_small.py` 0.3 s; `cert34.py` < 1 s; `verify.py` 1.6 s / 9.5 s / 45 s for Delta = 5 / 6 / 7
(peak memory 65 / 81 / 125 MB); `indep_check.py` 3.1 s (19 MB).

## Dependencies

Python 3.9+, mpmath, numpy and scipy (`verify.py` only, for the untrusted linear program),
python-flint (`indep_check.py`). Tested with Python 3.9.6, mpmath 1.3.0, numpy 1.23.5, scipy 1.13.1,
python-flint 0.6.0.

## Re-run status

PASS: all rule counts, slacks and the Delta = 3 slack table match the paper.

Note on rule counts: the counts 1116, 4505, 12753 stated in the paper for Delta = 5, 6, 7 are those reported by indep_check.py, which also checks the rule LLCC->tau. verify.py enumerates rules with a different convention (4843 and 13115 for Delta=6,7) and does not check LLCC->tau.
