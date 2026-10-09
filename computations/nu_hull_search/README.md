# nu_hull_search -- matching number: exhaustive hull search, k <= 8, n <= 215

**What it checks (proof):** the extremal trees with prescribed matching number k in the small range
3k-2 <= n <= n_0(k) (below the thresholds of `../nu_stability/`), by an exhaustive exact hull search.

## What is checked

For 2 <= k <= 8 and 3k-2 <= n <= 215, the maximum M(n,k) of pi(T) over trees with n vertices and
matching number k equals max_a F_k(n,a), the value of the best balanced connector-star, except at
(n,k) = (7,3) and (10,3), where M(7,3) = 9/2 and M(10,3) = 50/9.

**Method (`hulldp2.py`, helpers in `hulldp.py`).** A planted branch is summarized by
(Z, W) = (T_b, T_b y_b). If its root has degree d and children c, then Z = P + Q/d, W = P/d with
P = prod Z_c and Q = sum_c W_c prod_{c' != c} Z_{c'}; at an unplanted root with c children, pi = P + Q/c.
These maps are multilinear with nonnegative coefficients, so within each class (size, matching number,
whether the root is missed by some maximum matching) only the upper-right convex hull of the attainable
(Z, W) is needed; points on hull edges are kept, so ties survive. A floating-point filter
(tolerance 1e-9) proposes points to discard and the survivors are processed in exact rational arithmetic;
every reported maximizer is re-evaluated exactly from its tree. The filter's own tests use absolute
tolerances and do not by themselves prove that only points strictly inside the hull are discarded (the
docstring of `hulldp2.py` calls the filter conservative); every discard of the run below is certified
separately by `../hull_prefilter_check/recheck_nu.py`.
Classes with matching number above KMAX = 8 are discarded (the matching number is monotone under
taking subtrees).

**Lemma check (`check_lemma.py`).** Reads the search output and compares every M(n,k) in the range of
the lemma with the exact connector-star value `stability.cs_best` (the same function used in
`../nu_stability/`); confirms that the exceptions are exactly (7,3) and (10,3) with the stated values;
and, if present, compares all 1656 values M(n,k), k <= 8, n <= 215 with the output of the independent
implementation.

**Independent implementation (`independent_dp.py`).** Written separately from `hulldp*.py`: the same
(Z, W) recursion with its own exact upper-right hull, leaves added in closed form, pure `Fraction`
arithmetic. Its output for `python3 independent_dp.py 215 8` is `independent_dp_215_8.txt`.

Note: an early version of the search (not included) had an inverted hull test; the programs here are
the corrected ones, and the independent implementation was written to check exactly this.

## How to run

```
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 hulldp2.py 215 8 > dpk215_8.txt     # about 16 min, 2.8 GB
python3 check_lemma.py
# optional, slow (pure-Fraction arithmetic; several hours, not timed here):
python3 independent_dp.py 215 8 > independent_dp_215_8.txt
```

`hulldp2.py` writes progress lines (`# size ...`) to stderr.

## Expected output

- `dpk215_8.txt`: one line per (n, k): exact maximum, number of non-isomorphic extremal trees and
  their descriptions. (With KMAX = 8 it also prints lines for k = 9; those are not used.)
- `expected_output.txt` (output of `check_lemma.py`):
  ```
  [A] connector-star formula = exact M(n,k) on 1421 pairs (2<=k<=8, 3k-2<=n<=215); exceptions [(7, 3), (10, 3)]
  [B] M(7,3) = 9/2 (connector-star 35/8), M(10,3) = 50/9 (connector-star 265/48)
  [C] all 1656 values M(n,k), k<=8, n<=215, agree with the independent implementation
  matching-number search, k <= 8, n <= 215: OK
  ```

The search also reports that the extremal tree is unique in this range (apart from the two
exceptions); this structural output is evidence, not part of the statement checked.

## Runtime (one core, measured here)

`hulldp2.py 215 8`: 949 s, peak memory 2.8 GB. `check_lemma.py`: 2 s. `independent_dp.py 215 8`:
not re-run here (pure-Fraction arithmetic, several hours); its stored output is used for [C].

## Dependencies

Python 3.9+, numpy (float prefilter in `hulldp2.py`). Tested with Python 3.9.6, numpy 1.23.5.

## Re-run status

PASS: `hulldp2.py 215 8` re-run here; its output is byte-identical to the original run, and
`check_lemma.py` confirms the lemma. The independent implementation was not re-run here (several hours);
its stored output agrees with the re-run on all 1656 values.

## Runs for all k, and brute force (added October 2026)

`all_k/` holds the runs for all k: `hulldp2.py 120` (all k, n <= 120) and the independent
implementation `independent_dp.py 60` (all k, n <= 60), with a comparison of all values. `brute_force/` checks
every M(n,k) and the number of extremal trees for 4 <= n <= 20 by enumerating all 1,346,021 trees. See their
READMEs.

