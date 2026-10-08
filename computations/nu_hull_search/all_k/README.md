# nu_hull_search/all_k -- the matching-number search for all k, n <= 120, and its second implementation for n <= 60

**Paper item:** Lemma `lem:nu-small-cv`; Appendix C, item C16 ("The search was run for all k with n <= 120 ...
and all k with n <= 60"). Role: the runs for all k quoted in the paper, archived; the lemma itself uses only
k <= 8 (the run `../dpk215_8.txt`).

The programs are the archived ones of the parent folder, run here without the limit KMAX on the matching
number. These runs had been made before, but their outputs were not in the archive; they were re-run here in
October 2026, and both outputs are byte-identical to those of the earlier runs. `compare_all_k.py` was
written in October 2026 as an additional check.

## Files

| file | made by |
|---|---|
| `dp120_allk.txt` | `python3 ../hulldp2.py 120 > dp120_allk.txt` (all k, n <= 120) |
| `independent_dp_60.txt` | `python3 ../independent_dp.py 60 > independent_dp_60.txt` (all k, n <= 60; pure Fraction arithmetic) |
| `expected_output.txt` | `python3 compare_all_k.py` |

## What is checked

`compare_all_k.py` compares every value M(n,k) common to two of `dp120_allk.txt`, `independent_dp_60.txt`,
`../dpk215_8.txt` (k <= 8) and `../independent_dp_215_8.txt` (k <= 8), as exact rationals; checks that every
(n,k) with n <= 60 is present in both all-k runs; compares the numbers of extremal trees of `dp120_allk.txt`
with `../dpk215_8.txt`; and lists the pairs (n,k) with more than one extremal tree.

## How to run

From this folder:

```
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 ../hulldp2.py 120 > dp120_allk.txt          # about 27 min, about 8 GB (peak 7.7 GiB)
python3 ../independent_dp.py 60 > independent_dp_60.txt   # about 13 min, 1.4 GB
python3 compare_all_k.py
```

## Expected output

`expected_output.txt`:

    dp120_allk.txt: 3600 pairs (n,k), n <= 120, k <= 60
    independent_dp_60.txt: 900 pairs
    values vs independent_dp_60.txt (all k, n<=60): 900 common pairs, mismatches 0 []
    values vs ../dpk215_8.txt (k<=8): 896 common pairs, mismatches 0 []
    values vs ../independent_dp_215_8.txt (k<=8): 896 common pairs, mismatches 0 []
    every (n,k), 2<=n<=60, 1<=k<=n/2, present in both all-k runs: True
    numbers of extremal trees vs ../dpk215_8.txt: 896 pairs, differences 0
    pairs with more than one extremal tree in dp120_allk.txt: 3 [(21, 10), (49, 22), (65, 16)]
    RESULT: PASS

(The three pairs with two extremal trees have k > 8, outside the range of the lemma.)

## Runtime and memory (one core, measured here)

`hulldp2.py 120`: 1636 s, peak resident memory 8.26e9 bytes (7.7 GiB). `independent_dp.py 60`: 782 s, 1.4 GB.
`compare_all_k.py`: under 1 s.

## Dependencies

Python 3.9+, numpy (for `hulldp2.py`).
