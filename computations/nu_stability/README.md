# nu_stability -- matching number: finite range of the stability comparison

**Paper item (proof):** Lemma `lem:nu-stab-cv` (computer-verified), used in the proof of
`thm:nu-structure`(a), which gives the table of thresholds n_0(k), 2 <= k <= 10
(n_0 = 4, 24, 32, 60, 99, 149, 211, 289, 380). See also Appendix C, item C15.

## What is checked

For 2 <= k <= 10, with N_1(k) = 10, 255, 322, 464, 655, 894, 1184, 1526, 1924:

1. N_1(k) is at least the largest root of the quadratics in the proof of `thm:nu-structure`(a), in both
   cases (gamma, s) = ((m + sqrt(m+1))^2 / 4, m) and (sigma_k^2 / 2, 0), m = k-1, and at least
   max(4(m + sqrt m), sqrt m (m + sqrt m)). sigma_k is the smaller of its two closed forms, and which one
   is smaller is decided rigorously.
2. For every n with n_0(k) < n <= N_1(k)+1, the exact rational max_a F_k(n,a) (best balanced
   connector-star) exceeds 2^k (1 - gamma/(k(N+s)))^k, N = n-1, in both cases (only the first for k = 2).
3. For 3k-2 <= n <= n_0(k) the comparison fails in at least one case, so the tabulated n_0(k) is the
   least threshold this argument gives.

Arithmetic: max_a F_k(n,a) in exact rationals (`fractions.Fraction`); the bound, the roots and sigma_k
in Arb ball arithmetic (python-flint) at 256 bits; every comparison is decided rigorously in both
directions (an undecided comparison is reported).

## Files

| file | role |
|---|---|
| `nu_stab_iv.py` | the check of the lemma as stated (Arb, 256 bits). |
| `expected_output.txt` | its output. |
| `stability.py` | the first computation, in 60-digit floating point (mpmath): computes its own N_1(k) and lists the n where the comparison fails. A confirmation; the lemma rests on `nu_stab_iv.py`. |
| `stability_output.txt` | output of `python3 stability.py 2 3 4 5 6 7 8 9 10`. |

## How to run

```
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 nu_stab_iv.py
python3 stability.py 2 3 4 5 6 7 8 9 10     # optional confirmation
```

## Expected output

`nu_stab_iv.py` prints one line per k and ends with `ALL OK`. Per k: the largest roots (rounded up,
these are the values 8.7, 253.3, 319.8, 462.0, 653.1, 892.0, 1180.9, 1522.6, 1920.2 of the lemma),
`valid=True`, the failing range exactly [3k-2, n_0(k)], no undecided comparisons, and the smallest
relative margin above n_0(k); the overall smallest is 6.172e-06 at k = 8, n = 212.

`stability.py` reports the same N_1(k) and the largest failing n = 4, 24, 32, 60, 99, 149, 211, 289,
380, i.e. the table of n_0(k).

## Runtime (one core, measured here)

`nu_stab_iv.py`: 117 s, 18 MB. `stability.py 2 ... 10`: 117 s, 16 MB.

## Dependencies

Python 3.9+, python-flint (Arb), mpmath (`stability.py` only). Tested with Python 3.9.6,
python-flint 0.6.0, mpmath 1.3.0.

## Re-run status

PASS: roots, N_1(k), n_0(k) and the minimal margin 6.2e-6 (k = 8, n = 212) match the lemma.
