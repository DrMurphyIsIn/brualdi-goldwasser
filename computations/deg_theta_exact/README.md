# deg_theta_exact: the exact constants of the bounded-degree certificates, and the rule lists

**What this checks:** the typed-potential certificates for bounded maximum degree: for Delta = 3, 4 the
printed theta values of the hand potentials; for Delta = 5, 6, 7 that the target intervals cover the parent
ranges exactly, and the rule counts 1116, 4505, 12753. Role: a re-check of part of a proof (the
certificates themselves are verified in `../deg_certificates/`).

## What is checked

`theta_exact.py`:

1. theta_L = F - log(1 + eta) and theta_C = 2F - log(3/2) - log(1 + eta/3) (and, for Delta = 6, 7,
   theta_{A5} = g(A_5) - log(1 + 3 eta/23)) are enclosed in Arb (300 bits) from their definitions. The
   printed values for Delta = 3, 4 (theta_L = -0.0476, theta_C = -0.1000 for Delta = 3; 0.0149, -0.0684
   for Delta = 4) are their roundings to four decimals; they are used exactly (as enclosures) by the
   programs. For Delta = 6, 7 the definition of theta_{A5} makes the identity rule C^5 -> A_5 exact.
2. theta_I: the printed -0.0813 (Delta = 3) and -0.0391 (Delta = 4) are exact decimals, used as the exact
   rationals -813/10000 and -391/10000 by `../deg_certificates/explicit_small.py` and `indep_check.py`
   (read from their source). `../deg_certificates/cert34.py` uses the binary doubles nearest to them
   (they differ by 2.7e-18 and 2.8e-18), which does not affect any of its strict slacks (all >= 3.1e-5).
3. For Delta = 5, 6, 7 the exact theta of every interval type, read from
   `../deg_certificates/certificates/cert_D{5,6,7}_K4.json`, are printed (table below).
4. An independent enumeration of the rules under the typing stated in the paper (types L, C, for
   Delta >= 6 the branch A_5 = C^5 itself, and the intervals; a rule is a multiset of 1..Delta-1 child types
   with every possible parent type: C for the single child L, A_5 for C^5, otherwise every interval type
   meeting the exact parent range [1/(m+1+Rmax), 1/(m+1+Rmin)]). In exact rational arithmetic: the
   partitions of I_Delta and J_Delta are contiguous with the exact window endpoints; every parent range lies
   in its message window (I_Delta for one non-leaf child, J_Delta for two or more children);
   every parent range is covered exactly by its targets; and the numbers of rules are 14, 34, 1116, 4505,
   12753, as stated. For Delta = 6, 7 the branch L L C C (message 3/23) gets an interval type, as stated.

## Exact constants (Delta = 5, 6, 7)

Types `B0..B3` partition J_Delta and `A0..A3` partition I_Delta (`K` = the cherry C, `C5` = A_5 in the
certificate files). theta_L, theta_C, theta_{A5} are defined by logarithms (decimal values shown);
all other theta are the exact dyadic rationals of the certificates.

| Delta | type | interval | theta (exact) | decimal |
|---|---|---|---|---|
| 5 | L | {1} | F - log(1 + eta) | 0.0532475443 |
| 5 | C | {1/3} | 2F - log(3/2) - log(1 + eta/3) | -0.0508871170 |
| 5 | B0 | [1/9, 14/87] | -27975543973/549755813888 | -0.0508872180 |
| 5 | B1 | [14/87, 55/261] | -27975543973/549755813888 | -0.0508872180 |
| 5 | B2 | [55/261, 68/261] | -39462139399/1099511627776 | -0.0358906067 |
| 5 | B3 | [68/261, 9/29] | -40826752329/1099511627776 | -0.0371317149 |
| 5 | A0 | [2/5, 159/380] | -7269216303/1099511627776 | -0.0066113137 |
| 5 | A1 | [159/380, 83/190] | -17959882201/1099511627776 | -0.0163344177 |
| 5 | A2 | [83/190, 173/380] | 1720728667/549755813888 | 0.0031299872 |
| 5 | A3 | [173/380, 9/19] | 16477611691/1099511627776 | 0.0149863005 |
| 6 | L | {1} | F - log(1 + eta) | 0.0788352501 |
| 6 | C | {1/3} | 2F - log(3/2) - log(1 + eta/3) | -0.0401083928 |
| 6 | A5 | {3/23} | g(A_5) - log(1 + 3 eta/23) | -0.0401083928 |
| 6 | B0 | [1/11, 113/770] | -22049877673/549755813888 | -0.0401084938 |
| 6 | B1 | [113/770, 78/385] | -21521038419/549755813888 | -0.0391465408 |
| 6 | B2 | [78/385, 199/770] | -26968315/1073741824 | -0.0251162006 |
| 6 | B3 | [199/770, 11/35] | -14020175581/549755813888 | -0.0255025508 |
| 6 | A0 | [2/5, 193/460] | 3645886753/549755813888 | 0.0066318294 |
| 6 | A1 | [193/460, 101/230] | -681914609/274877906944 | -0.0024807909 |
| 6 | A2 | [101/230, 211/460] | 9582506645/549755813888 | 0.0174304780 |
| 6 | A3 | [211/460, 11/23] | 39608147259/1099511627776 | 0.0360234001 |
| 7 | L | {1} | F - log(1 + eta) | 0.0970483805 |
| 7 | C | {1/3} | 2F - log(3/2) - log(1 + eta/3) | -0.0329149373 |
| 7 | A5 | {3/23} | g(A_5) - log(1 + 3 eta/23) | -0.0332387302 |
| 7 | B0 | [1/13, 73/533] | -36546481369/1099511627776 | -0.0332388312 |
| 7 | B1 | [73/533, 105/533] | -35281272929/1099511627776 | -0.0320881308 |
| 7 | B2 | [105/533, 137/533] | -15331210287/549755813888 | -0.0278873091 |
| 7 | B3 | [137/533, 13/41] | -19598827929/1099511627776 | -0.0178250302 |
| 7 | A0 | [2/5, 227/540] | 2232343817/137438953472 | 0.0162424390 |
| 7 | A1 | [227/540, 119/270] | 8007167483/1099511627776 | 0.0072824764 |
| 7 | A2 | [119/270, 83/180] | 29965309731/1099511627776 | 0.0272532904 |
| 7 | A3 | [83/180, 13/27] | 3460677303/68719476736 | 0.0503594827 |

For Delta = 3, 4 (hand potentials): theta_I = -813/10000 resp. -391/10000 (exact), theta_J = theta_C,
theta_L = -0.0476181928 resp. 0.0149315677, theta_C = -0.1000106411 resp. -0.0683953681 (defined by
logarithms; ten decimals shown).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 theta_exact.py
```

It reads `../deg_certificates/certificates/*.json` and the source of three programs in
`../deg_certificates/`.

## Expected output

`expected_output.txt`, ending with `ALL CHECKS PASSED`.

## Runtime and memory (measured here, one core)

Under 1 s, about 19 MB.

## Re-run status

PASS (Python 3.9.6, python-flint 0.6.0): printed values are correct roundings; the rule counts
14, 34, 1116, 4505, 12753 and the exact coverage are reproduced.

## Dependencies

Python 3.9 or later, `python-flint`.
