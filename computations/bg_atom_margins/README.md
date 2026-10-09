# bg_atom_margins: atom values, the six atom margins of the high-degree case, g(A_4) < 1/960

**What it checks:** at lambda = 1, the values h(y), sigma, g of the atoms (leaf, cherry, A_j); for the
high-degree case (root degree >= 24) the six margins g - mu_0 (y - q) for the leaf, the cherry and
A_1, ..., A_4, and delta_0 - mu_0^2/(4 kappa) > 0.012445; the bound g(A_4) < 1/960 used for the benchmark
spider; the degree >= 24 ceiling log(26/23) - 0.012445 < 0.1101574 used in the comparison with explicit
spiders; the deficits g(A_4), g(A_6) quoted, rounded and truncated, for the best spider. Role: part of the proof (numerical inputs of
hand proofs).

## What is checked

`atom_margins.py` computes everything from the exact definitions at lambda = 1
(F* = log(621/64)/11, q = 3/23, beta = 2F* - log(3/2), kappa = beta/(1/3 - q)^2, gamma = (3/2)(F* - beta),
the potential h, the atoms with T(A_j) = (3/2)^j (4/3 - 1/(3(j+1))) and y(A_j) = 3/(4j+3),
g = |b| F* - log T, sigma = g - h(y), mu_0 = 23/624 = 1/(24(1+q)), delta_0 = 0.01426), in two arithmetics:
`mpmath.iv` (outward rounding, 256 bits) and `python-flint` Arb balls (300 bits). Every claim is decided on
the exact binary endpoints of the enclosure, in both arithmetics:

- the 8 tabulated atoms (leaf, cherry, A_1..A_4, A_6, A_7): each printed 7-decimal value of
  h(y), sigma and g is the correct rounding (the zeros at the leaf, the cherry and A_5 are identities);
- the six margins of the high-degree case are positive and their printed values (0.17453, 2.29e-4, 0.04915,
  0.01609, 0.00400, 1.43e-5) are the correct roundings; the smallest, at A_4, is 1.39% of g(A_4);
  y(A_4) - q = 12/437; mu_0 rounds to 0.0368590;
- gamma > mu_0, q + mu_0/(2 kappa) < 1/3 (about 0.229), and delta_0 - mu_0^2/(4 kappa) > 0.012445
  (value 0.01244580...);
- g(A_4) < 1/960 (g(A_4) = 0.00102642...), log(26/23) - 10/960 > 0.11218, and
  log(26/23) - 0.012445 < 0.1101574;
- g(A_4) and g(A_6) round to 0.0010264 and 0.0015153 and have leading digits 0.0010264... and
  0.0015152... (g(A_6) = 0.00151528502...).

## How to run

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 atom_margins.py
```

## Expected output

`expected_output.txt`: one `PASS` line per check, for each of the two arithmetics, ending with
`ALL CHECKS PASSED (both arithmetics)`.

## Runtime and memory (measured here, one core)

Under 1 s, about 23 MB.

## Re-run status

PASS (Python 3.9.6, mpmath 1.3.0, python-flint 0.6.0). The check of the leading digits of g(A_6) caught a
misprint: a truncated value had been written `0.0015153...` for a number whose digits are 0.0015152850...;
it now reads `0.0015152...` (the rounded value 0.0015153 is correct).

## Dependencies

Python 3.9 or later, `mpmath` (>= 1.3), `python-flint` (>= 0.6).
