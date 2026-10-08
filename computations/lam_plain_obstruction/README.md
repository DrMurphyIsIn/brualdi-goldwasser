# lam_plain_obstruction -- no plain witness for lambda in [79/20, 10^6]

**Paper item:** Lemma `lem:lam-cover` (computer-verified) and Appendix C, item C13, used in Theorem
`thm:lam-plainfail` (plain witnesses fail beyond 79/20). Role: part of a proof.

## What is checked

With `F = (1/2) log(1+lambda/2)`, `y_2(a) = 1/(2+lambda a)`, `L_x = log(1+lambda x/2)`, the margin
`mu(lambda; a, b) = L_b + ((1-b)/(a-y_2(a))) (L_a - F) - 2F`.
`obstruction.py` covers `[79/20, 10^6]` adaptively by subintervals with rational endpoints; on each it
evaluates `mu` with `lambda` an interval (`mpmath.iv`, 40 digits, outward enclosures of the exact rational
endpoints) for the ten pairs `(a,b)` of the lemma in turn, until the lower bound is positive. Every pair is
asserted to satisfy `1/2 < a < b < 1` and `y_2(a) < a`. It also evaluates `mu` at six sample activities
and at `lambda = 79/20`.

## How to run

    python3 obstruction.py

## Expected output

See `expected_output.txt`: `NO PLAIN WITNESS` at the seven sample points, with
`mu(79/20; 161/200, 999/1000) = 1.7400239e-7`, and then
`lam in [79/20, 10^6]: covered by 26232 interval certificates; smallest lower bound 3.7099e-11 on
[3.96582515, 3.96582878]`. These match the remark (26 232 subintervals, smallest lower bound `3.7e-11`
near `lambda = 3.966`, `mu(79/20) in [1.740, 1.741] e-7`).

## Runtime

37 s, 16 MB.

## Dependencies

Python 3.9+, `mpmath`.

A second cover in ball arithmetic (19,776 cells; it checks the conclusion of the theorem, not the ten pairs) is in `second_implementation/`.
