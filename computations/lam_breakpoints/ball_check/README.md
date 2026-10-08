# lam_breakpoints/ball_check -- second enclosure of the breakpoints lambda_3, ..., lambda_30 (ball arithmetic)

**Paper item:** Lemma `lem:lam-bp` and Appendix C, item C11. Role: a second, separately written enclosure of
the breakpoints; it adds to `../lemma_signs.py` (the signs of the lemma, Arb) and `../breakpoints.py` (the
enclosures for j <= 30, `mpmath.iv`).

`ball_breakpoints.py` was written in October 2026 as an additional check. It does not use `../rates.py` or
`../breakpoints.py`; it only reads the enclosures printed in `../expected_output.txt` to compare with them.

## What is checked

`f_j(lambda) = [ j log(1+lambda/2) + log(1 + lambda j y_c/(j+1)) ] / (2j+1)`, `y_c = 1/(2+lambda)`; `lambda_j` is
the activity where `f_j = f_{j+1}`. For each `3 <= j <= 30` the program bisects `[1/10, 3]` with exact rational
endpoints, deciding the sign of `f_j - f_{j+1}` at each rational midpoint by an Arb enclosure (python-flint,
256 bits), until the bracket is narrower than `2e-18`, and re-checks the two end signs (`+` below, `-` above;
an undecided sign stops the program). Since `f_j` and `f_{j+1}` cross exactly once
(`thm:lam-ladder`(b)), the bracket contains `lambda_j`. It then checks that

* each bracket meets the enclosure of `../breakpoints.py` (both contain the unique zero), and
* for `j = 3, ..., 6` the bracket lies inside the interval stated in `lem:lam-bp`.

## How to run

    python3 ball_breakpoints.py        # from this folder

## Expected output

`expected_output.txt`: one line per j with the bracket (22 decimals), its width (`1.3e-18`) and the size of
`|f_j - f_{j+1}|` at the two ends, each marked `VERIFIED`; then

    enclosures of breakpoints.py read: 28; overlapping the ones found here: 28
    j=3: enclosure inside the interval (0.43050, 0.43051) of the lemma: True
    ...
    ALL VERIFIED

For example `lambda_7` lies in `[1.6269120776095534467408, 1.6269120776095534479985]` and `lambda_30` in
`[2.7685654742615735059066, 2.7685654742615735071642]`.

## Runtime and memory (one core, measured here)

0.1 s, 18 MB.

## Dependencies

Python 3.9+, python-flint (0.6.0 tested).
