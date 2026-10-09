# lam_first_order -- sharpest first-order degree potential (Randic limit)

**What it checks:** in the Randic limit (lambda -> 0) of the weighted family pi_lambda, the sharpest
first-order degree potential, recomputed by exact value iteration. Role: confirmation only; no proof uses it.

## What is checked

Exact value iteration (Python `fractions`) of
`V(d) = (d-1) max_{e>=1} ( V(e) + 1/(d e) ) - 15/56`, `V(1) = -15/56`, over degrees `d <= D` (default 40),
where `V(d) = -phi(d)` is the first-order (lambda -> 0) deficit of a planted branch with root degree `d`.
The script truncates the degrees at `D`; the tail is an identity handled by hand.

## How to run

    python3 first_order_dp.py        # D = 40
    python3 first_order_dp.py 200    # larger truncation, same values

## Expected output

See `expected_output.txt`: converges after 3 iterations, with `phi(2)=1/28`, `phi(3)=1/168`, `phi(4)=0`,
`phi(5)=3/280`, `phi(6)=5/252`, `phi(7)=phi(8)=1/56` (printed as `V* = -phi`), and `sup_d V*(d) = 0` at `d = 4`.
These are the stated values.

## Runtime

Under 0.1 s, 12 MB.

## Dependencies

Python 3.9+ standard library only.
