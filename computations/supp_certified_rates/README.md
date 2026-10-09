# supp_certified_rates -- certified rates at 26 activities (28 certificates)

**What this is:** certified growth rates of the weighted family at 26 isolated rational activities
(28 witness certificates), with their programs and an independent re-check. Role: part of a proof in a
confirmation route (the rate at isolated activities; the uniform ceiling theorem contains every row).

## What is checked

At each rational activity `lambda` of the table, a convex piecewise-linear message potential `h` (a
*witness*) is verified to satisfy the Bellman inequality of the plain form (19 activities, `certify_plain.py`)
or of the leaf-exempt form (9 activities, `certify_leafx.py`), which proves that the rate is `rho = e^F` with
`F` the log-weight per vertex of the best atom. The checks: nondecreasing slopes, the tail lemma
(which fixes `M`, resp. `N`), and the Bellman inequality on cells for every `m <= M` (resp.
`k+m <= N`), each cell decided at its two endpoints after a tangent-line bound for the logarithm, bisecting
on failure. Node values pinned by the theory are exact formal numbers `c + sum a_p log p` (`formal.py`); at
the forced equality points the value must vanish *formally* (cancellation of logarithms after prime
factorization); every other endpoint value must be negative in `mpmath.iv` at 60 digits.

The witness itself is untrusted input: it is produced by a floating-point linear program
(`potential_lp.py`, `potential_leafx_lp.py`, using `scipy.optimize.linprog`).

## Files

* `certify_plain.py`, `certify_leafx.py` -- the certifiers (LP for the witness, then rigorous check).
* `formal.py` -- exact formal logarithms with interval enclosures.
* `potential_lp.py`, `potential_leafx_lp.py` -- the untrusted LPs.
* `certificates/cert_*.json` -- the 28 recorded certificates (one per row of the table of certified rates) (witness nodes as exact
  rationals, node values as formal numbers, and the counts).
* `recheck_recorded.py` -- feeds each recorded witness to the unchanged `certify()` routine of the two
  certifiers (bypassing the LP) and compares the counts with the record. Written for this release; it adds
  no checking logic of its own.
* `run_all.sh` -- regenerates all 28 witnesses from the LP and certifies them.

## How to run

    python3 recheck_recorded.py      # recommended: re-verifies the 28 recorded certificates
    sh run_all.sh                    # regenerates witnesses with your LP solver; writes out/

## Expected output

`expected_output.txt` (from `recheck_recorded.py`): all 28 lines `CERTIFIED ... matches record`, and
`28 recorded certificates re-verified; 28 match the recorded counts`. The node counts, `M` (`N` for the
leaf-exempt form) and cell counts are exactly those of the table of certified rates, e.g. `lambda = 16/5`: 17 nodes,
`M = 1264`, 24 643 cells; `lambda = 1` (plain): 16 nodes, `M = 31`, 513 cells; `lambda = 100`
(leaf-exempt): 4 nodes, `N = 25`, 1 403 cells.

`expected_output_lp_run.txt` (from `run_all.sh` on the machine below) is for information only. The LP is
not deterministic across solvers and versions, so regenerated witnesses differ from the recorded ones and
give different node and cell counts (all valid certificates when they pass). With scipy 1.13.1, 27 of 28
regenerated witnesses certify; at `lambda = 5/2` with the default LP grid (70 nodes) the LP returned a
witness that touches zero near `y = 0.99930` at `m = 1` and fails to certify (an untrusted-input failure,
not a failure of the statement). With LP grids of 50, 60, 80 or 100 nodes (`python3 certify_plain.py 5 2 60`)
the regenerated witness certifies, and the recorded witness certifies (`recheck_recorded.py`).

## Runtime and memory (single thread, one core)

* `recheck_recorded.py`: 43 s in total, 122 MB.
* `run_all.sh`: about 3 min in total. The LPs are dense and memory-hungry: the plain runs need up to 3.6 GB
  (`lambda = 16/5`), the leaf-exempt runs 5-7 GB each and about 20 GB at `lambda = 100`. Use
  `recheck_recorded.py` on a machine with less memory.

## Dependencies

Python 3.9+, `mpmath`, `sympy` (prime factorization), and for `run_all.sh` also `numpy` and `scipy`.
