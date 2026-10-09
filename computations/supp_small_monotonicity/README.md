# supp_small_monotonicity: monotonicity certificate on (0, 0.198]

**What this is.** A second certificate for small activities: a rigorous monotonicity certificate on
(0, 0.198], by interval arithmetic on 114 contiguous boxes.

**Role.** Confirmation of part (B) of the uniform ceiling theorem for small activities; not used in its
proof.

## What is checked

For every planted branch b and every s in [0, 0.198],
l'(b) := d/ds [log T_b(s) - |b| f_3(s)] <= 0, with equality only for the arm A_3 ("Lemma S" in the
program). The certificate is a typed induction on l' and on the auxiliary bound 0 <= z_b <= y_b
("Lemma Z"): the exact types are all 85 planted branches with at most 7 vertices and all arms; a general
branch of root degree e <= 12 is classed by e and by a bin of width 1/10 of a lower bound on its
children's message sum; one class per degree 13 <= e <= 300; an analytic tail beyond. Exact types are
enclosed on each s-box by mean-value forms with interval forward-mode differentiation (`mpmath.iv`,
30 digits); the dynamic program over children runs in double precision on outward-rounded inputs with a
cushion of 1e-9. The docstring of `lemmaS_certify.py` states it in full.

The paper states 114 contiguous boxes covering [0, 0.198], of width 0.001 on [0, 0.03] and 0.002
beyond.

Supporting checks:
- `lemmaS_hyp_check.py`: the induction hypothesis on all 53 272 planted branches with at most 14 vertices,
  with exact cavity values at several activities.
- `lemmaS_negctl.py`: negative controls (f_3' lowered by 1e-3, slack 0, a box beyond the threshold, A_3's
  value raised); the baseline passes and every variant fails (the slack control fails only in witness
  generation, as its docstring explains).

## How to run

```sh
sh run_all.sh
python3 lemmaS_hyp_check.py
python3 lemmaS_negctl.py
```

## Expected output

Each chunk ends `s in [a, b]: CERTIFIED; N boxes; ...` with N = 15, 15, 15, 15, 15, 15, 12, 12
(total 114). See `expected_output.txt`.

## Runtime and memory (measured here)

Measured here (one thread per chunk): 8 chunks, 3 242 s in all (about 54 min sequentially; chunks
are independent), longest 735 s; peak memory 22 MB. `lemmaS_hyp_check.py` 163 s, `lemmaS_negctl.py`
288 s.

Re-run result: PASS. Box counts 15, 15, 15, 15, 15, 15, 12, 12 (total 114), every chunk CERTIFIED;
53 272 branches with no violation at the six activities; negative controls behave as described above.

## Dependencies

Python 3.9 or later, `mpmath` (1.3.0). `exp1_ceiling.py` supplies the enumeration of rooted trees.
