# Independent check with Comparator

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's tool for checking a proof
against a separately written statement. Each challenge here restates, importing **only Mathlib**, the
definitions a headline theorem depends on (the weighted matching sum π_λ with Mathlib degrees, the maximum
M_n over the trees on `Fin n`, planted branches and the cavity recursion, ρ, witnesses, the arms and the
best arm rate f*) and the theorem itself, with
`sorry`. The solution, `CherrySolution.lean`, is just `import LeanCherry`. For each configuration
Comparator confirms that the solution's definitions and statements are *identical* to the challenge's,
that the proofs use only `propext`, `Quot.sound` and `Classical.choice`, and that the exported proofs are
accepted both by Lean's kernel and by [nanoda](https://github.com/ammkrn/nanoda_lib), an independent
implementation of the Lean kernel in Rust.

| configuration | challenge | theorems |
|---|---|---|
| `headline` | `ChHeadline.lean` | `pi_lam_le_tree` |
| `lambda1` | `ChLambda1.lean` | `pi_one_eq_permanent_tree` (with L = D − A and Mathlib's `Matrix.permanent`) |
| `graph` | `ChGraph.lean` | `pi_lam_lt_tree`, `Mn_le`, `Mn_ge`, `Mn_rate` |
| `branch` | `ChBr.lean` + `ChBranch.lean` | `Br.Tl_eq_cherry_iff`, `rho_eq`, `rho_isGreatest`, `rho_isLUB` |
| `oneblock` | `ChOneBlockBr/Tl/Graph.lean` + `ChOneBlock.lean` | `Mn_le_rho`, `Mn_ge_block`, `Mn_tendsto_rho`, `rhoB_eq_cherry`, `rhoB_le`, `rhoSet_bdd`, `Br.Tl_le_pow` |
| `witness` | `ChOneBlockBr/Tl/Graph.lean` + `ChWitness.lean` | `Witness.mt_main_a`, `Witness.mt_main_b`, `Witness.mt_main_c` (the definition of a witness, and the witness theorem (a)-(c)) |
| `window` | `ChWitness.lean` + `ChPartB.lean` + `ChWin.lean` | `window_witness`, `window_ceiling` (part (B) on [3.22, 1 + √5)), `part_B_of_inputs_low` (the reduction below 3.22, with its two inputs `PartB_WitnessInputLow` and `PartB_SmallInput` restated) |
| `window2` | `ChWitness.lean` + `ChPartB.lean` + `ChWin2.lean` | `window_witness_ext2`, `window_witness_full2` (part (B) on [2, 2.35) and on [2, 1 + √5)), `part_B_of_inputs_lower2` (the reduction below 2, with its input `PartB_WitnessInputLower2` restated) |
| `partB` | `ChWitness.lean` + `ChPartB.lean` + `ChPartBFull.lean` | `part_B_full` (part (B), without its equality clause, for every 0 < λ < 1 + √5, with no hypotheses), `partB_witness_all` (a witness and a best arm for every 0 < λ < 1 + √5), `partB_witnessInput` and `partB_smallInput` (the two former inputs, `PartB_WitnessInput` and `PartB_SmallInput`, as theorems), `fstar_eq_f3` (f* = f_3 on (0, 3/20]) |

Of the witness theorem only (a)-(c) are replayed. Its part (d), the examples (the golden hinge) and
`part_B_of_inputs` are checked by Lean's kernel in the build, but not by this second kernel, and so is the
intermediate step down to 2.35 (`window_witness_ext`, `window_witness_full`, `part_B_of_inputs_lower`).

Nine negative controls show that the check has teeth. Each changes one thing and must be **rejected**:

| configuration | change | expected |
|---|---|---|
| `neg_degree` | π_λ with degree + 1 instead of the degree | definition mismatch on `piL` |
| `neg_rate` | growth rate √(1 + λ/3) instead of √(1 + λ/2) | statement mismatch on `Mn_rate` |
| `neg_upper` | M_n ≤ (1 + λ)ρ^n instead of ρ^{n−1} (weaker, and true) | statement mismatch on `Mn_le_rho` |
| `neg_convex` | a witness without the convexity field | definition mismatch on `Witness.mk` |
| `neg_kappa` | the window witness with slope κ = 2 instead of κ = f*/t, claimed to be a witness on the window | rejected, since no proof exists (`sorryAx` in `CherrySolutionKappa.lean`) |
| `neg_window_low` | `window_witness_full2` claimed from λ = 1.95 instead of 2 | statement mismatch on `window_witness_full2` |
| `neg_input_range` | the input `PartB_WitnessInputLower2` stated on [1/10, 2.1) instead of [1/10, 2) | definition mismatch on `PartB_WitnessInputLower2` |
| `neg_partB_range` | `part_B_full` claimed for 0 ≤ λ instead of 0 < λ | statement mismatch on `part_B_full` |
| `neg_cross` | f* = f_3 claimed on (0, 1/2] instead of (0, 3/20]; this is false, since A_4 beats A_3 from about λ = 0.44 | statement mismatch on `fstar_eq_f3` |

The `neg_kappa` claim is not just unproved but false, and a sixth configuration, `kappa_refute`, must be
**accepted**: `CherrySolutionKappa.lean` proves `kap2_not_witness`, that for every λ in the window the
κ = 2 function is *not* a witness, because its Bellman inequality fails at a root with one non-exempt child,
at ȳ = y_C. So the slope of the window witness is genuinely constrained. The claim of `neg_window_low`, by contrast, is
not refuted: it is existential, and part (B) is expected to hold at 1.95 too. That control only shows that the
range of the statement is checked exactly. Its challenge, `ChNegKappa.lean`,
builds on `ChWinArms.lean` and `ChWinConst.lean`, which restate the window constants in two modules, as the
solution does, so that the auxiliary definitions get the same names on both sides.

Comparator matches constants by name and by term, so the challenges use the solution's names, and the
branch type sits in its own module so that its auxiliary definitions get the same names on both sides.
The challenges were written independently of the formalization, from the mathematics, during the audits
described in `../README.md`.

## Run it

```bash
# build the tools once (tag = this project's Lean version)
git clone --depth 1 --branch v4.32.0 https://github.com/leanprover/comparator.git
(cd comparator && lake build lean4export comparator)
git clone --depth 1 https://github.com/ammkrn/nanoda_lib.git && (cd nanoda_lib && cargo build --release)

# then, from formalization/cherry/ (after lake build)
export COMPARATOR_LEAN4EXPORT=/path/to/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=/path/to/nanoda_lib/target/release/nanoda_bin
export COMPARATOR_LANDRUN=/path/to/landrun   # a sandbox; on macOS a pass-through shim works
lake env comparator comparator/headline.comparator.json      # and likewise for the others
```

Each run takes one to two minutes and about 6 GB of memory.

## Result

On 1 October 2026, after the files for [2, 3.22) were added, every configuration was re-run. Every positive
configuration (`headline`, `lambda1`, `graph`, `branch`, `oneblock`, `witness`, `window`, `window2` and
`kappa_refute`) passed, with "Nanoda kernel accepts the solution", "Lean default kernel accepts the solution"
and "Your solution is okay!". Every negative control was rejected as expected: `neg_degree`, `neg_convex` and
`neg_input_range` with a definition mismatch, `neg_rate`, `neg_upper` and `neg_window_low` with a statement
mismatch, and `neg_kappa` with "Illegal axiom detected: 'sorryAx'". The runs were made locally on an Apple-silicon Mac, **not sandboxed**: the
landrun sandbox was replaced by a pass-through shim, as described in `../../comparator/README.md`. Since
the solution is our own, the guarantee comes from the replay by two kernels, not from the sandbox. These
runs are not part of CI.

On 1 October 2026, after part (B) on all of 0 < λ < 1 + √5 was added, the new configuration `partB` was run
and passed in the same way, with "Nanoda kernel accepts the solution", "Lean default kernel accepts the
solution" and "Your solution is okay!". Its two controls were rejected: `neg_partB_range` with a statement
mismatch on `part_B_full`, and `neg_cross` with a statement mismatch on `fstar_eq_f3`. These runs were made
the same way, locally and not sandboxed.
