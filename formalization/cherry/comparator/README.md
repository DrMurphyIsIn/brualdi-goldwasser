# Independent check with Comparator

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's tool for checking a proof
against a separately written statement. Each challenge here restates, importing **only Mathlib**, the
definitions a headline theorem depends on (the weighted matching sum π_λ with Mathlib degrees, the maximum
M_n over the trees on `Fin n`, planted branches and the cavity recursion, ρ) and the theorem itself, with
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

Only (a)-(c) of the witness theorem are replayed. Its part (d), the examples (the golden hinge) and
`part_B_of_inputs` are checked by Lean's kernel in the build, but not by this second kernel.

Four negative controls show that the check has teeth. Each changes one thing and must be **rejected**:

| configuration | change | expected |
|---|---|---|
| `neg_degree` | π_λ with degree + 1 instead of the degree | definition mismatch on `piL` |
| `neg_rate` | growth rate √(1 + λ/3) instead of √(1 + λ/2) | statement mismatch on `Mn_rate` |
| `neg_upper` | M_n ≤ (1 + λ)ρ^n instead of ρ^{n−1} (weaker, and true) | statement mismatch on `Mn_le_rho` |
| `neg_convex` | a witness without the convexity field | definition mismatch on `Witness.mk` |

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

On 1 October 2026 every positive configuration passed, with "Nanoda kernel accepts the solution", "Lean
default kernel accepts the solution" and "Your solution is okay!", and every negative control was rejected
with the expected mismatch. The runs were made locally on an Apple-silicon Mac, **not sandboxed**: the
landrun sandbox was replaced by a pass-through shim, as described in `../../comparator/README.md`. Since
the solution is our own, the guarantee comes from the replay by two kernels, not from the sandbox. These
runs are not part of CI.
