# Reading the formalization

This directory is the import closure of the main theorem, copied from a larger research repository in
which the problem was attacked for several weeks by several routes. Some of that history shows in the
source, and a reader should know how to filter it.

## Where to start

**`Statement.lean`** states the theorem using only Mathlib's graph vocabulary (`SimpleGraph.IsTree`,
`lapMatrix`, `Matrix.permanent`, `degree`) and lists the handful of definitions it depends on. If you
only read one file, read that one. It rests on `R3Cert/TreePaths.lean` (every Mathlib tree is a
`UTree`), `R3Cert/TreeBridge.lean` (that `UTree`'s path graph is the realized graph) and
`R3Cert/BGStatement.lean` (the Laplacian ratio is an isomorphism invariant; the two theorems).

| file | what it holds |
|---|---|
| `R3Cert/BGMaximizerAll.lean` | the main theorem `bg_maximizer_all` and its literal-permanent form `bg_maximizer_all_perm` |
| `R3Cert/Matching.lean` | `lapl`, and `pi_eq_msum`: per(L)/prod deg equals the weighted matching sum on any finite forest |
| `R3Cert/R47Tree.lean` | `UTree`, `Aobj`, the realization of a `UTree` as a simple graph, and `pi_utree` |
| `R3Cert/BGSpiderRule.lean` | the rule spider `W n`, and `Aobj_spiderU` (spider value = closed form `F`) |
| `R3Cert/BGSpiderTableData.lean` | the table `tab n` for n <= 491 (generated) |
| `R3Cert/BGSCLSharp.lean`, `BGGrowthRate.lean` | the sharp ceiling and the growth rate |
| `AxiomGuard.lean` | `#print axioms` for the 17 headline theorems |

To check that the theorem says what the paper claims, you need `Matching.lean`, `R47Tree.lean` (the
definitions of `UTree`, `usize`, `Aobj`, `realize`, `aGraph`), `BGSpiderRule.lean` (`spiderU`, `W`) and
`BGSpiderTableData.lean` (`tab`). Everything else is proof.

## Names and comments you can ignore

- **`conjecture1_proved = False`** appears in many docstrings. It is a bookkeeping flag of the original
  repository, tracking one specific earlier formulation of the problem (`conjecture1_of_layers`, a
  layered "tree-to-hub" reduction with hypotheses `Hnorm`/`Hdom`). That formulation was abandoned; one of
  its hypotheses was shown false. The main theorem here does not use it, and the flag says nothing about
  `bg_maximizer_all`.
- **"open", "not in Lean", "being formalized"** in older docstrings describe the state of a file's
  neighbours when that file was written. `BGMaximizerAll.lean` and `AxiomGuard.lean` are authoritative.
- **Prefixes.** `R3Cert` is the library name. `R47*`, `Step3`, `Bridge*` are the tree/graph plumbing.
  `BGSCL*` is the cavity model and the sharp ceiling. `BGSpider*` is the reduction to spiders and the
  spider optimization. `BGEnvCert/*` is the envelope certificate for 7 <= n <= 149. `BGMaximizer*` assembles.
- **Generated files** (`BGSpiderTableChunk_*`, `BGEnvCert/G149/*`, `BGSpiderMidCells*`, `BGSpiderMidRoot*`,
  `BGSpiderCandCells*`, `BGSpiderCand.lean`) are certificates. Their generators are in `../certificates`,
  and `../certificates/verify.sh` regenerates them byte for byte.
- Every module in `R3Cert/` is used: each contributes at least one declaration to the dependency graph of
  the headline theorems (checked by walking that graph; release v1.1.0 removed 54 modules and 17
  declarations that were not).

## Build notes

- `./build.sh` on a machine with 96 GB of memory (about 64 GB must be free for the heaviest file,
  `G149/Frag22`, which peaks at 63 GB on its own). Lake has no option to limit parallelism, so the script
  builds the heavy certificate files one at a time (`./build.sh 2` for two at once, tested on 96 GB) and
  then runs `lake build`.
- There is no `native_decide` anywhere: every computation is evaluated by the kernel (`decide +kernel`).
  A `sorry` or `native_decide` would show up in `AxiomGuard.lean` as `sorryAx` or `Lean.ofReduceBool`.

## The cherry regime (`cherry/`)

`cherry/` is a separate Lean project, not imported by anything here and not needed for the λ = 1 theorem.
It formalizes the cherry regime λ ≥ 1 + √5 of the λ-family (the branch ceiling with equality only for the
cherry, the strict upper bound for every tree, the lower bound, ρ(λ) = √(1 + λ/2) and the growth rate), the
one-block formula for every λ > 0, the witness framework (the witness theorem (a)-(c), and (d) up to one
step taken as a hypothesis), part (B) *proved* on the window [3.22, 1 + √5) by hand (`WinBell.lean`; the
inequality only, its equality clause is not formalized) and *reduced* below 3.22 to two computer-assisted
inputs that Lean does not prove (`PartB.lean`, `WinBell.lean`), and the λ = 1 link to per L/∏ deg. Its own
[README](cherry/README.md) states exactly what is and is not proved; read `TreeBridge.lean` (the
definition `piL`), `Growth.lean` (`Mn`), `Rho.lean` (`rhoSet`, `rhoB`), `Witness.lean` (`Witness`),
`PartB.lean` (f* and the inputs) and the end of `WinBell.lean` (the window theorems and the reduced input) to
check the statements. It is
small and builds in a few minutes; its comments are clean of the history described above.

