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

## Uniqueness of the maximizer (`BGUnique/`)

`BGUnique/` proves that the maximizer is unique up to isomorphism for every n ≥ 4 except n = 21, where
exactly two non-isomorphic trees attain the maximum: T(3,3,3), which is `bgMax 21`, and the subdivided star
S(21,10), a centre with ten legs of length 2 (`S21`). In Mathlib's vocabulary on the hypothesis side (`BGUnique/Mathlib.lean`, `bg_maximizers_mathlib`): a finite
tree G (`SimpleGraph`, `IsTree`) on n ≥ 4 vertices maximizes per (G.lapMatrix ℝ) / ∏ deg among all finite
trees on n vertices if and only if G is isomorphic (`≃g`) to the realization of `bgMax n`, or n = 21 and G is
isomorphic to the realization of `S21`; the realizations are proved to be trees on n vertices
(`real_isTree`, `card_verts_realize`). `bg_maximizer_unique_mathlib` is the case n ≠ 21, and
`bg_maximizers_21_mathlib` shows that at n = 21 both trees attain the maximum and are not isomorphic, so
there are exactly two isomorphism classes.

The proof works first in the spider family and then lifts to all trees. For n ≥ 492 the winner is strictly
better than every other spider by a chain of strict exchanges (`SpiderUnique.lean`); for 7 ≤ n ≤ 491 a
strict form of the spider table is checked by the kernel, one module per n for 150 ≤ n ≤ 491 (`Sweep/`) and
in chunks of 13 for 7 ≤ n ≤ 149 (`SmallSweep/`; `StrictTable*.lean`), with the few sizes where two spider lists describe the same tree proved to be
rerootings of each other (`SmallTies.lean`); for n ≤ 6 every rooted tree is enumerated (`TinyUnique.lean`).
`AllUnique.lean` states the result up to rerooting (`bg_maximizers_exact`). `RerootIsoGraph.lean` and
`RerootIsoComplete.lean` prove that rerooting together with reordering children is exactly isomorphism of the
unrooted trees (`rerootRel_iff_uiso`), and `RerootIsoBridge*.lean` prove that the address graph used there is
a tree with the right number of vertices and is isomorphic to the realized graph behind `pi_utree`
(`G_iso_aGraph`), which gives the statement on per(L)/∏ deg (`bg_maximizers_exact_aGraph`).

`BGUnique/` is a separate library, not a default target: build it with `lake build BGUnique` after
`./build.sh`. The 353 kernel sweep modules take 6-13 GB each and are best built one at a time (the
`bg-unique` workflow does this, and `BGUnique/run_sweep.sh` does it for 150 ≤ n ≤ 491).
`BGUnique/gen_sweep.py` regenerates the sweep modules and their aggregators, `gen_strict.py` and
`gen_combos.py` the strict certificates, and `sweep_check.py` is an exact dry run of the strict sweep in
Python. `BGUnique/AxiomGuard.lean` prints the axioms of every headline theorem (only propext,
Classical.choice and Quot.sound, or a subset), and `comparator/BGUniqueChallenge.lean` restates the result
using Mathlib alone for Comparator (see `comparator/README.md`).

## The cherry regime (`cherry/`)

`cherry/` is a separate Lean project, not imported by anything here and not needed for the λ = 1 theorem.
It formalizes the cherry regime λ ≥ 1 + √5 of the λ-family (the branch ceiling with equality only for the
cherry, the strict upper bound for every tree, the lower bound, ρ(λ) = √(1 + λ/2) and the growth rate), the
one-block formula for every λ > 0, the witness framework (the witness theorem (a)-(c), and (d) up to one
step taken as a hypothesis), and part (B) *proved* on all of 0 < λ < 1 + √5 with its equality clause and
no external input (`part_B_full_eq` and `part_B_equality`, in `PBEqMain.lean`; the inequality and its
consequences alone are `part_B_full`, in `PBMain.lean`). The proof uses two piecewise-linear witnesses, W2 on (0, 3/20] (`PBW2.lean`) and W* on
[3/20, 1 + √5) (`PBWstar.lean`); its scalar conditions are proved in the `PBAtoms`, `PBRows*`, `PBCerts` and
`PBCertsFix` files, as exact-rational interval checks over proved monotone enclosures and Bernstein
polynomials of degree at most 6; the equality clause, by strict forms of the Bellman steps, is in the
`PBEq*` files. The earlier window results, by hand on [3.22, 1 + √5) (`WinBell.lean`) and by
45 exact-rational box checks on [2, 3.22) (the `WinExt*` files), remain in the project. It also proves the
λ = 1 link to per L/∏ deg. Its own
[README](cherry/README.md) states exactly what is and is not proved; read `TreeBridge.lean` (the
definition `piL`), `Growth.lean` (`Mn`), `Rho.lean` (`rhoSet`, `rhoB`), `Witness.lean` (`Witness`),
`PartB.lean` (f* and the reduction of part (B) to its inputs) and `PBMain.lean` (`part_B_full`, which proves
those inputs) to check the statements. It is
small and builds in a few minutes; its comments are clean of the history described above.

