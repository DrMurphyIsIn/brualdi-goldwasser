# The cherry regime, kernel-checked

The main formalization in `../` answers Brualdi and Goldwasser's question at λ = 1: it proves which tree
maximizes per L(T)/∏ deg. The project page also tells a bigger story. Give every matched edge an extra
weight λ, and look at the whole family

  π_λ(T) = Σ over matchings M of T of ∏ over edges uv of M of λ/(deg u · deg v).

At λ = 1 this is the Laplacian ratio. As λ grows, the best building block climbs a ladder of arms, and at
λ = 1 + √5, where the golden ratio appears, the arms run off to infinity and plain cherries take over. From
there on, the cherry is the best block outright, and the maximum of π_λ grows like (1 + λ/2)^{n/2}.

The growth-rate side of that story is proved for every λ > 0. Below 1 + √5 the proof is computer-assisted
(interval arithmetic). From 1 + √5 on it is a hand proof: one-variable calculus at the anchor λ = 1 + √5,
using the golden identities 1 + λ/2 = φ² and 1 + λ = φ³, and then a monotonicity argument that carries the
anchor to every larger λ.

This directory is a second, separate Lean 4 project that checks the cherry regime λ ≥ 1 + √5 with the Lean
kernel, together with a general "one-block formula" that holds for every λ > 0. It does not touch, and is
not needed by, the λ = 1 theorem in `../`.

## What is proved

Write T_b(λ) for the weighted matching sum of a planted branch b (a rooted tree whose root also has a
phantom parent edge), |b| for its number of vertices, the *cherry* for the branch with two vertices, and
M_n(λ) for the maximum of π_λ over all trees on n vertices. Every statement below is a Lean theorem whose
axioms are exactly `propext`, `Classical.choice` and `Quot.sound` (no `sorry`, no `native_decide`, no
added axioms).

**For every λ ≥ 1 + √5:**

- For every finite tree T on n ≥ 1 vertices (a `SimpleGraph` with Mathlib's `IsTree`, degrees from
  Mathlib), π_λ(T) < (1 + λ)(1 + λ/2)^{(n−1)/2}. The upper bound is strict: it is never attained.
  (`pi_lam_lt_tree`; the non-strict form is `pi_lam_le_tree`.)
- For every planted branch b, T_b(λ) ≤ (1 + λ/2)^{|b|/2}, with equality if and only if b is the cherry.
  (`Br.ceiling_cherry_regime`, `Br.Tl_eq_cherry_iff`.) At the anchor λ = 1 + √5 this reads T_b ≤ φ^{|b|}.
- (1 + λ/2)^{⌊(n−1)/2⌋} ≤ M_n(λ) ≤ (1 + λ)(1 + λ/2)^{(n−1)/2} for every n ≥ 1, the lower bound by a
  center carrying ⌊(n−1)/2⌋ cherries (and one leaf when n is even). (`Mn_ge`, `Mn_le`.)
- ρ(λ) = sup over all planted branches b of T_b^{1/|b|} equals √(1 + λ/2), attained by the cherry, and
  lim M_n(λ)^{1/n} = √(1 + λ/2). (`rho_eq`, `rho_isGreatest`, `Mn_rate`, `rhoB_eq_cherry`.)

**For every λ > 0 (the bounds even for λ ≥ 0): the one-block formula.** With ρ(λ) defined as the supremum
of T_b^{1/|b|} over all finite planted branches (the leaf included):

- ρ(λ) ≤ 1 + λ (`rhoB_le`);
- T_b^{⌊(n−1)/|b|⌋} ≤ M_n(λ) for every branch b and every n ≥ 1, by the tree made of a new center carrying
  copies of b and leaves (`Mn_ge_block`);
- M_n(λ) ≤ (1 + λ) ρ(λ)^{n−1} (`Mn_le_rho`);
- lim M_n(λ)^{1/n} = ρ(λ) (`Mn_tendsto_rho`).

Below 1 + √5 this does **not** determine ρ(λ): it says that the best branch sets the growth rate, not which
branch is best or what the rate is.

**At λ = 1:** π_1(T) = per L(T) / ∏_v deg v for every tree on at least two vertices, with Mathlib's
`Matrix.permanent` and L = D − A (`pi_one_eq_permanent_tree`). This ties the family back to Brualdi and
Goldwasser's ratio.

Along the way the project also proves the cavity recursion (the recursive formula for T_b) equal to the
weighted matching sum on a Mathlib graph, the monomer-density inequality behind the monotonicity argument
(in a derivative form, for λ ≥ 2), and the non-strict monotonicity of T_b(λ)/(2 + λ)^{|b|/2} on [2, ∞).

M_n(λ) is defined as the maximum of π_λ over all trees on the vertex set {0, …, n−1} (`Finset.sup'` over
`Finset.univ.filter IsTree`), which is the same as the maximum over isomorphism classes.

## What is not formalized

- **Everything about λ < 1 + √5 beyond the one-block formula.** In particular the value ρ(λ) = e^{f*(λ)}
  there (the best block of the ladder sets the rate) and the equality cases there. That part rests on
  computer-assisted interval arithmetic and is not in Lean.
- **The witness framework** used for the range below 1 + √5. Its formalization exists and is being
  independently audited; it is not part of this publication yet.
- The strictness clauses of the monomer-density inequality and of the monotonicity.
- The formal proofs do not always follow the hand proofs. Most visibly, the anchor at 1 + √5 is proved in
  Lean by a pooled induction with a concave hinge (`Main.lean`, `Step.lean`, `Zero.lean`), not by the
  one-variable calculus of the hand proof. The statement is the same; the route differs.

## Checking it

```bash
cd formalization/cherry
lake exe cache get              # Mathlib's prebuilt files (same pins as ../)
lake build                      # about 3-4 minutes on an Apple M3 Ultra, under 6 GB of memory
lake env lean AxiomGuard.lean   # the axioms of the 13 headline theorems
```

The toolchain is Lean 4 v4.32.0 and Mathlib v4.32.0 (commit `81a5d257`), the same pins as `../`. If you
have already built `../`, you can reuse its Mathlib with `cp -c -R ../.lake/packages .lake/packages` (an
APFS clone on macOS) before `lake build`. Unlike `../`, this project is small: 26 files and about 4,500
lines, with no generated certificate data.

The `lean-cherry` workflow (`.github/workflows/lean-cherry.yml`, self-hosted, pushes to `main` that touch this
directory) builds it and checks the axiom guard.

## An independent second kernel

`comparator/` holds Comparator challenges for the headline theorems. Each challenge restates the
definitions (the matching sum with Mathlib degrees, the maximum over trees on `Fin n`, the cavity
recursion, ρ) and the theorems from scratch, importing only Mathlib, and Comparator checks that the
solution (`import LeanCherry`) proves exactly those statements and that both Lean's kernel and nanoda
accept the proofs. Its README has the details and the results; the runs were local and not sandboxed.

## Files

| file | what it holds |
|---|---|
| `TreeBridge.lean` | `piL` (π_λ of a Mathlib graph), every finite tree as a rooted branch, `pi_lam_le_tree` |
| `TreeStrict.lean` | `pi_lam_lt_tree`, the strict bound |
| `Tree.lean`, `Param.lean` | planted branches `Br`, the cavity recursion `Tl`, `msgl` |
| `Bridge.lean`, `BridgeMain.lean`, `GraphMatch.lean` | the cavity recursion equals the matching sum |
| `Main.lean`, `Step.lean`, `Zero.lean`, `Basic.lean` | the anchor at 1 + √5: T_b ≤ φ^{|b|} |
| `LemmaM.lean`, `LemmaMTree.lean`, `Deriv.lean` | the monomer-density inequality (derivative form) |
| `ThmE.lean` | the branch ceiling for every λ ≥ 1 + √5 |
| `Strict.lean` | equality only for the cherry |
| `Growth.lean`, `Realize.lean` | `Mn`, its bounds, ρ and the growth rate |
| `Rho.lean` | the one-block formula for every λ |
| `Lambda1.lean`, `R3Copy.lean` | the λ = 1 link to per L/∏ deg |
| `Whole.lean`, `AddLeaf.lean`, `Graph.lean`, `MatchSum.lean`, `Extra.lean` | plumbing |
| `AxiomGuard.lean` | `#print axioms` for the 13 headline theorems |

`R3Copy.lean` is a verbatim copy of the λ = 1 permanent/matching development of `../R3Cert`, renamed into
this namespace; its header records the provenance. Some module names (`ThmE`, `LemmaM`) are the working
names of the development and carry no meaning beyond that.

## Provenance

The formalization was produced with AI assistance (Claude, Anthropic) under the author's direction, like
the rest of this repository. Before publication it was independently audited four times, each audit by a
separate AI-run session that rebuilt the project from scratch, checked axioms and definitions, compared the
statements with the mathematics, checked small cases by brute force, and replayed the headline theorems
with Comparator against its own transcriptions. Those audits are AI checks, not human review; the Lean
kernel remains the only trusted component. Comments were lightly edited for publication; no Lean statement
or proof was changed.

Licensed under Apache-2.0, like all the mathematics and Lean code in this repository (see
[`../../LICENSING.md`](../../LICENSING.md)).
