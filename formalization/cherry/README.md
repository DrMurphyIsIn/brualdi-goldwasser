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
kernel, together with a general "one-block formula" that holds for every λ > 0, and the witness framework
that organizes the part below 1 + √5. That part, part (B) of the uniform ceiling without its equality
clause, is now **proved** in Lean for every 0 < λ < 1 + √5, with no external input (`part_B_full`), by a
two-witness argument whose scalar conditions are all proved in Lean. The equality clause is not formalized.
The project does not touch, and is not needed by, the λ = 1 theorem in `../`.

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

On its own this does **not** determine ρ(λ) below 1 + √5: it says that the best branch sets the growth rate,
not which branch is best or what the rate is.

**For every λ > 0: the witness framework.** A *witness* for (λ, F) is an exempt set A of branches, an interval
I with (0, ½] ⊆ I ⊆ [0, 1], and a function h that is convex and bounded below on I, subject to a Bellman
inequality for every non-exempt type of root (`Witness`, with the deficit g(b) = |b|F − log T_b). Lean proves
the witness theorem:

- (a) from a witness, g ≥ h(y_b) ≥ 0 on non-exempt branches and g ≥ 0 on exempt ones, so T_b ≤ e^{F|b|} for
  every branch (`Witness.mt_main_a`);
- (b) M_n(λ) ≤ (1 + λ)e^{F(n−1)} and ρ(λ) ≤ e^F (`Witness.mt_main_b`);
- (c) if some branch b* has g(b*) = 0, then ρ(λ) = e^F and e^{F|b*|⌊(n−1)/|b*|⌋} ≤ M_n(λ) (`Witness.mt_main_c`);
- (d) the characterization of the tight branches (`tight_leaf`, `tight_node`, `tight_of_g_zero`), except for
  one step: that a corner of h yields a supporting line touching its graph only at the mean message. That
  step is taken as a hypothesis (`jensen_eq_forces`).

The definition is not vacuous. The golden hinge at λ = 1 + √5 is proved to be a witness, tight at the
cherry (`hinge_witness`), and the witness theorem re-derives from it T_b ≤ φ^{|b|} and ρ(1 + √5) = φ
(`ceiling_at_lam_c_via_witness`, `rho_lam_c_via_witness`).

Part (B) is the statement that, for 0 < λ < 1 + √5, every planted branch b satisfies
log T_b ≤ |b| f*(λ), where f*(λ) is the best arm rate, sup over j ≥ 1 of log T(A_j)/(2j + 1), and A_j is a
root carrying j cherries. Lean proves it, without its equality clause, for every 0 < λ < 1 + √5 and with no
external input (`part_B_full`, described last below). It was first proved on the window [3.22, 1 + √5) and then
on [2, 1 + √5); those two steps remain in the project.

**Part (B) on the window [3.22, 1 + √5): proved, by hand.** For every λ in [3.22, 1 + √5), `window_witness`
proves that the explicit three-piece function h = max(0, s_1(y − y†), ε + κ(y − y_C)) is a witness for
(λ, f*(λ)), and that the supremum f*(λ) is attained by some arm. `window_ceiling` gives the branch bound
log T_b ≤ |b| f*(λ) for every planted branch, and with the witness theorem this gives ρ(λ) = e^{f*(λ)} and the
two-sided bound on M_n(λ) with a best arm as b*, on the window and with no input (by `Witness.mt_main_c`;
these consequences are not stated as separate theorems). The proof is by hand: the
interval checks of the computer-assisted version are replaced by monotonicity, tangent and chord arguments
(`WinC2.lean`), and the constants of the witness by closed-form enclosures in η = 1 + √5 − λ
(`WinConst.lean`). Its only numerical input is e^{0.4796} ≤ 1.6155, from Mathlib's `Real.exp_bound'`. This is
the inequality of part (B) without its equality clause: every Bellman case on the window is proved in the
non-strict form, and strictness is not formalized. The hand proof needs λ ≥ 3.22 (it uses
√(1 + λ/2) ≥ 1.6155); below that, the same witness is handled by the computation described next.

**Part (B) on [2, 3.22): proved, by a computation checked by the kernel.** `window_witness_full2` proves, for
every λ in [2, 1 + √5), that the same three-piece function h is a witness for (λ, f*(λ)), and that the
supremum f*(λ) is attained by some arm. On [3.22, 1 + √5) it uses `window_witness`. On [2, 3.22) the proof is
not a hand proof but a computation inside Lean: λ is split into 45 closed boxes (37 on [2.35, 3.22] in
`WinExtBoxes.lean`, 8 on [2, 2.35] in `WinExt2Boxes.lean`). On each box every quantity of the argument is
enclosed between exact rationals by proved monotone bounds (`WinExtBox.lean`), and the resulting 2,078
rational inequalities are closed by `norm_num` and checked by the kernel, as is the fact that the boxes cover
the range without a gap. f* enters only through exact identities and closed-form bounds on the cherry
deficit ε, so no arm is enumerated, and it does not matter which arm is best inside a box. The root types
with many children (k = 0 and m ≥ 8, or m ≥ 5 below 2.35) are handled by hand, by the argument used on the
window, with y† ≥ 1/6 and the slope bound λ/(m + 1 + λ m y_C) ≤ κ in place of y† ≥ 1/9 and λ ≤ 8κ below 2.35
(`WinExt2Core.lean`); the box conditions are needed only for fewer children. (`window_witness_ext` and
`window_witness_full` are the intermediate step, down to 2.35; `window_witness_ext2` is the piece [2, 2.35).)
As on the window, this is the inequality of part (B) without its equality clause. With the witness theorem it
gives, with no external input, the branch bound, ρ(λ) = e^{f*(λ)} and the two-sided bound on M_n(λ) with a
best arm on all of [2, 1 + √5).

The floor at 2 comes from the proof route, not from the witness. The box method stops at λ = 2, where one
case split of the argument (for m = 2 children) changes sign, and in box form it would also stop near 1.87,
at the condition for m = 4. Numerically, this witness shows no violation of its Bellman inequality down to
λ = 1.5, but the box method does not prove that. Below 2, part (B) is proved by the two-witness argument
described next.

**Part (B) on all of 0 < λ < 1 + √5: proved, with no external input.** `part_B_full` proves, for every
0 < λ < 1 + √5 and with no hypotheses, the branch bound log T_b ≤ |b| f*(λ) for every planted branch, where
f*(λ) = sup_{j ≥ 1} f_j(λ) is attained by some arm, ρ(λ) = e^{f*(λ)}, and
e^{f*|A_j|⌊(n−1)/|A_j|⌋} ≤ M_n(λ) ≤ (1 + λ)e^{(n−1)f*(λ)} for a best arm A_j and every n ≥ 1. It is
`part_B_of_inputs` applied to its two former inputs, both now theorems: `partB_witnessInput` (a witness for
(λ, f*(λ)) and a best arm on [0.1, 1 + √5)) and `partB_smallInput` (the branch bound and a best arm on
(0, 0.1]). Both come from `partB_witness_all`, which gives a witness and a best arm for every 0 < λ < 1 + √5:

- on [3/20, 1 + √5), the leaf-exempt piecewise-linear witness W*: flat up to y†, a ramp to ε at y_C, then
  slope κ = λ/(3 + 2t), with t = λ/(2 + λ) (`PBWstar.lean`);
- on (0, 3/20], the witness W2, with one more kink at y(A_2), where h(y(A_2)) = (4/5) g(A_2) (`PBW2.lean`).
  On this range f* = f_3, that is, the arm with three cherries is a best arm (`fstar_eq_f3`).

No cell cover is used. The Bellman inequalities are reduced by hand, uniformly in λ, to finitely many scalar
conditions (`PBStruct.lean`, `PBFlat.lean`), and each scalar condition is a Lean theorem over its whole
interval (`PBCerts.lean`, `PBCertsFix.lean`). Each condition is proved either by kernel-checked exact-rational
rows over proved monotone enclosures of a few one-variable functions (`PBAtoms.lean`, `PBRows*.lean`: 59
rows), or, for polynomials of degree at most 6, by exact Bernstein identities. Like the rest of part (B) in
this project, this is the inequality without its equality clause.

The Lean proof follows the two-witness argument, but four steps take valid routes that differ from the text.
- f* = f_3 on (0, 3/20] is proved by comparing the arms directly (`PBGap.lean`), in place of the crossing
  lemma for the arm ladder.
- For (S6), the needed monotonicity in the rate uses only f* ≥ f_3 (`psi_mono`).
- (S5) is proved at the true rate, with no pointwise monotonicity in the rate.
- (S3) uses the bound ε ≤ D/6.

The earlier forms of the reduction (`part_B_of_inputs`, `part_B_of_inputs_low`, `part_B_of_inputs_lower`,
`part_B_of_inputs_lower2`) remain in the project, but are no longer needed.

**At λ = 1:** π_1(T) = per L(T) / ∏_v deg v for every tree on at least two vertices, with Mathlib's
`Matrix.permanent` and L = D − A (`pi_one_eq_permanent_tree`). This ties the family back to Brualdi and
Goldwasser's ratio.

Along the way the project also proves the cavity recursion (the recursive formula for T_b) equal to the
weighted matching sum on a Mathlib graph, the monomer-density inequality behind the monotonicity argument
(in a derivative form, for λ ≥ 2), and the non-strict monotonicity of T_b(λ)/(2 + λ)^{|b|/2} on [2, ∞).

M_n(λ) is defined as the maximum of π_λ over all trees on the vertex set {0, …, n−1} (`Finset.sup'` over
`Finset.univ.filter IsTree`), which is the same as the maximum over isomorphism classes.

## What is not formalized

- The equality clause of part (B) (equality exactly for a best arm), everywhere, including the strict
  inequalities of the window argument, of the box computation and of the two-witness argument.
- In the witness theorem (d), the step from a corner of h to a strict supporting line, which is a
  hypothesis.
- The strictness clauses of the monomer-density inequality and of the monotonicity.
- The formal proofs do not always follow the hand proofs. Most visibly, the anchor at 1 + √5 is proved in
  Lean by a pooled induction with a concave hinge (`Main.lean`, `Step.lean`, `Zero.lean`), not by the
  one-variable calculus of the hand proof. The statement is the same; the route differs.

## Checking it

```bash
cd formalization/cherry
lake exe cache get              # Mathlib's prebuilt files (same pins as ../)
lake build                      # about 4-5 minutes on an Apple M3 Ultra, about 6 GB of memory
lake env lean AxiomGuard.lean   # the axioms of the 52 headline theorems
```

The toolchain is Lean 4 v4.32.0 and Mathlib v4.32.0 (commit `81a5d257`), the same pins as `../`. If you
have already built `../`, you can reuse its Mathlib with `cp -c -R ../.lake/packages .lake/packages` (an
APFS clone on macOS) before `lake build`. Unlike `../`, this project is small: 58 files and about 13,400
lines. Its generated certificate data are the two box files, `WinExtBoxes.lean` and `WinExt2Boxes.lean`, and
the part (B) certificate rows, `PBRows*.lean` (see "Generated files" below).

The `lean-cherry` workflow (`.github/workflows/lean-cherry.yml`, self-hosted, pushes to `main` that touch this
directory) builds it and checks the axiom guard.

## An independent second kernel

`comparator/` holds Comparator challenges for the headline theorems. Each challenge restates the
definitions (the matching sum with Mathlib degrees, the maximum over trees on `Fin n`, the cavity
recursion, ρ) and the theorems from scratch, importing only Mathlib, and Comparator checks that the
solution (`import LeanCherry`) proves exactly those statements and that both Lean's kernel and nanoda
accept the proofs. For the witness framework, (a)-(c) of the witness theorem were replayed this way, and so
were the window statements (`window_witness`, `window_ceiling`), the reduction below 3.22
(`part_B_of_inputs_low`), the extension to [2, 1 + √5) (`window_witness_ext2`, `window_witness_full2`) and the
reduction below 2 (`part_B_of_inputs_lower2`), and part (B) on all of 0 < λ < 1 + √5 (`part_B_full`,
`partB_witness_all`, `partB_witnessInput`, `partB_smallInput`, `fstar_eq_f3`); (d), the examples,
`part_B_of_inputs` and the intermediate step down to 2.35 were not. Its README has the details and
the results; the runs were local and not sandboxed.

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
| `Witness.lean` | witnesses and the witness theorem (a)-(d) |
| `WitnessExamples.lean` | the trivial witness, and the golden hinge as a witness at 1 + √5 |
| `PartB.lean` | part (B) from its two numerical inputs |
| `WinArms.lean` | the window: closed forms for the arms A_j, bounds on f*, and that some arm attains it |
| `WinConst.lean` | the window: the constants of the witness and their enclosures in η = 1 + √5 − λ |
| `WinC2.lean` | the window: the Bellman inequality for 1 ≤ m ≤ 7 children, by hand |
| `WinBell.lean` | the window witness, `window_witness`, `window_ceiling`, and part (B) from the inputs below 3.22 |
| `WinExtCore.lean` | the window argument, run from a list of facts about the constants (`WFacts`) |
| `WinExtBox.lean` | proved monotone enclosures, by exact rationals, of the window constants on a λ-box |
| `WinExtAssemble.lean` | a box's rational inequalities (`BoxOK`) give `WFacts` on the whole box |
| `WinExtBoxes.lean` | generated: the 37 boxes covering [2.35, 3.22] and their certificates |
| `WinExtMain.lean` | `window_witness_ext`, `window_witness_full`, and part (B) from the inputs below 2.35 |
| `WinExt2Core.lean`, `WinExt2Assemble.lean` | the same with the k = 0, m ≥ 5 types by hand (`WFacts2`, `BoxOK2`) |
| `WinExt2Boxes.lean` | generated: the 8 boxes covering [2, 2.35] and their certificates |
| `WinExt2Main.lean` | `window_witness_ext2`, `window_witness_full2`, and part (B) from the inputs below 2 |
| `PBBasic.lean` | part (B): elementary log bounds, the convex-tangent lemma, the slope κ, and enclosures of ε on all of (0, 1 + √5) |
| `PBAtoms.lean`, `PBRowsCore.lean` | proved monotone enclosures of the one-variable functions behind the certificates |
| `PBRowsC1.lean`, `PBRowsC3.lean`, `PBRowsC7.lean`, `PBRowsC8.lean`, `PBRowsC10.lean` | generated: the certificate rows |
| `PBCerts.lean`, `PBCertsFix.lean` | every scalar condition as a theorem over its whole interval, and the (S6) step on [λ_D2, 2] |
| `PBStruct.lean`, `PBFlat.lean` | the reduction of the Bellman inequalities to the scalar conditions, by hand |
| `PBWstar.lean`, `PBW2.lean` | the witnesses W* on [3/20, 1 + √5) and W2 on (0, 3/20] |
| `PBGap.lean` | f* = f_3 on (0, 3/20], by a direct comparison of the arms |
| `PBMain.lean` | `partB_witness_all`, the two former inputs, and `part_B_full` |
| `Lambda1.lean`, `R3Copy.lean` | the λ = 1 link to per L/∏ deg |
| `Whole.lean`, `AddLeaf.lean`, `Graph.lean`, `MatchSum.lean`, `Extra.lean` | plumbing |
| `AxiomGuard.lean` | `#print axioms` for the 52 headline theorems |
| `scripts/` | the generators of `WinExt2Core.lean`, `WinExt2Assemble.lean` and the two box files |

`R3Copy.lean` is a verbatim copy of the λ = 1 permanent/matching development of `../R3Cert`, renamed into
this namespace; its header records the provenance. Some module names (`ThmE`, `LemmaM`) are the working
names of the development and carry no meaning beyond that.

### Generated files

Four files are written by scripts in `scripts/` (run them from that directory, with Python 3 and no other
dependencies). `make_ext2.py` writes `WinExt2Core.lean` and `WinExt2Assemble.lean` by a textual
transformation of `WinExtCore.lean` and `WinExtAssemble.lean`. `emit_lean.py` and `emit_lean2.py` write
`WinExtBoxes.lean` and `WinExt2Boxes.lean` from the box constants in `boxes.json` and `boxes2.json`.
Rerunning them reproduces the committed files byte for byte; this was checked in the independent audit
(AI-run) and again before publication. The search that chose the box constants is not included. They need
no trust: the kernel checks every inequality, and the coverage of the range.

`BoxOK2` still carries two fields that are no longer needed: `h8` (λ ≤ 8κ), which its proof never uses, and
`hydl9` (a lower bound 1/9 on y†), which the new field `hydl6` (1/6) implies. Both are checked for every box.
This is cosmetic, and they were left in place so that the code is exactly the code that was audited.

The part (B) certificate rows (`PBRowsC1.lean`, `PBRowsC3.lean`, `PBRowsC7.lean`, `PBRowsC8.lean`,
`PBRowsC10.lean`) were also written by a script, from the exact rational endpoints and enclosure values of
each row. That script is not included. The rows need no trust either: each is a kernel-checked rational
inequality, and the covering of each interval by its rows is proved in `PBCerts.lean`. Three certificates in
`AxiomGuard.lean`, `cert_C9`, `mono_r` and `mono_Lq`, are auxiliary: `part_B_full` does not use them.

## Provenance

The formalization was produced with AI assistance (Claude, Anthropic) under the author's direction, like
the rest of this repository. Before publication it was independently audited, by AI-run audits, each by a
separate AI-run session that rebuilt the project from scratch, checked axioms and definitions, compared the
statements with the mathematics, checked small cases by brute force, and replayed the headline theorems
with Comparator against its own transcriptions. Those audits are AI checks, not human review; the Lean
kernel remains the only trusted component. Comments were lightly edited for publication; no Lean statement
or proof was changed.

Licensed under Apache-2.0, like all the mathematics and Lean code in this repository (see
[`../../LICENSING.md`](../../LICENSING.md)).
