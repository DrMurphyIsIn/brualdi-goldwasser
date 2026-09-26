/-
  R4-R7 campaign, PHASE 7: the TREE -> HUB-STATE reduction schema (Hnorm's missing floor).

  The `Hnorm` layer of `conjecture1_of_layers` asserts that every tree is `Aobj`-dominated by
  some Balanced+Capped hub-backbone.  The whole balancing / rate machinery built so far
  (`single_hub_Hnorm`, `Aobj_balance_le_deep`, arm-rate unimodality, ...) operates on objects
  that are ALREADY of the form `backboneU s`.  What was missing is the BOTTOM of the stack: a
  reduction taking an ARBITRARY `UTree t` to `∃ s, Aobj t ≤ Aobj (backboneU s)`.  Without it,
  none of the downstream machinery can even be applied.

  This file supplies that reduction as a REUSABLE SCHEMA, lifting one level up the exact
  well-founded pattern that closed the single-hub arm-balancing case
  (`single_hub_reaches_balanced`): a monotone rewrite relation + a strictly-decreasing measure
  + a progress lemma, assembled by fuel-bounded induction on the measure.

  What is PROVED here (no `sorry`, axiom-free):

    * `treeToHub_of_isHubForm` -- a tree already in hub form trivially satisfies the bound;
    * `treeToHub_of_rewrite`   -- THE SCHEMA: given any `Aobj`-monotone rewrite `R` with a
                                  strictly-decreasing `ℕ`-measure whose only stuck points are
                                  hub-form trees, every tree is `Aobj`-dominated by a
                                  hub-backbone.  This is the tree-level analogue of
                                  `single_hub_reaches_balanced` + `Aobj_transferStar_le`.

  What REMAINS (the three typed obligations the schema isolates -- the genuine mathematics,
  each backed by an existing paper/Python certificate to be ported):

    (R-mono)  `R t t' → Aobj t ≤ Aobj t'`      -- Kelmans edge-switch / leg->cherry / branch
                                                   reductions are `Aobj`-non-decreasing.
                                                   Sources: kelmans_*.py (Kelmans corner Polya
                                                   cert psi_close/psi_symbolic), plainification_
                                                   theorem.py, deficit.py.  *** The hard node
                                                   (the historical "R4/Kelmans reduction"). ***
    (R-meas)  `R t t' → mu t' < mu t`           -- a lexicographic tree measure that every
                                                   rewrite strictly lowers (vertex budget:
                                                   kelmans_vertex_budget.py).
    (R-prog)  `¬ IsHubForm t → ∃ t', R t t'`    -- any non-hub-form tree admits a rewrite
                                                   (structural: a non-backbone shape always has
                                                   an applicable Kelmans/plainification move).

  Composing `tree_to_hub` (this file's target) with the existing single-hub balancing + cap +
  de-load machinery upgrades the witnessed `s` to Balanced+Capped, completing `Hnorm`.

  HONEST SCOPE.  This file proves the REDUCTION SCHEMA and reduces the tree->hub problem to the
  three obligations above; it does NOT discharge them (that is the Kelmans campaign).  The
  schema itself is genuine (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47HubState

namespace R3Cert
namespace Step3

open RTree

/-- A tree is in HUB-NORMAL FORM if it is literally a hub-backbone `backboneU s`.  This is the
    target normal form of the tree->hub rewrite: the stuck points of the reduction. -/
def IsHubForm (t : UTree) : Prop := ∃ s : List Hub, t = backboneU s

/-- Every hub-backbone is trivially in hub form (the identity witness). -/
theorem isHubForm_backboneU (s : List Hub) : IsHubForm (backboneU s) := ⟨s, rfl⟩

/-- A tree already in hub form trivially satisfies the tree->hub domination bound (with
    equality, via its own witness). -/
theorem treeToHub_of_isHubForm {t : UTree} (h : IsHubForm t) :
    ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨s, le_refl _⟩

/-- **The tree -> hub-state reduction schema.**

    Given
      * a rewrite relation `R` on trees that never decreases `Aobj` (`hmono`),
      * a `ℕ`-valued measure `mu` that every `R`-step strictly decreases (`hmeas`),
      * progress: any tree NOT already in hub form admits an `R`-step (`hprog`),

    every tree is `Aobj`-dominated by SOME hub-backbone `backboneU s`.

    This lifts, one structural level up, the well-founded recursion that closed the single-hub
    arm-balancing case (`single_hub_reaches_balanced` + `Aobj_transferStar_le`): fuel-bounded
    ordinary induction on `mu` (robust against well-founded-eliminator naming), terminating at a
    hub-form tree, with `Aobj`-monotonicity accumulated along the chain by `le_trans`.
    conjecture1_proved = False. -/
theorem treeToHub_of_rewrite
    (R : UTree → UTree → Prop) (mu : UTree → ℕ)
    (hmono : ∀ {t t' : UTree}, R t t' → Aobj t ≤ Aobj t')
    (hmeas : ∀ {t t' : UTree}, R t t' → mu t' < mu t)
    (hprog : ∀ {t : UTree}, ¬ IsHubForm t → ∃ t', R t t') :
    ∀ t : UTree, ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) := by
  suffices H : ∀ n (t : UTree), mu t ≤ n → ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) by
    exact fun t => H (mu t) t le_rfl
  intro n
  induction n with
  | zero =>
    intro t hle
    by_cases hhub : IsHubForm t
    · exact treeToHub_of_isHubForm hhub
    · obtain ⟨t', hstep⟩ := hprog hhub
      exact absurd (hmeas hstep) (by omega)
  | succ n ih =>
    intro t hle
    by_cases hhub : IsHubForm t
    · exact treeToHub_of_isHubForm hhub
    · obtain ⟨t', hstep⟩ := hprog hhub
      have hlt : mu t' < mu t := hmeas hstep
      have hle' : mu t' ≤ n := by omega
      obtain ⟨s, hs⟩ := ih t' hle'
      exact ⟨s, le_trans (hmono hstep) hs⟩

/-!
### The three remaining obligations, named

The schema `treeToHub_of_rewrite` reduces the tree->hub problem to the three predicates below,
stated for an arbitrary rewrite relation `R` and measure `mu`.  Discharging them (with the
concrete Kelmans/plainification/leg-cherry rewrite) yields the unconditional `tree_to_hub`
via `treeToHub_of_rewrite`.  These are DEFINITIONS (no proof obligation is asserted here), so
this file stays `sorry`-free while making the frontier crisp and CI-guardable.
-/

/-- (R-mono) The rewrite never decreases the objective. -/
def RewriteMonotone (R : UTree → UTree → Prop) : Prop :=
  ∀ {t t' : UTree}, R t t' → Aobj t ≤ Aobj t'

/-- (R-meas) The measure strictly decreases along every rewrite. -/
def RewriteDecreases (R : UTree → UTree → Prop) (mu : UTree → ℕ) : Prop :=
  ∀ {t t' : UTree}, R t t' → mu t' < mu t

/-- (R-prog) Every tree not in hub form admits a rewrite (only hub forms are stuck). -/
def RewriteProgresses (R : UTree → UTree → Prop) : Prop :=
  ∀ {t : UTree}, ¬ IsHubForm t → ∃ t', R t t'

/-- **`tree_to_hub`, conditional on the three Kelmans obligations.**  The clean statement of
    the reduction: supply a monotone, strictly-decreasing, progressing rewrite and every tree is
    `Aobj`-dominated by a hub-backbone.  This is the exact bottom-of-stack `Hnorm` needs; the
    remaining work is discharging `RewriteMonotone`/`RewriteDecreases`/`RewriteProgresses` for
    the concrete Kelmans rewrite. -/
theorem tree_to_hub_of_obligations
    (R : UTree → UTree → Prop) (mu : UTree → ℕ)
    (hmono : RewriteMonotone R) (hmeas : RewriteDecreases R mu)
    (hprog : RewriteProgresses R) :
    ∀ t : UTree, ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) :=
  treeToHub_of_rewrite R mu (fun h => hmono h) (fun h => hmeas h) (fun h => hprog h)

end Step3
end R3Cert
