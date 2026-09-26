/-
  R4-R7 campaign, PHASE 7: the generalized tree-reduction schema + the direct Hnorm reduction
  (tree->hub, Pass 2).

  Pass 1 gave the tree->hub schema for the WEAK target `IsHubForm` (any backbone).  But the
  capstone's actual `Hnorm` hypothesis is stronger:

      Hnorm : ∀ t, ∃ s, Balanced s ∧ Capped s ∧ Aobj t ≤ Aobj (backboneU s)

  -- the witness backbone must be Balanced AND Capped (the merge normalization is run INSIDE the
  capstone by `chain_to_normalForm`, so `Hnorm` itself carries no normal-form condition).

  This file generalizes the schema over an ARBITRARY target predicate `Normal : UTree -> Prop`
  and specializes it to the Balanced+Capped-backbone target, giving `hnorm_of_rewrite`: `Hnorm`
  follows from a SINGLE `Aobj`-non-decreasing, measure-decreasing rewrite whose stuck points are
  exactly the Balanced+Capped backbones.

  Combined with Pass 1 (`childReplace_monotone : RewriteMonotone ChildReplace`, which discharges
  the monotonicity obligation for the generator every concrete move instantiates), the entire
  `Hnorm` layer is now reduced to exhibiting ONE such rewrite -- i.e. to the two remaining
  obligations `RewriteDecreases` (a strictly-dropping measure) and `RewriteProgresses` (every
  non-Balanced-Capped-backbone tree admits a move), for the concrete Kelmans-straighten +
  arm-balance + de-load rewrite.

  What is PROVED here (no `sorry`, axiom-clean):
    * `treeReduce_of_rewrite` -- the schema for an arbitrary `Normal` target;
    * `treeToHub_of_rewrite'` -- Pass-1's `IsHubForm` target recovered as a corollary;
    * `hnorm_of_rewrite`      -- `Hnorm` reduced to one Balanced+Capped-backbone-terminating
                                 rewrite.

  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7TreeToHub
import R3Cert.R47StepMono

namespace R3Cert
namespace Step3

open RTree

/-- **Generalized tree-reduction schema.**  For an arbitrary target predicate `Normal`, an
    `Aobj`-non-decreasing rewrite `R` with a strictly-decreasing `ℕ`-measure `mu` whose only stuck
    points satisfy `Normal` reduces every tree to a `Normal` tree of not-smaller `Aobj`.  Same
    fuel-bounded induction as `treeToHub_of_rewrite`, target abstracted. -/
theorem treeReduce_of_rewrite
    (Normal : UTree → Prop) (R : UTree → UTree → Prop) (mu : UTree → ℕ)
    (hmono : ∀ {t t' : UTree}, R t t' → Aobj t ≤ Aobj t')
    (hmeas : ∀ {t t' : UTree}, R t t' → mu t' < mu t)
    (hprog : ∀ {t : UTree}, ¬ Normal t → ∃ t', R t t') :
    ∀ t : UTree, ∃ n : UTree, Normal n ∧ Aobj t ≤ Aobj n := by
  suffices H : ∀ N (t : UTree), mu t ≤ N → ∃ n : UTree, Normal n ∧ Aobj t ≤ Aobj n by
    exact fun t => H (mu t) t le_rfl
  intro N
  induction N with
  | zero =>
    intro t hle
    by_cases hn : Normal t
    · exact ⟨t, hn, le_refl _⟩
    · obtain ⟨t', hstep⟩ := hprog hn
      exact absurd (hmeas hstep) (by omega)
  | succ N ih =>
    intro t hle
    by_cases hn : Normal t
    · exact ⟨t, hn, le_refl _⟩
    · obtain ⟨t', hstep⟩ := hprog hn
      have hlt : mu t' < mu t := hmeas hstep
      obtain ⟨n, hn', hmono'⟩ := ih t' (by omega)
      exact ⟨n, hn', le_trans (hmono hstep) hmono'⟩

/-- Pass-1's `IsHubForm` reduction, recovered from the generalized schema. -/
theorem treeToHub_of_rewrite'
    (R : UTree → UTree → Prop) (mu : UTree → ℕ)
    (hmono : ∀ {t t' : UTree}, R t t' → Aobj t ≤ Aobj t')
    (hmeas : ∀ {t t' : UTree}, R t t' → mu t' < mu t)
    (hprog : ∀ {t : UTree}, ¬ IsHubForm t → ∃ t', R t t') :
    ∀ t : UTree, ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) := by
  intro t
  obtain ⟨n, ⟨s, rfl⟩, hle⟩ := treeReduce_of_rewrite IsHubForm R mu hmono hmeas hprog t
  exact ⟨s, hle⟩

/-- A tree is in BALANCED-CAPPED HUB FORM if it is a `backboneU` of a Balanced+Capped hub-state --
    the exact target class of the capstone's `Hnorm` witness. -/
def IsBCHubForm (t : UTree) : Prop :=
  ∃ s : List Hub, Balanced s ∧ Capped s ∧ t = backboneU s

/-- **`Hnorm`, reduced to a single rewrite.**  If there is an `Aobj`-non-decreasing rewrite with a
    strictly-decreasing measure whose stuck points are exactly the Balanced+Capped backbones, then
    the capstone's `Hnorm` hypothesis holds.  This folds the tree->backbone straightening,
    arm-balancing, and capping into one monotone reduction to the `Hdom`-ready witness class.
    With Pass 1 discharging monotonicity for the child-replacement generator, only the measure
    (`RewriteDecreases`) and progress (`RewriteProgresses`) obligations remain. -/
theorem hnorm_of_rewrite
    (R : UTree → UTree → Prop) (mu : UTree → ℕ)
    (hmono : ∀ {t t' : UTree}, R t t' → Aobj t ≤ Aobj t')
    (hmeas : ∀ {t t' : UTree}, R t t' → mu t' < mu t)
    (hprog : ∀ {t : UTree}, ¬ IsBCHubForm t → ∃ t', R t t') :
    ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧ Aobj t ≤ Aobj (backboneU s) := by
  intro t
  obtain ⟨n, ⟨s, hbal, hcap, rfl⟩, hle⟩ :=
    treeReduce_of_rewrite IsBCHubForm R mu hmono hmeas hprog t
  exact ⟨s, hbal, hcap, hle⟩

end Step3
end R3Cert
