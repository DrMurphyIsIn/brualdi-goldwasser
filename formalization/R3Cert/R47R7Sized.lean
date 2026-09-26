/-
  R4-R7 campaign, PHASE 7: the SIZE-PRESERVING tree->hub reduction (the well-posed target).

  The size-free `tree_to_hub` (R47R7StraightTrivial) is TRIVIAL and feeds the ill-posed capstone.
  The WELL-POSED capstone `conjecture1_of_layers_fixedN` needs a SIZE-PRESERVING witness
  (`stateSize s = usize t`).  This file re-threads vertex-count preservation through the whole
  tree->hub arc, producing the size-preserving reduction resting on the GENUINE obligation
  `StraightProgress_sized` -- a straightening move that keeps the vertex count fixed (so it cannot
  cheat by jumping to a large near-star).  That is where the real Kelmans mathematics lives.

  What is PROVED here (no `sorry`, axiom-clean):
    * `usizeList_perm`, `deepPerm_usize` -- deep permutation preserves the vertex count;
    * `strDefect_decode_sized` -- the decode is size-preserving (`usize (backboneU s) = usize t`);
    * `straighten_to_defectZero_sized` -- the schema reduces to a defect-zero tree of the SAME size;
    * `tree_to_hub_sized (StraightProgress_sized)` -- SIZE-PRESERVING tree->hub:
        `∀ t, ∃ s, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s)`.

  The one remaining obligation `StraightProgress_sized` is NON-trivial (unlike the size-free
  `StraightProgress`): the move must rearrange the SAME vertices into a higher-`Aobj`, lower-defect
  tree.  This is the honest Kelmans-straighten frontier.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Decode
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

/-! ### Deep permutation preserves the vertex count -/

theorem usizeList_eq_sum (l : List UTree) : usizeList l = (l.map usize).sum := by
  induction l with
  | nil => rw [usizeList_nil, List.map_nil, List.sum_nil]
  | cons K rest ih => rw [usizeList_cons, ih, List.map_cons, List.sum_cons]

theorem usizeList_perm {l1 l2 : List UTree} (h : l1.Perm l2) : usizeList l1 = usizeList l2 := by
  rw [usizeList_eq_sum, usizeList_eq_sum]; exact (h.map usize).sum_eq

mutual
theorem deepPerm_usize : ∀ {t t' : UTree}, DeepPerm t t' → usize t = usize t'
  | _, _, @DeepPerm.mk cs ds es hcong hperm => by
      rw [usize_node, usize_node, deepPerm_usizeList hcong, usizeList_perm hperm]
theorem deepPerm_usizeList :
    ∀ {cs ds : List UTree}, List.Forall₂ DeepPerm cs ds → usizeList cs = usizeList ds
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h hrest => by
      rw [usizeList_cons, usizeList_cons, deepPerm_usize h, deepPerm_usizeList hrest]
end

/-! ### The size-preserving decode -/

/-- The structural decode is size-preserving: a defect-zero tree is deep-perm to a backbone of the
    SAME vertex count. -/
theorem strDefect_decode_sized (t : UTree) (h : strDefect t = 0) :
    ∃ s : List Hub, DeepPerm t (backboneU s) ∧ usize (backboneU s) = usize t := by
  obtain ⟨s, hdp⟩ := strDefect_decode (sizeOf t) t le_rfl h
  exact ⟨s, hdp, (deepPerm_usize hdp).symm⟩

/-! ### The size-preserving straightening obligation and schema -/

/-- A SIZE-PRESERVING straightening step: same vertex count, `Aobj`-non-decreasing, defect-lowering.
    Unlike the size-free `StraightStep`, `t'` cannot be a large near-star. -/
def StraightStep_sized (t t' : UTree) : Prop :=
  usize t = usize t' ∧ Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t

/-- The genuine (non-trivial) straightening obligation. -/
def StraightProgress_sized : Prop :=
  ∀ t : UTree, strDefect t ≠ 0 → ∃ t', StraightStep_sized t t'

/-- **Size-preserving reduction to a defect-zero tree** (given `StraightProgress_sized`).
    Fuel-bounded induction on `strDefect`, carrying `usize` equality and `Aobj` monotonicity. -/
theorem straighten_to_defectZero_sized (hprog : StraightProgress_sized) :
    ∀ t : UTree, ∃ n : UTree, strDefect n = 0 ∧ usize n = usize t ∧ Aobj t ≤ Aobj n := by
  suffices H : ∀ N (t : UTree), strDefect t ≤ N →
      ∃ n : UTree, strDefect n = 0 ∧ usize n = usize t ∧ Aobj t ≤ Aobj n by
    exact fun t => H (strDefect t) t le_rfl
  intro N
  induction N with
  | zero =>
    intro t hle
    exact ⟨t, Nat.le_zero.mp hle, rfl, le_refl _⟩
  | succ N ih =>
    intro t hle
    by_cases h0 : strDefect t = 0
    · exact ⟨t, h0, rfl, le_refl _⟩
    · obtain ⟨t', hsz, hmono, hmeas⟩ := hprog t h0
      obtain ⟨n, hn0, hnsz, hnle⟩ := ih t' (by omega)
      exact ⟨n, hn0, hnsz.trans hsz.symm, hmono.trans hnle⟩

/-- **The SIZE-PRESERVING `tree_to_hub`, resting on `StraightProgress_sized`.**  Every tree is
    `Aobj`-dominated by a hub-backbone of the SAME vertex count.  This is the well-posed target
    (feeds `conjecture1_of_layers_fixedN`, which needs `stateSize s = usize t`); the sole remaining
    obligation `StraightProgress_sized` is the genuine Kelmans-straighten move existence. -/
theorem tree_to_hub_sized (hprog : StraightProgress_sized) :
    ∀ t : UTree, ∃ s : List Hub, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s) := by
  intro t
  obtain ⟨n, hn0, hnsz, hnle⟩ := straighten_to_defectZero_sized hprog t
  obtain ⟨s, hdp, hssz⟩ := strDefect_decode_sized n hn0
  exact ⟨s, by rw [hssz, hnsz], hnle.trans (le_of_eq (deepPerm_Aobj hdp))⟩

end Step3
end R3Cert
