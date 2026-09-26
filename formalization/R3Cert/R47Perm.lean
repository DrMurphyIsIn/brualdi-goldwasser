/-
  Rate port, file 1: PERMUTATION INVARIANCE of the matching partition functions.

  `Popen` is a product and `Matched` a leave-one-out sum, so both are invariant under
  child-list permutation; hence so are `Zopen`/`Ztot` of a node.  This is the glue the
  cherry-folding parse needs: `dtSub` keeps children in input order while `litRealize`
  puts cherries first, and the two lists are permutations with EQUAL entries.

  Proof: `List.Perm` induction; the swap case is the two-term leave-one-out algebra
  (ring), cons is congruence, trans is transitivity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Legs

namespace R3Cert
namespace Step3

open RTree

theorem Popen_perm {l1 l2 : List (ℝ × RTree)} (h : l1.Perm l2) :
    Popen l1 = Popen l2 := by
  induction h with
  | nil => rfl
  | @cons x l1' l2' _ ih =>
    obtain ⟨w, c⟩ := x
    simp only [Popen]
    rw [ih]
  | @swap x y l =>
    obtain ⟨wx, cx⟩ := x
    obtain ⟨wy, cy⟩ := y
    simp only [Popen]
    ring
  | @trans l1' l2' l3' _ _ ih1 ih2 =>
    rw [ih1, ih2]

theorem Matched_perm {l1 l2 : List (ℝ × RTree)} (h : l1.Perm l2) :
    Matched l1 = Matched l2 := by
  induction h with
  | nil => rfl
  | @cons x l1' l2' hperm ih =>
    obtain ⟨w, c⟩ := x
    simp only [Matched]
    rw [ih, Popen_perm hperm]
  | @swap x y l =>
    obtain ⟨wx, cx⟩ := x
    obtain ⟨wy, cy⟩ := y
    simp only [Matched, Popen]
    ring
  | @trans l1' l2' l3' _ _ ih1 ih2 =>
    rw [ih1, ih2]

theorem Ztot_node_perm {l1 l2 : List (ℝ × RTree)} (h : l1.Perm l2) :
    Ztot (RTree.node l1) = Ztot (RTree.node l2) := by
  simp only [Ztot]
  rw [Popen_perm h, Matched_perm h]

theorem Zopen_node_perm {l1 l2 : List (ℝ × RTree)} (h : l1.Perm l2) :
    Zopen (RTree.node l1) = Zopen (RTree.node l2) := by
  simp only [Zopen]
  exact Popen_perm h

end Step3
end R3Cert
