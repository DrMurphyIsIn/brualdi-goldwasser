/-
  R4-R7 campaign, PHASE 5e (part 1): the edge-split identity -- root rotation without
  relabeling.

  Per the P5e design (P5_SEAM_DESIGN.md): re-rooting the state at the absorber reduces
  an interior merge to the head case.  The engine is the EDGE-SPLIT identity: matchings
  of a tree either use a given root-incident edge or not, so for any child position
      Ztot (node (X ++ (w, T) :: Y))
        = Ztot (node (X ++ Y)) * Ztot T + w * (Zopen (node (X ++ Y)) * Zopen T).
  The right side is SYMMETRIC in the two components of the edge (the true-degree edge
  weights are rooting-independent), so one-step root rotation follows by applying it
  at both rootings of an edge -- both reduce to the same four component terms.

  This file machine-checks the RTree-level layer: `Popen_append'`, `Matched_append`,
  `Zopen_append_split`, `Ztot_append_split`.  The state-level rotation and the Vee
  identity are part 2.

  Nothing here asserts per-step monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Dispatch

namespace R3Cert
namespace Step3

open RTree

/-! ### Partition functions over concatenations -/

theorem Popen_append' (l1 l2 : List (ℝ × RTree)) :
    Popen (l1 ++ l2) = Popen l1 * Popen l2 := by
  induction l1 with
  | nil =>
    simp only [List.nil_append, Popen]
    ring
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    simp only [List.cons_append, Popen]
    rw [ih]
    ring

theorem Matched_append (l1 l2 : List (ℝ × RTree)) :
    Matched (l1 ++ l2) = Matched l1 * Popen l2 + Popen l1 * Matched l2 := by
  induction l1 with
  | nil =>
    simp only [List.nil_append, Matched, Popen]
    ring
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    simp only [List.cons_append, Matched, Popen]
    rw [ih, Popen_append']
    ring

/-! ### The edge split at a middle child -/

/-- Open partition function with a middle child split into its own factor. -/
theorem Zopen_append_split (X Y : List (ℝ × RTree)) (w : ℝ) (T : RTree) :
    Zopen (RTree.node (X ++ (w, T) :: Y))
      = Zopen (RTree.node (X ++ Y)) * Ztot T := by
  simp only [Zopen, Popen_append', Popen]
  ring

/-- **The edge-split identity**: matchings either avoid the distinguished root edge
    (component product) or use it (weight times both open sides).  The right side is
    symmetric in the edge, which makes root rotation free. -/
theorem Ztot_append_split (X Y : List (ℝ × RTree)) (w : ℝ) (T : RTree) :
    Ztot (RTree.node (X ++ (w, T) :: Y))
      = Ztot (RTree.node (X ++ Y)) * Ztot T
        + w * (Zopen (RTree.node (X ++ Y)) * Zopen T) := by
  simp only [Ztot, Zopen, Matched_append, Popen_append', Matched, Popen]
  ring

end Step3
end R3Cert
