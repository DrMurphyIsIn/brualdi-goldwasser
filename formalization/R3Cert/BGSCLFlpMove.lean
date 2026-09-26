/-
  Problem B, Stage B1: the local FLP straight-step.

  The crest-retaining degree-equalizing FLP move (the leaf-onto-leaf path extension) acts, at the
  reducing site `crest = []`, by replacing a child `flpChildBefore [] = node [leaf, leaf]` (non-piece)
  with `flpChildAfter [] = node [flpStem]` (an ARM, hence a piece) -- the "V -> path" degree-equalizer,
  the exact OPPOSITE of the refuted `pushInto`.  This file packages the three already-proved clauses
  into a single `StraightStep_sized`:
    * `usize` equal        -- from `usize_flp_move_eq` (BGSCLRealOblACaseABook);
    * `Aobj` non-decrease  -- from `aobj_flp_context_lift_crest` (BGSCLRealOblACaseALift, crest = []);
    * `strDefect` strictly drops -- `strDefect_flp_flip_lt` (proved here): the acted child flips
      piece-status (non-piece -> piece), lowering the parent's `npCount` by 1, provided the parent
      carries at least one OTHER non-piece child (`1 <= npCount (pre ++ post)`; without a sibling the
      node is already defect-zero).

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLRealOblACaseALift
import R3Cert.R47R7Sized

namespace R3Cert
namespace Step3

open RTree

/-! ### Piece status of the two acted nodes -/

/-- `flpChildAfter [] = node [flpStem]` is an arm (its one child `flpStem` is a cherry), hence a piece. -/
theorem isPiece_flpChildAfter_nil : isPiece (flpChildAfter []) = true := by
  simp [flpChildAfter, flpStem, flpLeaf, isPiece, isArm, isCherry, isLeaf]

/-- `flpChildBefore [] = node [leaf, leaf]` is non-piece (two leaves: not an arm, not a cherry). -/
theorem isPiece_flpChildBefore_nil : isPiece (flpChildBefore []) = false := by
  simp [flpChildBefore, flpLeaf, isPiece, isArm, isCherry, isLeaf]

/-- The acted-before node carries no internal defect. -/
theorem strDefect_flpChildBefore_nil : strDefect (flpChildBefore []) = 0 := by
  simp [flpChildBefore, flpLeaf, strDefect, npCount, npDefectSum, isPiece, isArm, isCherry, isLeaf]

/-! ### The size-preserving `usize` congruence for the local move -/

theorem usize_flp_context_eq (pre post : List UTree) :
    usize (UTree.node (pre ++ flpChildBefore [] :: post))
      = usize (UTree.node (pre ++ flpChildAfter [] :: post)) := by
  rw [usize_node, usize_node, usizeList_eq_sum, usizeList_eq_sum,
      List.map_append, List.map_append, List.map_cons, List.map_cons,
      List.sum_append, List.sum_append, List.sum_cons, List.sum_cons,
      usize_flp_move_eq []]

/-! ### The `strDefect` drop -/

/-- **The local FLP flip strictly lowers `strDefect`** when the acted node has a non-piece sibling.
    Replacing the non-piece `node [leaf, leaf]` by the piece `node [flpStem]` drops the parent's
    `npCount` by 1 while leaving `npDefectSum` unchanged (both acted nodes have zero internal defect). -/
theorem strDefect_flp_flip_lt (pre post : List UTree) (hsib : 1 ≤ npCount (pre ++ post)) :
    strDefect (UTree.node (pre ++ flpChildAfter [] :: post))
      < strDefect (UTree.node (pre ++ flpChildBefore [] :: post)) := by
  rw [npCount_append] at hsib
  have hnpA : npCount (pre ++ flpChildAfter [] :: post) = npCount pre + npCount post := by
    rw [npCount_append, npCount, isPiece_flpChildAfter_nil]; simp
  have hnpB : npCount (pre ++ flpChildBefore [] :: post) = npCount pre + npCount post + 1 := by
    rw [npCount_append, npCount, isPiece_flpChildBefore_nil]; simp; omega
  have hdA : npDefectSum (pre ++ flpChildAfter [] :: post) = npDefectSum pre + npDefectSum post := by
    rw [npDefectSum_append, npDefectSum, isPiece_flpChildAfter_nil]; simp
  have hdB : npDefectSum (pre ++ flpChildBefore [] :: post) = npDefectSum pre + npDefectSum post := by
    rw [npDefectSum_append, npDefectSum, isPiece_flpChildBefore_nil,
        strDefect_flpChildBefore_nil]; simp
  simp only [strDefect, hnpA, hnpB, hdA, hdB]
  omega

/-! ### The packaged local straight-step -/

/-- **B1: the local FLP move is a size-preserving straightening step.**  At any node carrying the
    acted `node [leaf, leaf]` plus at least one other non-piece child, the crest-`[]` FLP flip is a
    `StraightStep_sized` (usize-preserving, `Aobj`-non-decreasing, `strDefect`-strictly-dropping). -/
theorem flp_local_straightStep (pre post : List UTree) (hsib : 1 ≤ npCount (pre ++ post)) :
    StraightStep_sized (UTree.node (pre ++ flpChildBefore [] :: post))
      (UTree.node (pre ++ flpChildAfter [] :: post)) :=
  ⟨usize_flp_context_eq pre post,
   aobj_flp_context_lift_crest pre post [],
   strDefect_flp_flip_lt pre post hsib⟩

end Step3
end R3Cert
