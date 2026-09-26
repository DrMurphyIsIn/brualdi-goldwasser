/-
  R4-R7 campaign, PHASE 7: the STRAIGHTENING FINDER's context-lifting layer (Hnorm scoped port).

  The size-preserving tree->hub reduction `tree_to_hub_sized` (R47R7Sized) rests on the single
  obligation `StraightProgress_sized` -- every positive-defect tree admits a size-preserving,
  `Aobj`-non-decreasing, defect-lowering move.  The deep-hub de-branch move
  (`R47R7PushInto.deephub_local_straightStep`) supplies that move when the defect sits at the ROOT.

  The remaining structural work (per HANDOFF_TREE_TO_HUB_20260831, "next steps" #1) is
  CONTEXT-LIFTING: a move applied at a DEEP node inside `t` must lift to a `StraightStep_sized` on
  all of `t`.  This file discharges the two PURELY STRUCTURAL halves of that lift -- the `usize`
  congruence and the `strDefect` congruence under replacing a single child -- and packages the
  whole lift as `straightStep_sized_lift`, isolating the `Aobj`-monotonicity as an EXPLICIT
  `(Ztot, Zopen)`-gain hypothesis (Obligation A at the replacement site; NOT introduced here).

  What is PROVED here (no `sorry`, axiom-clean):
    * `usize_child_replace` / `usizeList_child_replace` -- replacing a child by an equal-`usize`
      one preserves the total vertex count (list + node forms);
    * `npCount_child_replace` -- replacing a child by one of the same `isPiece` status preserves
      the non-piece count of a list;
    * `npDefectSum_child_replace_lt` -- replacing a NON-piece child by a non-piece one of strictly
      smaller `strDefect` strictly lowers the list's `npDefectSum` (and never below the drop);
    * `strDefect_child_replace_lt` -- the node-level `strDefect` strictly drops under the same;
    * `straightStep_sized_lift` -- **the CONTEXT-LIFT**: a `StraightStep_sized` on a single child
      (equal `usize`, `Aobj`-monotone via the supplied gain, strictly lower `strDefect`, same
      `isPiece` status, non-piece) lifts to a `StraightStep_sized` on the parent node.  The
      `Aobj`-monotone half is taken as a hypothesis -- exactly the degree-changing cavity gain
      (`Aobj_tail_child_replace_le_deg` / Obligation A) at the replacement site.

  This turns the `StraightProgress_sized` finder into a plain recursive descent whose only
  per-node debt is Obligation A -- the Kelmans cavity inequality -- so nothing here weakens the
  frontier or hides an axiom.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Sized
import R3Cert.R47R7PushInto
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

/-! ### `usize` congruence under single-child replacement -/

/-- Replacing one child `c` of a list by `c'` of equal `usize` preserves the list's total. -/
theorem usizeList_child_replace (pre post : List UTree) {c c' : UTree}
    (hc : usize c = usize c') :
    usizeList (pre ++ c :: post) = usizeList (pre ++ c' :: post) := by
  rw [usizeList_append, usizeList_append, usizeList_cons, usizeList_cons, hc]

/-- Replacing one child `c` of a node by `c'` of equal `usize` preserves the node's vertex count. -/
theorem usize_child_replace (pre post : List UTree) {c c' : UTree}
    (hc : usize c = usize c') :
    usize (UTree.node (pre ++ c :: post)) = usize (UTree.node (pre ++ c' :: post)) := by
  rw [usize_node, usize_node, usizeList_child_replace pre post hc]

/-! ### `npCount` congruence: same `isPiece` status leaves the non-piece count fixed -/

/-- Replacing one child of a list by one of the SAME `isPiece` status preserves the non-piece
    count. -/
theorem npCount_child_replace (pre post : List UTree) {c c' : UTree}
    (hpc : isPiece c = isPiece c') :
    npCount (pre ++ c :: post) = npCount (pre ++ c' :: post) := by
  rw [npCount_append, npCount_append, npCount, npCount, hpc]

/-! ### `npDefectSum` strictly drops when a non-piece child's defect strictly drops -/

/-- Replacing a NON-piece child `c` of a list by a non-piece `c'` of strictly smaller `strDefect`
    strictly lowers `npDefectSum`, and the drop is exactly `strDefect c - strDefect c'`. -/
theorem npDefectSum_child_replace_lt (pre post : List UTree) {c c' : UTree}
    (hc : isPiece c = false) (hc' : isPiece c' = false) (hlt : strDefect c' < strDefect c) :
    npDefectSum (pre ++ c' :: post) + (strDefect c - strDefect c')
      = npDefectSum (pre ++ c :: post) := by
  rw [npDefectSum_append, npDefectSum_append, npDefectSum, npDefectSum,
    if_neg (by simp [hc']), if_neg (by simp [hc])]
  omega

/-! ### The node-level `strDefect` strictly drops -/

/-- **The `strDefect` context-lift.**  Replacing a non-piece child `c` of a node by a non-piece
    `c'` of strictly smaller `strDefect` strictly lowers the node's `strDefect`.  (The non-piece
    count is unchanged, so the `(npCount - 1)` term is common; only the defect sum drops.) -/
theorem strDefect_child_replace_lt (pre post : List UTree) {c c' : UTree}
    (hc : isPiece c = false) (hc' : isPiece c' = false) (hlt : strDefect c' < strDefect c) :
    strDefect (UTree.node (pre ++ c' :: post)) < strDefect (UTree.node (pre ++ c :: post)) := by
  have hcount : npCount (pre ++ c :: post) = npCount (pre ++ c' :: post) :=
    npCount_child_replace pre post (by rw [hc, hc'])
  have hsum := npDefectSum_child_replace_lt pre post hc hc' hlt
  rw [strDefect, strDefect, hcount]
  omega

/-! ### The context-lift theorem -/

/-- **The `StraightStep_sized` context-lift.**  A size-preserving straightening step on a single
    (non-piece) child `c ↦ c'` lifts to a size-preserving straightening step on the parent node,
    PROVIDED the `Aobj`-monotone half is supplied for the parent -- exactly the degree-changing
    cavity gain (`Aobj_tail_child_replace_le_deg`, i.e. Obligation A) at the replacement site.

    Structural halves proven here:
      * `usize` preservation (via `usize_child_replace`, since `usize c = usize c'` from the child
        step);
      * `strDefect` strict drop (via `strDefect_child_replace_lt`, since `c`/`c'` are non-piece and
        the child step lowered `strDefect`).

    So the finder's recursive descent needs, per node, ONLY the `Aobj`-monotone hypothesis -- no
    further bookkeeping.  Obligation A is honestly isolated and NOT assumed here. -/
theorem straightStep_sized_lift (pre post : List UTree) {c c' : UTree}
    (hc : isPiece c = false) (hc' : isPiece c' = false)
    (hstep : StraightStep_sized c c')
    (hAobj : Aobj (UTree.node (pre ++ c :: post)) ≤ Aobj (UTree.node (pre ++ c' :: post))) :
    StraightStep_sized (UTree.node (pre ++ c :: post)) (UTree.node (pre ++ c' :: post)) := by
  obtain ⟨hsz, _, hmeas⟩ := hstep
  refine ⟨?_, hAobj, ?_⟩
  · exact usize_child_replace pre post hsz
  · exact strDefect_child_replace_lt pre post hc hc' hmeas

end Step3
end R3Cert
