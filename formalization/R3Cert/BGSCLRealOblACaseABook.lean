/-
  RealObligationA — Case A: the structural BOOKKEEPING of the leaf-path-extension move.

  `BGSCLRealOblACaseAIdentity.lean` proved the ROOT-level `Aobj`-monotonicity (`f2_aobj_monotone`).  The full
  `RealObligationA` move also needs, for the acted node `u = node [leaf, leaf]` (→ `flpStem = node [leaf]`):

    (1) SIZE preserved         — `usize` unchanged (stem = 2 vertices = the two leaves).       [proved here]
    (2) strDefect strictly DROPS — the PIECE-FLIP mechanism: `u = node [leaf, leaf]` is NON-piece, but
        `flpStem` is a cherry (PIECE), so in any parent `p = node (pre ++ u :: post)` the child `u` flips
        piece-status and `npCount p` drops by exactly 1 — hence `strDefect p` drops.                [proved here]
    (3) `Aobj` CONTEXT-LIFT — the whole-tree `Aobj` monotonicity when the move acts at a NON-root `u`.

  HONEST SCOPE on (3).  The existing child-replacement monotonicity `Aobj_child_replace_le`
  (`R47R7ChildMono.lean`) requires `udeg T = udeg T'` — a DEGREE-PRESERVING replacement.  The leaf-path-
  extension CHANGES the acted node's degree (`node [leaf, leaf]` has `udeg 3`; `flpStem` has `udeg 2`), so it
  is NOT an instance of `Aobj_child_replace_le`.  The context-lift is therefore a genuine DEGREE-CHANGING
  child-monotonicity lemma, not mechanical bookkeeping — it is stated below as the crisp residual
  `Aobj_flp_context_lift` (a Prop, NOT proved here).  (Numerically it holds — `a3_align.py` embedded cases show
  the whole-tree `ΔAobj > 0` — but a kernel proof needs the degree-changing cavity monotonicity.)

  Parts (1),(2) are kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47StepSize
import R3Cert.R47R7Straighten
import R3Cert.BGSCLRealOblACaseAIdentity

namespace R3Cert
namespace Step3

open RTree

/-! ### (1) Size preservation -/

theorem usize_flpLeaf : usize flpLeaf = 1 := by
  simp [flpLeaf, usize_node, usizeList_nil]

theorem usize_flpStem : usize flpStem = 2 := by
  simp [flpStem, flpLeaf, usize_node, usizeList_cons, usizeList_nil]

/-- The leaf-path-extension preserves the vertex count (`stem` = 2 vertices = the two leaves). -/
theorem usize_flp_move_eq (rest : List UTree) :
    usize (UTree.node (flpStem :: rest)) = usize (UTree.node (flpLeaf :: flpLeaf :: rest)) := by
  simp only [usize_node, usizeList_cons, usize_flpStem, usize_flpLeaf]
  omega

/-! ### (2) The piece-flip — the strDefect-reduction mechanism -/

/-- `flpStem = node [leaf]` is a cherry, hence a PIECE. -/
theorem isPiece_flpStem : isPiece flpStem = true := by
  simp [isPiece, isArm, isCherry, isLeaf, flpStem, flpLeaf]

/-- `node [leaf, leaf]` (the pre-move acted node) is NON-piece (two leaves: not an arm, not a cherry). -/
theorem isPiece_flp_before : isPiece (UTree.node [flpLeaf, flpLeaf]) = false := by
  simp [isPiece, isArm, isCherry, isLeaf, flpLeaf]

/-- **The piece-flip drops the parent's `npCount` by exactly 1.**  In any parent
    `node (pre ++ u :: post)`, replacing the non-piece `u = node [leaf, leaf]` by the piece `flpStem`
    lowers the non-piece child count by 1 — the local mechanism by which the leaf-path-extension strictly
    reduces `strDefect`. -/
theorem npCount_flp_flip (pre post : List UTree) :
    npCount (pre ++ flpStem :: post) + 1
      = npCount (pre ++ UTree.node [flpLeaf, flpLeaf] :: post) := by
  rw [npCount_append, npCount_append]
  have h1 : npCount (flpStem :: post) = npCount post := by
    rw [npCount, isPiece_flpStem]; simp
  have h2 : npCount (UTree.node [flpLeaf, flpLeaf] :: post) = 1 + npCount post := by
    rw [npCount, isPiece_flp_before]; simp
  rw [h1, h2]; omega

/-! ### (3) The DEGREE-CHANGING Aobj context-lift — SUPERSEDED (see below) -/

/-- **MIS-STATED / FALSE — retained only as the subject of its own refutation.**  This Prop replaces the acted
    child `node [flpLeaf, flpLeaf]` WHOLESALE by `flpStem = node [flpLeaf]` — which DROPS a vertex (not
    size-preserving) and is NOT the leaf-path-extension move.  It is FALSE in the cavity model
    (`flp_context_lift_book_false` in `BGSCLRealOblACaseALift.lean`: witness `node[node[leaf,leaf],leaf]`
    `Aobj=8/3 > node[flpStem,leaf]=5/2`).  The genuine, size-preserving context-lift retains the acted node's
    other children `crest` (`node(flpLeaf::flpLeaf::crest) → node(flpStem::crest)`) and IS PROVED as
    `R3Cert.Step3.aobj_flp_context_lift_crest` (`BGSCLRealOblACaseALift.lean`) — that is what downstream Case-A
    assembly must consume; nothing consumes THIS name except the refutation.  `f2_aobj_monotone` is the root case. -/
def Aobj_flp_context_lift : Prop :=
  ∀ (pre post : List UTree),
    Aobj (UTree.node (pre ++ UTree.node [flpLeaf, flpLeaf] :: post))
      ≤ Aobj (UTree.node (pre ++ flpStem :: post))

end Step3
end R3Cert
