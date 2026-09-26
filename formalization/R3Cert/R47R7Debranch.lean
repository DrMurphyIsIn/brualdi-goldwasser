/-
  R4-R7 campaign, PHASE 7: the DE-BRANCH move arithmetic (tree->hub, Phase 3 scaffolding).

  Phase 0 confirmed a single SPR "de-branch" move discharges `StraightProgress_sized`: relocate an
  off-backbone branch onto the spine, dropping `strDefect` by exactly 1.  The concrete provable move
  is: attach a non-piece branch `B` to a HUB `H` (a node whose children are ALL pieces).  This file
  proves the `strDefect` ACCOUNTING of that move -- the tractable structural half -- isolating the
  `Aobj`-monotonicity (Obligation A, the Kelmans cavity inequality) as the single remaining lemma.

  Core arithmetic:
    * `strDefect_hub_attach` -- attaching a non-piece `B` to a hub gives `strDefect = strDefect B`
      (the hub's own defect stays 0; only `B`'s defect is inherited);
    * `strDefect_cons_nonpiece` / `strDefect_remove_nonpiece` -- removing a non-piece child from a
      node drops the local branch count by 1 and the sum by that child's defect.

  Together these give the `strDefect`-drops-by-1 accounting of the de-branch step.  What is PROVED
  here is `no `sorry``, axiom-clean; `Aobj t ≤ Aobj (debranch t)` is the isolated Kelmans obligation.
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Straighten
import R3Cert.R47StepSize
import R3Cert.R47R7Sized

namespace R3Cert
namespace Step3

open RTree

/-- **The hub-attach identity.**  Attaching a non-piece branch `B` to a HUB (a node whose children
    are all pieces) yields a node whose defect is exactly `B`'s: the hub contributes no branch defect
    (its non-piece count goes `0 → 1`, and `max(0, 1-1) = 0`), and only `B`'s own defect is inherited.
    This is the local core of the de-branch move's `strDefect` accounting. -/
theorem strDefect_hub_attach {Hs : List UTree} {B : UTree}
    (hpieces : ∀ c ∈ Hs, isPiece c = true) (hB : isPiece B = false) :
    strDefect (UTree.node (Hs ++ [B])) = strDefect B := by
  rw [strDefect, npCount_append, npCount_pieces hpieces, npDefectSum_append,
    npDefectSum_pieces hpieces, npCount, npCount, npDefectSum, npDefectSum]
  simp [hB]

/-- Non-piece count of a node with a distinguished non-piece child `B` peeled off the front. -/
theorem npCount_cons_nonpiece {B : UTree} {rest : List UTree} (hB : isPiece B = false) :
    npCount (B :: rest) = npCount rest + 1 := by
  rw [npCount, if_neg (by rw [hB]; simp)]; omega

/-- Defect sum of a node with a distinguished non-piece child `B` peeled off the front. -/
theorem npDefectSum_cons_nonpiece {B : UTree} {rest : List UTree} (hB : isPiece B = false) :
    npDefectSum (B :: rest) = strDefect B + npDefectSum rest := by
  rw [npDefectSum, if_neg (by rw [hB]; simp)]

/-! ### The local de-branch step -/

/-- **The local de-branch step drops `strDefect` by exactly 1.**  At a node whose first child is a
    hub `A = node As` (all-piece children, itself non-piece) and whose second child `B` is non-piece,
    moving `B` onto the hub (`A ↦ node (As ++ [B])`, `B` removed from the parent) drops the parent's
    branch count by one while the hub inherits only `B`'s own defect -- a net drop of exactly 1. -/
theorem strDefect_debranch_local {As rest : List UTree} {B : UTree}
    (hAs : ∀ c ∈ As, isPiece c = true) (hB : isPiece B = false)
    (hA : isPiece (UTree.node As) = false)
    (hA' : isPiece (UTree.node (As ++ [B])) = false) :
    strDefect (UTree.node (UTree.node (As ++ [B]) :: rest)) + 1
      = strDefect (UTree.node (UTree.node As :: B :: rest)) := by
  have hhub : strDefect (UTree.node As) = 0 := by
    rw [strDefect, npCount_pieces hAs, npDefectSum_pieces hAs]
  have hattach : strDefect (UTree.node (As ++ [B])) = strDefect B := strDefect_hub_attach hAs hB
  rw [strDefect, strDefect, npCount_cons_nonpiece hA', npCount_cons_nonpiece hA,
    npCount_cons_nonpiece hB, npDefectSum_cons_nonpiece hA', npDefectSum_cons_nonpiece hA,
    npDefectSum_cons_nonpiece hB, hhub, hattach]
  omega

/-- **The local de-branch step preserves the vertex count.**  It only relocates `B`. -/
theorem usize_debranch_local (As rest : List UTree) (B : UTree) :
    usize (UTree.node (UTree.node (As ++ [B]) :: rest))
      = usize (UTree.node (UTree.node As :: B :: rest)) := by
  simp only [usize_node, usizeList_cons, usize_node, usizeList_append, usizeList_cons,
    usizeList_nil]
  omega

/-- **The local de-branch step IS a `StraightStep_sized`, modulo the Kelmans `Aobj` inequality.**
    The structural halves (`usize` preservation, `strDefect` −1) are proven here; the sole remaining
    hypothesis `hAobj` is Obligation A -- the Kelmans cavity inequality that pulling the branch `B`
    onto the hub does not decrease `Aobj` (Phase 0: strict on every genuine case). -/
theorem debranch_local_straightStep {As rest : List UTree} {B : UTree}
    (hAs : ∀ c ∈ As, isPiece c = true) (hB : isPiece B = false)
    (hA : isPiece (UTree.node As) = false) (hA' : isPiece (UTree.node (As ++ [B])) = false)
    (hAobj : Aobj (UTree.node (UTree.node As :: B :: rest))
           ≤ Aobj (UTree.node (UTree.node (As ++ [B]) :: rest))) :
    StraightStep_sized (UTree.node (UTree.node As :: B :: rest))
                       (UTree.node (UTree.node (As ++ [B]) :: rest)) :=
  ⟨(usize_debranch_local As rest B).symm, hAobj, by
    have h := strDefect_debranch_local (rest := rest) hAs hB hA hA'; omega⟩

end Step3
end R3Cert
