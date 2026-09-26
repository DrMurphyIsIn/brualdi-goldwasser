/-
  R4-R7 campaign, PHASE 7: the DEEP-HUB `pushInto` (tree->hub, Phase 3 -- full existence).

  The local de-branch step (`R47R7Debranch`) needs a HUB child.  A defect node without a hub child
  (e.g. `node [node [hubA], node [hubB]]`) needs the branch `B` attached to the DEEP hub along a
  sibling `A`'s spine.  `pushInto A B` performs that: it descends `A`'s (unique) non-piece child
  until it reaches a hub, then attaches `B` there.

    pushInto (node As) B = node (pushIntoList As B)
    pushIntoList []          B = [B]                                   -- hub: attach here
    pushIntoList (c :: rest) B = if isPiece c then c :: pushIntoList rest B
                                 else pushInto c B :: rest             -- descend the spine child

  What is PROVED here (no `sorry`, axiom-clean):
    * `usize_pushInto` -- `pushInto` preserves the vertex count (`usize (pushInto A B) = usize A + usize B`).

  The `strDefect` identity and the existence lemma follow.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Debranch
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

mutual
/-- Attach `B` to the deep hub along the first non-piece spine of `A`. -/
def pushInto : UTree → UTree → UTree
  | .node As, B => .node (pushIntoList As B)
/-- Attach `B` into the first non-piece child of a child list, or append it (hub reached). -/
def pushIntoList : List UTree → UTree → List UTree
  | [], B => [B]
  | c :: rest, B => if isPiece c then c :: pushIntoList rest B else pushInto c B :: rest
end

/-! ### Vertex-count preservation -/

mutual
theorem usize_pushInto : ∀ (A B : UTree), usize (pushInto A B) = usize A + usize B
  | .node As, B => by
      rw [pushInto, usize_node, usize_node, usizeList_pushIntoList]; omega
theorem usizeList_pushIntoList :
    ∀ (As : List UTree) (B : UTree), usizeList (pushIntoList As B) = usizeList As + usize B
  | [], B => by rw [pushIntoList, usizeList_cons, usizeList_nil]; omega
  | c :: rest, B => by
      rw [pushIntoList]
      split
      · rw [usizeList_cons, usizeList_pushIntoList, usizeList_cons]; omega
      · rw [usizeList_cons, usize_pushInto, usizeList_cons]; omega
end

/-! ### A node with a non-piece child is non-piece -/

theorem isPiece_node_of_mem_nonpiece {cs : List UTree} (h : ∃ e ∈ cs, isPiece e = false) :
    isPiece (UTree.node cs) = false := by
  obtain ⟨e, he, hep⟩ := h
  have hec : isCherry e = false := by
    rw [isPiece, Bool.or_eq_false_iff] at hep; exact hep.2
  rw [isPiece, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · show (cs.all isCherry) = false
    rw [Bool.eq_false_iff]
    intro hall
    exact absurd ((List.all_eq_true.mp hall) e he) (by rw [hec]; simp)
  · cases cs with
    | nil => rfl
    | cons c t =>
      cases t with
      | nil =>
        show isLeaf c = false
        rw [Bool.eq_false_iff]
        obtain rfl := List.mem_singleton.mp he
        intro hleaf
        rw [isLeaf_eq hleaf] at hep; simp [isPiece, isArm] at hep
      | cons c2 t2 => rfl

/-! ### The `strDefect` identity: `pushInto` inherits exactly the attached branch's defect -/

mutual
/-- `pushInto` into a defect-free (spine-like) subtree yields a subtree whose defect is exactly the
    attached branch `B`'s -- the deep hub absorbs `B` without adding any branch defect. -/
theorem strDefect_pushInto : ∀ (A B : UTree), strDefect A = 0 → isPiece B = false →
    strDefect (pushInto A B) = strDefect B
  | .node As, B, hA, hB => by
      have hnp : npCount As ≤ 1 ∧ npDefectSum As = 0 := by rw [strDefect] at hA; omega
      rw [pushInto, strDefect, npCount_pushIntoList As B hnp.1 hnp.2 hB,
        npDefectSum_pushIntoList As B hnp.1 hnp.2 hB]
      omega
theorem npCount_pushIntoList : ∀ (As : List UTree) (B : UTree),
    npCount As ≤ 1 → npDefectSum As = 0 → isPiece B = false → npCount (pushIntoList As B) = 1
  | [], B, _, _, hB => by rw [pushIntoList, npCount, npCount, if_neg (by rw [hB]; simp)]
  | c :: rest, B, hnc, hnd, hB => by
      rw [pushIntoList]
      split
      · rename_i hc
        rw [npCount, if_pos hc, Nat.zero_add]
        rw [npCount, if_pos hc] at hnc
        rw [npDefectSum, if_pos hc] at hnd
        exact npCount_pushIntoList rest B (by omega) (by omega) hB
      · rename_i hc
        rw [Bool.not_eq_true] at hc
        rw [npCount, if_neg (by rw [isPiece_pushInto c B hB]; simp)]
        rw [npCount, if_neg (by rw [hc]; simp)] at hnc
        omega
theorem npDefectSum_pushIntoList : ∀ (As : List UTree) (B : UTree),
    npCount As ≤ 1 → npDefectSum As = 0 → isPiece B = false →
    npDefectSum (pushIntoList As B) = strDefect B
  | [], B, _, _, hB => by simp [pushIntoList, npDefectSum, hB]
  | c :: rest, B, hnc, hnd, hB => by
      rw [pushIntoList]
      split
      · rename_i hc
        rw [npDefectSum, if_pos hc, Nat.zero_add]
        rw [npCount, if_pos hc] at hnc
        rw [npDefectSum, if_pos hc] at hnd
        exact npDefectSum_pushIntoList rest B (by omega) (by omega) hB
      · rename_i hc
        rw [Bool.not_eq_true] at hc
        rw [npDefectSum, if_neg (by rw [isPiece_pushInto c B hB]; simp)]
        rw [npDefectSum, if_neg (by rw [hc]; simp)] at hnd
        rw [npCount, if_neg (by rw [hc]; simp)] at hnc
        have hsc : strDefect c = 0 := by omega
        have hrest0 : npDefectSum rest = 0 := by omega
        rw [strDefect_pushInto c B hsc hB, hrest0]
        omega
theorem isPiece_pushInto : ∀ (A B : UTree), isPiece B = false → isPiece (pushInto A B) = false
  | .node As, B, hB => by
      rw [pushInto]; exact isPiece_node_of_mem_nonpiece (mem_nonpiece_pushIntoList As B hB)
theorem mem_nonpiece_pushIntoList : ∀ (As : List UTree) (B : UTree), isPiece B = false →
    ∃ e ∈ pushIntoList As B, isPiece e = false
  | [], B, hB => ⟨B, by rw [pushIntoList]; simp, hB⟩
  | c :: rest, B, hB => by
      rw [pushIntoList]
      split
      · obtain ⟨e, he, hep⟩ := mem_nonpiece_pushIntoList rest B hB
        exact ⟨e, List.mem_cons_of_mem _ he, hep⟩
      · exact ⟨pushInto c B, by simp, isPiece_pushInto c B hB⟩
end

/-! ### The deep-hub de-branch step (generalises the direct-hub step to spine-like `A`) -/

/-- **The deep-hub de-branch step drops `strDefect` by exactly 1.**  At a node whose first child `A`
    is defect-free and non-piece (a spine-like hub-chain) and whose second child `B` is non-piece,
    pushing `B` onto `A`'s deep hub drops the branch count by one while `A` inherits only `B`'s own
    defect.  Generalises `strDefect_debranch_local` (which needed `A` to be a DIRECT hub). -/
theorem strDefect_deephub_local {A B : UTree} {rest : List UTree}
    (hA0 : strDefect A = 0) (hA : isPiece A = false) (hB : isPiece B = false) :
    strDefect (UTree.node (pushInto A B :: rest)) + 1
      = strDefect (UTree.node (A :: B :: rest)) := by
  rw [strDefect, strDefect, npCount_cons_nonpiece (isPiece_pushInto A B hB),
    npCount_cons_nonpiece hA, npCount_cons_nonpiece hB,
    npDefectSum_cons_nonpiece (isPiece_pushInto A B hB), npDefectSum_cons_nonpiece hA,
    npDefectSum_cons_nonpiece hB, strDefect_pushInto A B hA0 hB, hA0]
  omega

/-- The deep-hub de-branch step preserves the vertex count. -/
theorem usize_deephub_local (A B : UTree) (rest : List UTree) :
    usize (UTree.node (pushInto A B :: rest)) = usize (UTree.node (A :: B :: rest)) := by
  simp only [usize_node, usizeList_cons, usize_pushInto]; omega

/-- **The deep-hub de-branch step IS a `StraightStep_sized`, modulo the Kelmans `Aobj` inequality.**
    The general (spine-like `A`) form of the de-branch move; structural halves proven, Obligation A
    isolated. -/
theorem deephub_local_straightStep {A B : UTree} {rest : List UTree}
    (hA0 : strDefect A = 0) (hA : isPiece A = false) (hB : isPiece B = false)
    (hAobj : Aobj (UTree.node (A :: B :: rest)) ≤ Aobj (UTree.node (pushInto A B :: rest))) :
    StraightStep_sized (UTree.node (A :: B :: rest)) (UTree.node (pushInto A B :: rest)) :=
  ⟨(usize_deephub_local A B rest).symm, hAobj, by
    have h := strDefect_deephub_local (rest := rest) hA0 hA hB; omega⟩

end Step3
end R3Cert
