/-
  Single-edge root-shift Aobj-invariance -- the crux enabler for a `RerootStep` coverage class.

  Rerooting a tree at an adjacent child is the structural move
      node (node ds :: rest)   →   node (ds ++ [node rest])
  (the child `node ds` becomes the new root, keeping its children `ds` and gaining a new child
  `node rest` = the old root minus that child).  It is `Aobj`-INVARIANT: in the cavity model both sides
  reduce, after dividing by the common child products, to the SAME real-var expression (verified exactly:
  `(1 + T/(b+1))·(1 + (S + 1/(b+1+T))/(a+1)) = (1 + S/(a+1))·(1 + (1/(a+1+S) + T)/(b+1))`, an identity in
  `a=|ds|, b=|rest|, S=qSum ds, T=qSum rest`).  So Aobj-invariance for an ARBITRARY reroot follows by
  COMPOSING this single-shift identity -- no `SimpleGraph.Iso` needed.

  This discharges the `Aobj`-equality half of a `RerootStep`; combined with the (trivial) `usize` equality
  and a lower-`strDefect` target rooting it gives a `StraightStep_sized`, extending `CoverR` toward the
  measured 99.3% coverage (see `proof/verification/COVER_RELATION_STATUS.md`).

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLFlpDeepLift
import R3Cert.R47BackboneAmp
import R3Cert.R47R7Sized

namespace R3Cert
namespace Step3

open RTree

private theorem prod_Ztot_pos (l : List UTree) : 0 < (l.map fun K => Ztot (dtSub K)).prod := by
  apply List.prod_pos; intro x hx; rw [List.mem_map] at hx; obtain ⟨K, _, rfl⟩ := hx; exact Ztot_dt_pos K

/-- `qContrib (node cs) = 1 / (|cs| + 1 + qSum cs)` (the product cancels). -/
theorem qContrib_node (cs : List UTree) :
    Zopen (dtSub (UTree.node cs)) / Ztot (dtSub (UTree.node cs)) / (udeg (UTree.node cs) : ℝ)
      = 1 / ((cs.length : ℝ) + 1 + qSum cs) := by
  have hP : 0 < (cs.map fun K => Ztot (dtSub K)).prod := prod_Ztot_pos cs
  have hQ : 0 ≤ qSum cs := qSum_nonneg cs
  rw [Zopen_dtSub_node_eq, Ztot_dtSub_node_eq, udeg_node]
  have hd1 : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hd2 : (0:ℝ) < (cs.length : ℝ) + 1 + qSum cs := by positivity
  push_cast; field_simp

/-- `qSum` of a singleton is the single child's `qContrib`. -/
private theorem qSum_one (t : UTree) :
    qSum [t] = Zopen (dtSub t) / Ztot (dtSub t) / (udeg t : ℝ) := by
  simp only [qSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **The single-edge root-shift preserves `Aobj`.** -/
theorem Aobj_rootShift (ds rest : List UTree) :
    Aobj (UTree.node (ds ++ [UTree.node rest])) = Aobj (UTree.node (UTree.node ds :: rest)) := by
  have hPD : 0 < (ds.map fun K => Ztot (dtSub K)).prod := prod_Ztot_pos ds
  have hPR : 0 < (rest.map fun K => Ztot (dtSub K)).prod := prod_Ztot_pos rest
  have hQS : 0 ≤ qSum ds := qSum_nonneg ds
  have hQT : 0 ≤ qSum rest := qSum_nonneg rest
  rw [Aobj_factor, Aobj_factor]
  -- LHS map/prod/qSum/length
  rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
    mul_one, qSum_append, qSum_one, List.length_append, List.length_cons, List.length_nil]
  -- RHS map/prod/qSum/length
  rw [List.map_cons, List.prod_cons, qSum_cons, List.length_cons]
  -- qContrib FIRST (before Ztot rewrites its denominator), then the product Ztot
  rw [qContrib_node rest, qContrib_node ds, Ztot_dtSub_node_eq rest, Ztot_dtSub_node_eq ds]
  -- now a pure real identity
  have hdA : (0:ℝ) < (ds.length : ℝ) + 1 := by positivity
  have hdB : (0:ℝ) < (rest.length : ℝ) + 1 := by positivity
  have hdA' : (0:ℝ) < (ds.length : ℝ) + 1 + qSum ds := by positivity
  have hdB' : (0:ℝ) < (rest.length : ℝ) + 1 + qSum rest := by positivity
  have hne0 : ((0:ℕ):ℝ) + 1 ≠ 0 := by norm_num
  push_cast
  field_simp
  ring

/-- The root-shift preserves the vertex count. -/
theorem usize_rootShift (ds rest : List UTree) :
    usize (UTree.node (UTree.node ds :: rest)) = usize (UTree.node (ds ++ [UTree.node rest])) := by
  simp only [usize_node, usizeList_cons, usizeList_append, usizeList_nil]
  omega

/-- **The single-edge root-shift as a straightening step relation.**  Reroot to the adjacent child when
    that lowers `strDefect` (`Aobj` equal by `Aobj_rootShift`, `usize` equal). -/
def RootShiftStep (t t' : UTree) : Prop :=
  ∃ ds rest : List UTree,
    t = UTree.node (UTree.node ds :: rest) ∧ t' = UTree.node (ds ++ [UTree.node rest]) ∧
    strDefect t' < strDefect t

theorem RootShiftStep.straightStep {t t' : UTree} (h : RootShiftStep t t') : StraightStep_sized t t' := by
  obtain ⟨ds, rest, rfl, rfl, hlt⟩ := h
  exact ⟨usize_rootShift ds rest, le_of_eq (Aobj_rootShift ds rest).symm, hlt⟩

/-! ### Composite reroot: reach ANY rerooting via shifts + child-reorderings, `Aobj`/`usize` invariant -/

/-- One elementary re-rooting move: shift the root to its first child, OR reorder the root's children
    (needed to bring any child to the front before shifting). -/
def RerootStep1 (t t' : UTree) : Prop :=
  (∃ ds rest : List UTree, t = UTree.node (UTree.node ds :: rest) ∧ t' = UTree.node (ds ++ [UTree.node rest]))
    ∨ (∃ cs cs' : List UTree, cs.Perm cs' ∧ t = UTree.node cs ∧ t' = UTree.node cs')

theorem RerootStep1.aobj {t t' : UTree} (h : RerootStep1 t t') : Aobj t = Aobj t' := by
  rcases h with ⟨ds, rest, rfl, rfl⟩ | ⟨cs, cs', hp, rfl, rfl⟩
  · exact (Aobj_rootShift ds rest).symm
  · exact Aobj_node_perm hp

theorem RerootStep1.usize {t t' : UTree} (h : RerootStep1 t t') : usize t = usize t' := by
  rcases h with ⟨ds, rest, rfl, rfl⟩ | ⟨cs, cs', hp, rfl, rfl⟩
  · exact usize_rootShift ds rest
  · rw [usize_node, usize_node, usizeList_perm hp]

/-- The reflexive-transitive closure: `t'` is any rerooting/reordering of `t`. -/
def RerootRel : UTree → UTree → Prop := Relation.ReflTransGen RerootStep1

theorem RerootRel.aobj {t t' : UTree} (h : RerootRel t t') : Aobj t = Aobj t' := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans hbc.aobj

theorem RerootRel.usize {t t' : UTree} (h : RerootRel t t') : usize t = usize t' := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans hbc.usize

/-- **The composite reroot as a straightening step**: reroot to ANY lower-`strDefect` rooting.  `Aobj` and
    `usize` are invariant (composed over `Aobj_rootShift` / `Aobj_node_perm`), so this is a
    `StraightStep_sized` whenever the target rooting has strictly lower defect.  Reaching the measured 99.3%
    coverage (`COVER_RELATION_STATUS.md`). -/
def CompRerootStep (t t' : UTree) : Prop := RerootRel t t' ∧ strDefect t' < strDefect t

theorem CompRerootStep.straightStep {t t' : UTree} (h : CompRerootStep t t') : StraightStep_sized t t' :=
  ⟨h.1.usize, le_of_eq h.1.aobj, h.2⟩

end Step3
end R3Cert
