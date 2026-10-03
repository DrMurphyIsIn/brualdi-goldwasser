import Mathlib
import R3Cert.BGMaximizer
import R3Cert.BGSpiderRule

namespace R3Cert
namespace RerootEquiv

open R3Cert.RTree R3Cert.Step3 BGSpiderOpt BGSpiderRule

/-! ### `RerootRel` is an equivalence relation -/

theorem shift (ds rest : List UTree) :
    RerootRel (UTree.node (UTree.node ds :: rest)) (UTree.node (ds ++ [UTree.node rest])) :=
  Relation.ReflTransGen.single (Or.inl ⟨ds, rest, rfl, rfl⟩)

theorem perm {cs cs' : List UTree} (h : cs.Perm cs') : RerootRel (UTree.node cs) (UTree.node cs') :=
  Relation.ReflTransGen.single (Or.inr ⟨cs, cs', h, rfl, rfl⟩)

/-- The inverse of a root shift is a reorder, a shift and a reorder. -/
theorem shift_inv (ds rest : List UTree) :
    RerootRel (UTree.node (ds ++ [UTree.node rest])) (UTree.node (UTree.node ds :: rest)) := by
  have h1 : (ds ++ [UTree.node rest]).Perm (UTree.node rest :: ds) := List.perm_append_singleton _ _
  have h2 : (rest ++ [UTree.node ds]).Perm (UTree.node ds :: rest) := List.perm_append_singleton _ _
  exact ((perm h1).trans (shift rest ds)).trans (perm h2)

theorem step_symm {t t' : UTree} (h : RerootStep1 t t') : RerootRel t' t := by
  rcases h with ⟨ds, rest, rfl, rfl⟩ | ⟨cs, cs', hp, rfl, rfl⟩
  · exact shift_inv ds rest
  · exact perm hp.symm

theorem symm {t t' : UTree} (h : RerootRel t t') : RerootRel t' t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (step_symm hbc).trans ih

/-- `RerootRel` (rerooting and reordering children) is an equivalence relation. -/
theorem equivalence : Equivalence RerootRel :=
  ⟨fun _ => Relation.ReflTransGen.refl, symm, Relation.ReflTransGen.trans⟩

/-! ### Concrete moves on spiders -/

theorem spiderU_perm {l l' : List Child} (h : l.Perm l') : RerootRel (spiderU l) (spiderU l') :=
  perm (h.map childU)

/-- Rerooting a spider `C^C A_s` at its arm vertex gives the spider `C^s A_C`. -/
theorem swap (C s : ℕ) :
    RerootRel (spiderU (List.replicate C Child.cherry ++ [Child.arm s]))
      (spiderU (List.replicate s Child.cherry ++ [Child.arm C])) := by
  unfold spiderU
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, childU]
  have hp : (List.replicate C cherryU ++ [armU s]).Perm (armU s :: List.replicate C cherryU) :=
    List.perm_append_singleton _ _
  refine (perm hp).trans ?_
  exact shift (List.replicate s cherryU) (List.replicate C cherryU)

/-- Rerooting the spider `A_J A_0` at its arm vertex gives the all-cherry spider `C^(J+1)`. -/
theorem leafArm (J : ℕ) :
    RerootRel (spiderU [Child.arm J, Child.arm 0]) (spiderU (List.replicate (J + 1) Child.cherry)) := by
  unfold spiderU
  simp only [List.map_cons, List.map_nil, List.map_replicate, childU]
  have e : List.replicate (J + 1) cherryU = List.replicate J cherryU ++ [UTree.node [armU 0]] := by
    rw [List.replicate_succ']; rfl
  rw [e]
  exact shift (List.replicate J cherryU) [armU 0]

theorem leafArm' (J : ℕ) :
    RerootRel (spiderU [Child.arm 0, Child.arm J]) (spiderU (List.replicate (J + 1) Child.cherry)) :=
  (spiderU_perm (List.Perm.swap _ _ [])).trans (leafArm J)

/-! ### Paths -/

/-- The path on `k + 1` vertices rooted at an end. -/
def pathU : ℕ → UTree
  | 0 => UTree.node []
  | k + 1 => UTree.node [pathU k]

theorem usize_pathU (k : ℕ) : usize (pathU k) = k + 1 := by
  induction k with
  | zero => simp [pathU, usize_node, usizeList_nil]
  | succ k ih => simp only [pathU, usize_node, usizeList_cons, usizeList_nil, ih]; omega

/-- A path rooted at an inner vertex is a rerooting of the path rooted at an end. -/
theorem path_two (a b : ℕ) :
    RerootRel (UTree.node [pathU a, pathU b]) (UTree.node [pathU (a + b + 1)]) := by
  induction a generalizing b with
  | zero =>
    have := shift [] [pathU b]
    simpa [pathU, Nat.add_comm] using this
  | succ a ih =>
    have h1 := shift [pathU a] [pathU b]
    have h2 := ih (b + 1)
    simp only [List.cons_append, List.nil_append] at h1
    have e : a + (b + 1) + 1 = a + 1 + b + 1 := by omega
    rw [e] at h2
    exact h1.trans h2

/-! ### A rerooting invariant: the number of leaves -/

mutual
/-- Leaves of a subtree hanging below its parent. -/
def lvT : UTree → ℕ
  | .node cs => (if cs.length = 0 then 1 else 0) + lvL cs
def lvL : List UTree → ℕ
  | [] => 0
  | c :: t => lvT c + lvL t
end

/-- Leaves of a rooted tree (the root counts when it has exactly one child). -/
def lvR : UTree → ℕ
  | .node cs => (if cs.length = 1 then 1 else 0) + lvL cs

theorem lvL_eq (l : List UTree) : lvL l = (l.map lvT).sum := by
  induction l with
  | nil => simp [lvL]
  | cons c t ih => simp [lvL, ih]

theorem lvL_append (a b : List UTree) : lvL (a ++ b) = lvL a + lvL b := by
  simp [lvL_eq]

theorem lvL_perm {a b : List UTree} (h : a.Perm b) : lvL a = lvL b := by
  rw [lvL_eq, lvL_eq]; exact (h.map lvT).sum_eq

theorem lvR_step {t t' : UTree} (h : RerootStep1 t t') : lvR t = lvR t' := by
  rcases h with ⟨ds, rest, rfl, rfl⟩ | ⟨cs, cs', hp, rfl, rfl⟩
  · simp only [lvR, lvL, lvT, lvL_append, List.length_cons, List.length_append, List.length_singleton]
    by_cases hd : ds.length = 0 <;> by_cases hr : rest.length = 0 <;> simp [hd, hr] <;> omega
  · simp only [lvR, hp.length_eq, lvL_perm hp]

theorem lvR_rel {t t' : UTree} (h : RerootRel t t') : lvR t = lvR t' := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (lvR_step hbc)

end RerootEquiv
end R3Cert
