/-
  R4-R7 campaign, PHASE 7: DEEP-permutation invariance of `Aobj` (tree->hub, Pass 4).

  `Aobj_node_perm` (R47ArmPerm) proves `Aobj` invariant under permuting a node's children at the
  ROOT.  This file extends it to permutations at ANY depth: two trees related by reordering
  children at every level have equal `Aobj`.  This is the reverse anchor the straightening decode
  needs -- a defect-zero tree is a backbone with children permuted at every level, and deep-perm
  invariance turns that into `Aobj`-equality with an actual `backboneU s`.

  The engine: `Ztot`/`Zopen` of a realized node depend on its children only through the triple
  `(weight, Ztot child, Zopen child)` (the cavity recursion is a symmetric function of that data),
  so equal-data children give equal `Ztot`/`Zopen` (`Popen_Matched_congr`); and a child
  permutation is already handled by `Ztot_node_perm`/`Zopen_node_perm`.

  What is PROVED here (no `sorry`, axiom-clean):
    * `Popen_Matched_congr` -- `Popen`/`Matched` depend only on the children's `(w, Ztot, Zopen)`;
    * `DeepPerm` + `deepPerm_refl` -- the deep child-permutation equivalence;
    * `deepPerm_subInv` -- deep-perm trees share `(udeg, Ztot∘dtSub, Zopen∘dtSub)`;
    * `deepPerm_Aobj` -- **`Aobj` is invariant under deep permutation** (the anchor).

  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47Perm
import R3Cert.R47ArmPerm
import R3Cert.R47R7Straighten

namespace R3Cert
namespace Step3

open RTree

/-! ### `Popen`/`Matched` depend only on the children's `(weight, Ztot, Zopen)` -/

/-- Realized children carry equal cavity data. -/
def PData (p q : ℝ × RTree) : Prop :=
  p.1 = q.1 ∧ Ztot p.2 = Ztot q.2 ∧ Zopen p.2 = Zopen q.2

/-- `Popen` and `Matched` are congruences for `PData`: they see children only through
    `(weight, Ztot, Zopen)`. -/
theorem Popen_Matched_congr {l1 l2 : List (ℝ × RTree)} (h : List.Forall₂ PData l1 l2) :
    Popen l1 = Popen l2 ∧ Matched l1 = Matched l2 := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons p q l1' l2' hpq hrest ih =>
    obtain ⟨w, c⟩ := p
    obtain ⟨w', c'⟩ := q
    obtain ⟨hw, hzt, hzo⟩ := hpq
    obtain ⟨ihP, ihM⟩ := ih
    simp only at hw hzt hzo
    refine ⟨?_, ?_⟩
    · rw [Popen, Popen, hzt, ihP]
    · rw [Matched, Matched, hw, hzt, hzo, ihP, ihM]

/-! ### Subtree invariants and the child-list lift -/

/-- Two subtrees share their realized `(udeg, Ztot∘dtSub, Zopen∘dtSub)`. -/
def SubInv (K K' : UTree) : Prop :=
  udeg K = udeg K' ∧ Ztot (dtSub K) = Ztot (dtSub K') ∧ Zopen (dtSub K) = Zopen (dtSub K')

/-- `SubInv` children lift to `PData` on the realized child lists (equal degree). -/
theorem dtChildren_forall2 (d : ℕ) {cs ds : List UTree} (h : List.Forall₂ SubInv cs ds) :
    List.Forall₂ PData (dtChildren d cs) (dtChildren d ds) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons K K' cs' ds' hKK' hrest ih =>
    rw [dtChildren_cons, dtChildren_cons]
    obtain ⟨hu, hzt, hzo⟩ := hKK'
    exact List.Forall₂.cons ⟨by simp only [hu], hzt, hzo⟩ ih

/-- **The congruence + permutation step.**  If a child list is `SubInv`-related element-wise to
    `ds`, and `ds` is a permutation of `es`, then the realized node's `Ztot` and `Zopen` agree at
    any degree `d`.  (Congruence via `Popen_Matched_congr`, reorder via `Ztot`/`Zopen_node_perm`.) -/
theorem node_deep_eq (d : ℕ) {cs ds es : List UTree}
    (hsub : List.Forall₂ SubInv cs ds) (hperm : ds.Perm es) :
    Ztot (RTree.node (dtChildren d cs)) = Ztot (RTree.node (dtChildren d es))
    ∧ Zopen (RTree.node (dtChildren d cs)) = Zopen (RTree.node (dtChildren d es)) := by
  obtain ⟨hP, hM⟩ := Popen_Matched_congr (dtChildren_forall2 d hsub)
  have hperm' : (dtChildren d ds).Perm (dtChildren d es) := by
    rw [dtChildren_eq_map, dtChildren_eq_map]; exact hperm.map _
  refine ⟨?_, ?_⟩
  · calc Ztot (RTree.node (dtChildren d cs))
        = Ztot (RTree.node (dtChildren d ds)) := by rw [Ztot, Ztot, hP, hM]
      _ = Ztot (RTree.node (dtChildren d es)) := Ztot_node_perm hperm'
  · calc Zopen (RTree.node (dtChildren d cs))
        = Zopen (RTree.node (dtChildren d ds)) := by rw [Zopen, Zopen, hP]
      _ = Zopen (RTree.node (dtChildren d es)) := Zopen_node_perm hperm'

/-! ### Deep permutation -/

/-- Two trees are DEEP-permutation equivalent when their children are deep-perm related
    element-wise up to a reordering.  Reflexive; captures reordering children at every level. -/
inductive DeepPerm : UTree → UTree → Prop
  | mk {cs ds es : List UTree} (hcong : List.Forall₂ DeepPerm cs ds) (hperm : ds.Perm es) :
      DeepPerm (UTree.node cs) (UTree.node es)

mutual
/-- Deep-perm trees share their subtree invariants `(udeg, Ztot∘dtSub, Zopen∘dtSub)`. -/
theorem deepPerm_subInv : ∀ {t t' : UTree}, DeepPerm t t' → SubInv t t'
  | _, _, @DeepPerm.mk cs ds es hcong hperm => by
      have hsub : List.Forall₂ SubInv cs ds := deepPerm_subInv_list hcong
      have hle : cs.length = es.length := hsub.length_eq.trans hperm.length_eq
      refine ⟨?_, ?_, ?_⟩
      · rw [udeg_node, udeg_node, hle]
      · rw [dtSub_node, dtSub_node, hle]; exact (node_deep_eq (es.length + 1) hsub hperm).1
      · rw [dtSub_node, dtSub_node, hle]; exact (node_deep_eq (es.length + 1) hsub hperm).2
/-- Element-wise `deepPerm_subInv` over a child list. -/
theorem deepPerm_subInv_list :
    ∀ {cs ds : List UTree}, List.Forall₂ DeepPerm cs ds → List.Forall₂ SubInv cs ds
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons h hrest =>
      List.Forall₂.cons (deepPerm_subInv h) (deepPerm_subInv_list hrest)
end

mutual
/-- Deep permutation is reflexive. -/
theorem deepPerm_refl : ∀ t : UTree, DeepPerm t t
  | .node cs => DeepPerm.mk (deepPerm_refl_list cs) (List.Perm.refl cs)
/-- Element-wise reflexivity over a child list. -/
theorem deepPerm_refl_list : ∀ cs : List UTree, List.Forall₂ DeepPerm cs cs
  | [] => List.Forall₂.nil
  | c :: rest => List.Forall₂.cons (deepPerm_refl c) (deepPerm_refl_list rest)
end

/-- **`Aobj` is invariant under deep permutation** -- `Aobj_node_perm` extended to all depths.
    The reverse anchor: reordering children at any level leaves the objective unchanged. -/
theorem deepPerm_Aobj {t t' : UTree} (h : DeepPerm t t') : Aobj t = Aobj t' := by
  cases h with
  | @mk cs ds es hcong hperm =>
    have hsub : List.Forall₂ SubInv cs ds := deepPerm_subInv_list hcong
    have hle : cs.length = es.length := hsub.length_eq.trans hperm.length_eq
    simp only [Aobj, dtRealize_node]
    rw [hle]
    exact (node_deep_eq es.length hsub hperm).1

/-! ### Composition: the literal tree->hub, modulo straightening progress + the decode -/

/-- **The tree->hub reduction, composed via the deep-perm anchor.**  Given straightening progress
    and the structural DECODE (every defect-zero tree is deep-perm equivalent to a backbone), every
    tree is `Aobj`-dominated by a hub-backbone.  This is the literal `tree_to_hub`, now resting on
    exactly two obligations: `StraightProgress` (the Kelmans-straighten move existence) and the
    decode -- which the deep-perm anchor `deepPerm_Aobj` reduces to a purely STRUCTURAL extraction
    (`Aobj`-equality no longer needs to nest; a defect-zero tree is a backbone with children
    reordered at every level). -/
theorem tree_to_hub_of_progress_decode
    (hprog : StraightProgress)
    (hdecode : ∀ t : UTree, strDefect t = 0 → ∃ s : List Hub, DeepPerm t (backboneU s)) :
    ∀ t : UTree, ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) := by
  intro t
  obtain ⟨n, hn0, hle⟩ := straighten_to_defectZero hprog t
  obtain ⟨s, hdp⟩ := hdecode n hn0
  exact ⟨s, hle.trans (le_of_eq (deepPerm_Aobj hdp))⟩

end Step3
end R3Cert
