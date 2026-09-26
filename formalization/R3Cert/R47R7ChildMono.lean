/-
  R4-R7 campaign, PHASE 7: the Aobj-monotone rewrite GENERATOR (tree->hub, Pass 1).

  The tree->hub reduction schema (`R47R7TreeToHub.treeToHub_of_rewrite`) needs a concrete
  `Aobj`-non-decreasing rewrite `R`.  This file supplies the single reusable GENERATOR of such
  rewrites: CHILD-REPLACEMENT MONOTONICITY.

  The cavity recursion is linear with NONNEGATIVE coefficients in each child
  (`R47R6SpineMono.Ztot_node_snoc`): `Ztot(node) = C1·Ztot(dtSub child) + C2·Zopen(dtSub child)`.
  Hence replacing ANY child `T` by `T'` that raises both `Ztot(dtSub)` and `Zopen(dtSub)` at
  EQUAL degree (`udeg T = udeg T'`) never decreases the root's `Aobj`.  Every concrete monotone
  move of the Kelmans campaign (topped-up merge, arm resize, leg->cherry) instantiates this by
  exhibiting its local `(Ztot, Zopen)` gain; the `spine_balance_pair` induction (same file) then
  propagates a gain at any DEPTH up to the root.

  What is PROVED here (no `sorry`, axiom-clean):
    * `Aobj_tail_child_replace_le` -- replacing the LAST root child monotonically;
    * `Aobj_child_replace_le`      -- replacing ANY root child (via `Aobj_node_perm`).

  These are the first concrete witnesses of `R47R7TreeToHub.RewriteMonotone`: a rewrite built
  from degree-preserving, `(Ztot,Zopen)`-raising subtree replacements is `Aobj`-monotone.

  HONEST SCOPE.  Root-child replacement (any depth follows by reusing `spine_balance_pair`'s
  induction, deferred to the Kelmans-merge brick which supplies the local gain).  Genuine proof
  (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6SpineMono
import R3Cert.R47ArmPerm
import R3Cert.R47R7TreeToHub

namespace R3Cert
namespace Step3

open RTree

/-- **Tail child-replacement is `Aobj`-monotone.**  Replacing the last child `T` of the root by
    `T'` with not-smaller `(Ztot, Zopen)` of its realized subtree, at equal `udeg`, does not
    decrease `Aobj`.  Direct from `node_Ztot_child_mono` at the root degree. -/
theorem Aobj_tail_child_replace_le (pre : List UTree) (T T' : UTree)
    (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T'))
    (hzo : Zopen (dtSub T) ≤ Zopen (dtSub T'))
    (hu : udeg T = udeg T') :
    Aobj (UTree.node (pre ++ [T])) ≤ Aobj (UTree.node (pre ++ [T'])) := by
  simp only [Aobj, dtRealize_node]
  have hlenT : (pre ++ [T]).length = pre.length + 1 := by simp
  have hlenT' : (pre ++ [T']).length = pre.length + 1 := by simp
  rw [hlenT, hlenT']
  exact node_Ztot_child_mono pre T T' (pre.length + 1) hzt hzo hu

/-- **Any-position child-replacement is `Aobj`-monotone.**  Replacing an arbitrary root child `T`
    (with `pre`/`post` siblings) by `T'` of not-smaller `(Ztot, Zopen)` at equal `udeg` does not
    decrease `Aobj`.  Reduces to `Aobj_tail_child_replace_le` by permuting `T` to the tail via the
    already-proven `Aobj_node_perm`. -/
theorem Aobj_child_replace_le (pre post : List UTree) (T T' : UTree)
    (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T'))
    (hzo : Zopen (dtSub T) ≤ Zopen (dtSub T'))
    (hu : udeg T = udeg T') :
    Aobj (UTree.node (pre ++ T :: post)) ≤ Aobj (UTree.node (pre ++ T' :: post)) := by
  have hperm : ∀ X : UTree, (pre ++ X :: post).Perm ((pre ++ post) ++ [X]) := by
    intro X
    have h1 : (X :: post).Perm (post ++ [X]) := by
      simpa using (List.perm_append_comm (l₁ := [X]) (l₂ := post))
    have h2 := h1.append_left pre
    rw [List.append_assoc]
    exact h2
  calc Aobj (UTree.node (pre ++ T :: post))
      = Aobj (UTree.node ((pre ++ post) ++ [T])) := Aobj_node_perm (hperm T)
    _ ≤ Aobj (UTree.node ((pre ++ post) ++ [T'])) :=
        Aobj_tail_child_replace_le (pre ++ post) T T' hzt hzo hu
    _ = Aobj (UTree.node (pre ++ T' :: post)) := (Aobj_node_perm (hperm T')).symm

/-- **The child-replacement rewrite relation.**  One root child is replaced by a
    degree-preserving subtree of not-smaller `(Ztot, Zopen)`.  Every concrete Kelmans/leg-cherry
    move is a sub-relation of this (each is a subtree replacement that raises the child's cavity
    quantities), so all of them inherit `Aobj`-monotonicity from `childReplace_monotone`. -/
inductive ChildReplace : UTree → UTree → Prop
  | mk (pre post : List UTree) (T T' : UTree)
      (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T'))
      (hzo : Zopen (dtSub T) ≤ Zopen (dtSub T'))
      (hu : udeg T = udeg T') :
      ChildReplace (UTree.node (pre ++ T :: post)) (UTree.node (pre ++ T' :: post))

/-- **The `RewriteMonotone` obligation, discharged for the child-replacement generator.**  This
    is the first of the three tree->hub schema obligations closed for a concrete rewrite family:
    `ChildReplace` never decreases `Aobj`.  The concrete Kelmans rewrite, being a sub-relation,
    reuses this directly. -/
theorem childReplace_monotone : RewriteMonotone ChildReplace := by
  intro t t' h
  cases h with
  | mk pre post T T' hzt hzo hu => exact Aobj_child_replace_le pre post T T' hzt hzo hu

end Step3
end R3Cert
