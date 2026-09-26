/-
  Bridge STEP 4h: THE WEIGHT-COUNT THEOREM -- every edge of a good realized tree carries
  `1 / (count(parent) * count(child))`.

  The mutual induction (`emission_weights`/`emissionList_weights`) walks the emitters with
  two carried facts: the ambient count of the current root equals its `GoodTree` degree, and
  the ambient list is BLIND to the emission's interior (counts there equal the local counts).
  At each head child: the parent-edge weight is exactly `1/(d * (childCount c + 1))`
  (`GoodTree`), and the ambient count of the child address is `1 + childCount c`
  (`count_head_child` + blindness); the head subtree recurses with the re-based facts (the
  isolation lemmas of 4f/4g zero out everything else); the tail shifts the index.

  `realize_weights` instantiates at the true root (`rEdges_countRoot`), giving: for every
  `GoodTree`-realization (in particular `litHub`, by `litHub_good`), every edge weight is
  the reciprocal degree product of the realized graph -- the `hw` hypothesis of
  `isEdgeEnum_liftEdges` up to the 4e/4f count bridges.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4g

namespace R3Cert
namespace Step3

open RTree

mutual

theorem emission_weights (E : List AEdge) : ∀ (a : List ℕ) (t : RTree) (d : ℕ),
    GoodTree d t →
    E.countP (touchB a) = d →
    (∀ x k, (k :: a) <:+ x →
      E.countP (touchB x) = (rEdges a t).countP (touchB x)) →
    ∀ e ∈ rEdges a t,
      e.2.2 = 1 / ((E.countP (touchB e.1) : ℝ) * (E.countP (touchB e.2.1) : ℝ))
  | a, .node cs, d, hg, hroot, hblind, e, he => by
    rw [rEdges] at he
    refine emissionList_weights E a 0 d cs hg.members hroot ?_ e he
    intro x k _ hkx
    have hx := hblind x k hkx
    rw [rEdges] at hx
    exact hx

theorem emissionList_weights (E : List AEdge) : ∀ (a : List ℕ) (i d : ℕ)
    (cs : List (ℝ × RTree)),
    (∀ p ∈ cs, p.1 = 1 / ((d : ℝ) * ((childCount p.2 : ℝ) + 1))
      ∧ GoodTree (childCount p.2 + 1) p.2) →
    E.countP (touchB a) = d →
    (∀ x k, i ≤ k → (k :: a) <:+ x →
      E.countP (touchB x) = (rRoot a i cs ++ rSub a i cs).countP (touchB x)) →
    ∀ e ∈ rRoot a i cs ++ rSub a i cs,
      e.2.2 = 1 / ((E.countP (touchB e.1) : ℝ) * (E.countP (touchB e.2.1) : ℝ))
  | a, i, d, [], _, _, _, e, he => by
    rw [rRoot, rSub] at he
    exact absurd he (by simp)
  | a, i, d, (w, c) :: rest, hgood, hroot, hblind, e, he => by
    have hw_head := hgood (w, c) (List.mem_cons.mpr (Or.inl rfl))
    have hw1 : w = 1 / ((d : ℝ) * ((childCount c : ℝ) + 1)) := hw_head.1
    have hg2 : GoodTree (childCount c + 1) c := hw_head.2
    have hgood' : ∀ p ∈ rest, p.1 = 1 / ((d : ℝ) * ((childCount p.2 : ℝ) + 1))
        ∧ GoodTree (childCount p.2 + 1) p.2 :=
      fun p hp => hgood p (List.mem_cons.mpr (Or.inr hp))
    have hcnt_child : E.countP (touchB (i :: a)) = 1 + childCount c := by
      rw [hblind (i :: a) i (le_refl i) (List.suffix_refl _)]
      exact count_head_child a i w c rest
    -- the tail is blind past index i
    have hblind' : ∀ x k, i + 1 ≤ k → (k :: a) <:+ x →
        E.countP (touchB x)
          = (rRoot a (i + 1) rest ++ rSub a (i + 1) rest).countP (touchB x) := by
      intro x k hik hkx
      have hxa : x ≠ a := by
        intro h
        rw [h] at hkx
        have := hkx.length_le
        simp only [List.length_cons] at this
        omega
      have hxia : x ≠ i :: a := by
        intro h
        rw [h] at hkx
        have heq2 : (k :: a) = (i :: a) :=
          suffix_eq_of_length hkx (List.suffix_refl _) (by simp)
        simp only [List.cons.injEq] at heq2
        omega
      have h1 : touchB x (a, i :: a, w) = false := by
        simp only [touchB, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        exact ⟨fun h => hxa h.symm, fun h => hxia h.symm⟩
      have h2 : (rEdges (i :: a) c).countP (touchB x) = 0 := by
        refine rEdges_count_notSuffix _ _ _ ?_
        intro hsuf
        have heq2 : (i :: a) = (k :: a) := suffix_eq_of_length hsuf hkx (by simp)
        simp only [List.cons.injEq] at heq2
        omega
      rw [hblind x k (by omega) hkx, rRoot, rSub, List.cons_append, List.countP_cons,
        List.countP_append, List.countP_append, h1, if_neg Bool.false_ne_true, h2,
        List.countP_append]
      omega
    have htail := emissionList_weights E a (i + 1) d rest hgood' hroot hblind'
    -- the head subtree is blind below `i :: a`
    have hblind'' : ∀ x k, (k :: (i :: a)) <:+ x →
        E.countP (touchB x) = (rEdges (i :: a) c).countP (touchB x) := by
      intro x k hkx
      have hia_x : (i :: a) <:+ x := (List.suffix_cons k (i :: a)).trans hkx
      have hlen : a.length + 2 ≤ x.length := by
        have := hkx.length_le
        simp only [List.length_cons] at this
        omega
      have hxa : x ≠ a := by
        intro h
        rw [h] at hlen
        omega
      have hxia : x ≠ i :: a := by
        intro h
        rw [h] at hlen
        simp only [List.length_cons] at hlen
        omega
      have h1 : touchB x (a, i :: a, w) = false := by
        simp only [touchB, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        exact ⟨fun h => hxa h.symm, fun h => hxia h.symm⟩
      have h2 : (rRoot a (i + 1) rest).countP (touchB x) = 0 :=
        rRoot_count_deep a rest (i + 1) x (by omega)
      have h3 : (rSub a (i + 1) rest).countP (touchB x) = 0 :=
        rSub_count_other a rest (i + 1) i x (by omega) hia_x
      rw [hblind x i (le_refl i) hia_x, rRoot, rSub, List.cons_append, List.countP_cons,
        List.countP_append, List.countP_append, h1, if_neg Bool.false_ne_true, h2, h3]
      omega
    have hchild := emission_weights E (i :: a) c (childCount c + 1) hg2
      (by omega) hblind''
    rw [rRoot, rSub] at he
    rcases List.mem_append.mp he with hL | hR
    · rcases List.mem_cons.mp hL with heq | hL'
      · subst heq
        show w = 1 / ((E.countP (touchB a) : ℝ) * (E.countP (touchB (i :: a)) : ℝ))
        rw [hw1, hroot, hcnt_child]
        push_cast
        ring
      · exact htail e (List.mem_append.mpr (Or.inl hL'))
    · rcases List.mem_append.mp hR with hSub | hTail
      · exact hchild e hSub
      · exact htail e (List.mem_append.mpr (Or.inr hTail))

end

/-- **Every edge of a good realization carries the reciprocal degree product** (counts in
    the full realized list).  Instantiate with `litHub_good` for the competitor trees. -/
theorem realize_weights (t : RTree) (d : ℕ) (hg : GoodTree d t) (hd : childCount t = d) :
    ∀ e ∈ realize t, e.2.2
      = 1 / (((realize t).countP (touchB e.1) : ℝ)
          * ((realize t).countP (touchB e.2.1) : ℝ)) := by
  have hroot : (realize t).countP (touchB []) = d := by
    rw [realize, rEdges_countRoot [] t, hd]
  intro e he
  exact emission_weights (realize t) [] t d hg hroot
    (fun x k _ => by rw [realize]) e (by rwa [realize] at he)

end Step3
end R3Cert
