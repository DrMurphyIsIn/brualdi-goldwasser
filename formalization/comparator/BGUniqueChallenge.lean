/-
  The Comparator CHALLENGE for uniqueness: the maximizers of the Brualdi-Goldwasser ratio, stated in Mathlib's
  vocabulary only (it imports nothing but Mathlib). For trees on n ≥ 4 vertices, n ≠ 21, any two trees that
  maximize per (lapMatrix) / ∏ deg among all trees on n vertices are isomorphic; for n = 21 there are two
  maximizing trees that are not isomorphic, and every maximizing tree is isomorphic to one of them.
  The `sorry`s below are the challenge's by design; the proofs are in `BGUniqueSolution.lean`.
-/
import Mathlib

namespace BGUniqueComparator

theorem unique (n : ℕ) (h4 : 4 ≤ n) (h21 : n ≠ 21)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {W : Type} [Fintype W] [DecidableEq W] (G' : SimpleGraph W) [DecidableRel G'.Adj]
    (hG : G.IsTree) (hV : Fintype.card V = n) (hG' : G'.IsTree) (hW : Fintype.card W = n)
    (hmax : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
      H.IsTree → Fintype.card X = n →
        (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)))
    (hmax' : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
      H.IsTree → Fintype.card X = n →
        (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G'.lapMatrix ℝ).permanent / (∏ v, (G'.degree v : ℝ))) :
    Nonempty (G ≃g G') := by
  sorry

theorem two_at_21 :
    ∃ (G₁ G₂ : SimpleGraph (Fin 21)) (_ : DecidableRel G₁.Adj) (_ : DecidableRel G₂.Adj),
      G₁.IsTree ∧ G₂.IsTree ∧ IsEmpty (G₁ ≃g G₂) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ))) ∧
      (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ)) = (G₂.lapMatrix ℝ).permanent / (∏ v, (G₂.degree v : ℝ)) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) = (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ)) →
          Nonempty (H ≃g G₁) ∨ Nonempty (H ≃g G₂)) := by
  sorry

end BGUniqueComparator
