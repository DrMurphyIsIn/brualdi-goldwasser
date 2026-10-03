/-
  NEGATIVE CONTROL (must be rejected): every tree on n ≥ 4 vertices maximizes the ratio. This is false already
  for n = 4, where the star K_{1,3} is not a maximizer (the negation is proved in
  `BGUnique.Controls.not_negEveryTree`).
-/
import Mathlib

namespace BGUniqueComparator

theorem unique (n : ℕ) (h4 : 4 ≤ n) (h21 : n ≠ 21)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (hV : Fintype.card V = n) :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
      H.IsTree → Fintype.card X = n → (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) := by
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
