/-
  NEGATIVE CONTROL (must be rejected): a single isomorphism class of maximizers at n = 21. This is false: the
  two maximizing trees at n = 21 are not isomorphic (`R3Cert.BGUnique.bg_maximizers_21_mathlib`; the negation is
  proved in `BGUnique.Controls.not_negOneClass21`).
-/
import Mathlib

namespace BGUniqueComparator

theorem two_at_21 :
    ∃ (G₁ : SimpleGraph (Fin 21)) (_ : DecidableRel G₁.Adj), G₁.IsTree ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ))) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) = (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ)) → Nonempty (H ≃g G₁)) := by
  sorry

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

end BGUniqueComparator
