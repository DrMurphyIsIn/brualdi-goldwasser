/- Negative control: `ChPartBEq.lean` with equality claimed exactly at the cherry. The claim is false: at
   l = 1, |b| f* - log T(b) is about 0.0077 for the cherry, and the best arm A_5, which is not the cherry, attains
   the bound. Comparator must reject it with a statement mismatch. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

theorem part_B_equality {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) (b : Br) :
    Real.log (Tl l b) = size b * fstar l ↔ b = cherry := by
  sorry

theorem part_B_full_eq {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧
    (∀ b : Br, Real.log (Tl l b) = size b * fstar l ↔ ∃ j : ℕ, 1 ≤ j ∧ b = armB j ∧ fArm l j = fstar l) ∧
    rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  sorry

end

end LeanCherry
