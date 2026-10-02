/- Negative control: `ChPartBEq.lean` with the M_n part of part_B_full_eq stated WITHOUT f_j = f* (the
   weaker, unstrengthened form). The statement is true but is not the one proved, so Comparator must reject it with
   a statement mismatch: this checks that the strengthened statement is the one replayed. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

theorem part_B_equality {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) (b : Br) :
    Real.log (Tl l b) = size b * fstar l ↔ ∃ j : ℕ, 1 ≤ j ∧ b = armB j ∧ fArm l j = fstar l := by
  sorry

theorem part_B_full_eq {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧
    (∀ b : Br, Real.log (Tl l b) = size b * fstar l ↔ ∃ j : ℕ, 1 ≤ j ∧ b = armB j ∧ fArm l j = fstar l) ∧
    rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  sorry

end

end LeanCherry
