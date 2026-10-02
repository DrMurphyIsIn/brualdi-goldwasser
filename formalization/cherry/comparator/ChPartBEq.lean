/- Comparator challenge: the equality clause of part (B), for every 0 < l < 1+sqrt5.
   part_B_equality: log T(b) = |b| f*(l) exactly when b is an arm A_j (j >= 1) with f_j(l) = f*(l), i.e. a best arm.
   part_B_full_eq: the branch bound, the equality clause, rho = e^{f*}, and the two-sided bound on M_n with a best
   arm A_j (f_j = f*), for every 0 < l < 1+sqrt5, with no hypotheses. -/
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
      ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  sorry

end

end LeanCherry
