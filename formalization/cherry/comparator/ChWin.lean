/- Comparator challenge: part (B) on the window and the reduction below it.
   window_witness: for 3.22 <= l < 1+sqrt5 there is a witness for (l, f*(l)) and a best arm.
   window_ceiling: the branch bound log T_b <= |b| f* of part (B) on the window.
   part_B_of_inputs_low: the branch bound, rho = e^{f*} and the two-sided bound on M_n with a best arm, for
   0 < l < 1+sqrt5, from the witness input on [0.1, 3.22) only and the small-lambda input. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

def PartB_WitnessInputLow : Prop :=
  ∀ l : ℝ, (1 / 10 : ℝ) ≤ l → l < 3.22 →
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

theorem window_witness (l : ℝ) (h1 : 3.22 ≤ l) (h2 : l < 1 + √5) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  sorry

theorem window_ceiling (l : ℝ) (h1 : 3.22 ≤ l) (h2 : l < 1 + √5) (b : Br) :
    Real.log (Tl l b) ≤ size b * fstar l := by
  sorry

theorem part_B_of_inputs_low (hW : PartB_WitnessInputLow) (hS : PartB_SmallInput) {l : ℝ} (hl0 : 0 < l)
    (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  sorry

end

end LeanCherry
