/- Comparator challenge: part (B) on [2, 1+sqrt5) and the reduction below 2.
   window_witness_ext2: for 2 <= l < 2.35 there is a witness for (l, f*(l)) and a best arm.
   window_witness_full2: the same for 2 <= l < 1+sqrt5.
   PartB_WitnessInputLower2: the witness input of part (B), restricted to [1/10, 2).
   part_B_of_inputs_lower2: the branch bound, rho = e^{f*} and the two-sided bound on M_n with a best arm, for
   0 < l < 1+sqrt5, from the witness input on [0.1, 2) only and the small-lambda input. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

def PartB_WitnessInputLower2 : Prop :=
  ∀ l : ℝ, (1 / 10 : ℝ) ≤ l → l < 2 →
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

theorem window_witness_ext2 (l : ℝ) (h1 : 2 ≤ l) (h2 : l < 2.35) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  sorry

theorem window_witness_full2 (l : ℝ) (h1 : 2 ≤ l) (h2 : l < 1 + √5) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  sorry

theorem part_B_of_inputs_lower2 (hW : PartB_WitnessInputLower2) (hS : PartB_SmallInput) {l : ℝ} (hl0 : 0 < l)
    (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  sorry

end

end LeanCherry
