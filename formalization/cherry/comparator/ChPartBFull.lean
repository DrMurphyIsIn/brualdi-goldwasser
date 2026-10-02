/- Comparator challenge: part (B) on all of 0 < l < 1+sqrt5, with no external input.
   fstar_eq_f3: f* = f_3 (the arm with three cherries is a best arm) for 0 < l <= 3/20.
   partB_witness_all: for every 0 < l < 1+sqrt5 there is a witness for (l, f*(l)) and a best arm.
   partB_witnessInput, partB_smallInput: the two former inputs of part (B), as restated in ChPartB.lean.
   part_B_full: the branch bound, rho = e^{f*} and the two-sided bound on M_n with a best arm, for every
   0 < l < 1+sqrt5, with no hypotheses. The equality clause of part (B) is not part of this challenge. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

theorem fstar_eq_f3 (l : ℝ) (hl0 : 0 < l) (hl : l ≤ 3 / 20) : fstar l = fArm l 3 := by
  sorry

theorem partB_witness_all (l : ℝ) (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧
      ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  sorry

theorem partB_witnessInput : PartB_WitnessInput := by
  sorry

theorem partB_smallInput : PartB_SmallInput := by
  sorry

theorem part_B_full {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  sorry

end

end LeanCherry
