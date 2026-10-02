/- Negative control: `ChPartBFull.lean` with f* = f_3 claimed on (0, 1/2] instead of (0, 3/20]. The claim is false
   (the best arm switches from A_3 to A_4 between l = 0.43 and 0.45; at l = 1/2, f_4 - f_3 is about 6.7e-5), and Comparator must reject it with a statement mismatch. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

theorem fstar_eq_f3 (l : ℝ) (hl0 : 0 < l) (hl : l ≤ 1 / 2) : fstar l = fArm l 3 := by
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
