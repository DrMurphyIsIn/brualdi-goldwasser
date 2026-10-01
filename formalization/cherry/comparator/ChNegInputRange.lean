/- Negative control: `ChWin2.lean` with the input PartB_WitnessInputLower2 stated on [1/10, 2.1) instead of
   [1/10, 2). Comparator must reject it with a definition mismatch on PartB_WitnessInputLower2. -/
import ChPartB

namespace LeanCherry

noncomputable section

open Br

def PartB_WitnessInputLower2 : Prop :=
  ∀ l : ℝ, (1 / 10 : ℝ) ≤ l → l < 2.1 →
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
