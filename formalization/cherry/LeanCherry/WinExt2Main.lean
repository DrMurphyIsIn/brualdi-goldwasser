/-
LeanCherry.WinExt2Main -- the window extended to [2, 2.35], part 4: the window witness on [2, lam_c), and Part (B) with the external
witness input reduced to [0.1, 2).
-/
import LeanCherry.WinExt2Boxes
import LeanCherry.WinExtMain

open Real

namespace LeanCherry

noncomputable section

open Classical Br

/-- the theta = 1 window witness below 2.35: a tight witness and a best arm for every l in [2, 2.35) -/
theorem window_witness_ext2 (l : ℝ) (h1 : 2 ≤ l) (h2 : l < 2.35) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l :=
  (WinExt2.wfacts_ext2 l h1 h2.le).witness_and_arm

/-- the window witness on all of [2, lam_c) -/
theorem window_witness_full2 (l : ℝ) (h1 : 2 ≤ l) (h2 : l < 1 + √5) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  rcases lt_or_ge l 2.35 with hl | hl
  · exact window_witness_ext2 l h1 hl
  · exact window_witness_full l hl h2

/-- the external numerical input of Part (B), with [2, lam_c) removed (now proved) -/
def PartB_WitnessInputLower2 : Prop :=
  ∀ l : ℝ, (1 / 10 : ℝ) ≤ l → l < 2 →
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

theorem partB_witnessInput_of_lower2 (h : PartB_WitnessInputLower2) : PartB_WitnessInput := by
  intro l h1 h2
  rcases lt_or_ge l 2 with hl | hl
  · exact h l h1 hl
  · exact window_witness_full2 l hl h2

/-- Part (B) from the reduced inputs: witnesses on [0.1, 2) and the small-lam input -/
theorem part_B_of_inputs_lower2 (hW : PartB_WitnessInputLower2) (hS : PartB_SmallInput) {l : ℝ} (hl0 : 0 < l)
    (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) :=
  part_B_of_inputs (partB_witnessInput_of_lower2 hW) hS hl0 hlc

end

end LeanCherry
