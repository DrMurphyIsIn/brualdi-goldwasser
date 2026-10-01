/-
LeanCherry.PartB -- the ceiling for 0 < lambda < 1 + sqrt 5 (part (B)), REDUCED to explicitly stated numerical inputs.

  arm A_j = a vertex carrying j cherries (2j+1 vertices);  f_j(l) = log T(A_j)/(2j+1);  f*(l) = sup_{j>=1} f_j(l).
  PartB_WitnessInput  : for every l in [0.1, 1+sqrt5), there EXISTS a witness for (l, f*(l)) and some arm A_j with
                        f_j = f* (tightness at a best arm).  Supplied by the computer-assisted witness covers on [0.1, 3.22] and the
                        window argument on [3.22, lam_c).  NOT kernel-checked; this is an abstract ∃-statement, the witness formulas
                        are not made explicit.
  PartB_SmallInput    : for every l in (0, 0.1], the ceiling log T_b <= |b| f*(l) for all b and some best arm attains f*.
                        Supplied by the computer-assisted typed induction, which is NOT a witness; its conclusion is taken as the input.
  part_B_of_inputs    : inputs => for every 0 < l < 1+sqrt5: the ceiling, rho = e^{f*}, and the M_n sandwich with b* = a best arm.
The equality clause of (B) ("equality exactly when b is a best arm") is NOT derived here.
-/
import LeanCherry.WitnessExamples

open Finset

namespace LeanCherry

noncomputable section

open Br

/-- the arm A_j: a vertex carrying j cherries -/
def armB (j : ℕ) : Br := .node (List.replicate j cherry)

lemma armB_size (j : ℕ) : size (armB j) = 2 * j + 1 := by
  simp only [armB, size, sizeL_replicate]; simp [cherry, size, sizeL]; ring

/-- the arm rate f_j -/
def fArm (l : ℝ) (j : ℕ) : ℝ := Real.log (Tl l (armB j)) / (2 * j + 1)

/-- the best arm rate f* -/
def fstar (l : ℝ) : ℝ := sSup {x | ∃ j : ℕ, 1 ≤ j ∧ x = fArm l j}

lemma gB_arm_eq_zero {l : ℝ} {j : ℕ} (h : fArm l j = fstar l) : gB l (fstar l) (armB j) = 0 := by
  unfold gB; rw [armB_size, ← h, fArm]; push_cast; field_simp; ring

/-- numerical input 1 (computer-verified outside Lean, NOT here): a tight witness on [0.1, 1 + sqrt 5) -/
def PartB_WitnessInput : Prop :=
  ∀ l : ℝ, (1 / 10 : ℝ) ≤ l → l < 1 + √5 →
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

/-- numerical input 2 (computer-verified outside Lean by the typed induction, NOT here): the ceiling on (0, 0.1] -/
def PartB_SmallInput : Prop :=
  ∀ l : ℝ, 0 < l → l ≤ 1 / 10 →
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

/-- part (B) from the two numerical inputs (inequality part and its consequences) -/
theorem part_B_of_inputs (hW : PartB_WitnessInput) (hS : PartB_SmallInput) {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  -- the ceiling in both regimes
  have hceil : (∀ b : Br, Tl l b ≤ Real.exp (fstar l * size b)) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
    rcases le_or_gt (1 / 10 : ℝ) l with h | h
    · obtain ⟨⟨A, I, hh, W⟩, harm⟩ := hW l h hlc
      exact ⟨W.mt_main_a.2.2.2, harm⟩
    · obtain ⟨hc, harm⟩ := hS l hl0 h.le
      refine ⟨fun b => ?_, harm⟩
      calc Tl l b = Real.exp (Real.log (Tl l b)) := (Real.exp_log (Tl_pos hl0.le b)).symm
        _ ≤ Real.exp (fstar l * size b) := Real.exp_le_exp.mpr (by linarith [hc b])
  obtain ⟨hc, j, hj, hfj⟩ := hceil
  obtain ⟨hrho, hMn⟩ := tight_consequences hl0.le hc (gB_arm_eq_zero hfj)
  refine ⟨fun b => ?_, hrho, j, hj, hMn⟩
  have := Real.log_le_log (Tl_pos hl0.le b) (hc b)
  rw [Real.log_exp] at this; linarith

end

end LeanCherry
