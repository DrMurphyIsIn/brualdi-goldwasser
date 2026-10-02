/-
LeanCherry.PBMain -- part (B) of the uniform ceiling on all of 0 < lam < 1 + sqrt 5, with NO external input:
the witness W2 on (0, 3/20] (where F = f_3, LeanCherry.PBGap) and the witness W* on [3/20, 1 + sqrt 5).
Every scalar condition is a theorem of LeanCherry.PBCerts / PBCertsFix; everything else is by hand.
-/
import LeanCherry.PBW2
import LeanCherry.PBGap

open Real

namespace LeanCherry

noncomputable section

open Classical Br

/-- a witness for (lam, f*) and a best arm, for every 0 < lam < 1 + sqrt 5 -/
theorem partB_witness_all (l : ℝ) (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧
      ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  have H : PB l := ⟨hl0, hlc⟩
  refine ⟨?_, fstar_attained hl0 H.Dinf_pos⟩
  rcases le_total l (3 / 20) with h | h
  · have W : W2Facts l := ⟨H, h, fstar_eq_f3 l hl0 h⟩
    exact ⟨_, _, _, W.witness⟩
  · exact ⟨_, _, _, H.wstar_witness h⟩

/-- the former external input on [0.1, lam_c), now proved -/
theorem partB_witnessInput : PartB_WitnessInput :=
  fun l h1 h2 => partB_witness_all l (by linarith) h2

/-- the former external input on (0, 0.1] (previously the typed induction), now proved -/
theorem partB_smallInput : PartB_SmallInput := by
  intro l hl0 hl1
  obtain ⟨⟨A, I, h, W⟩, harm⟩ := partB_witness_all l hl0 (by have := sqrt5_bounds.1; linarith)
  refine ⟨fun b => ?_, harm⟩
  have hc := W.mt_main_a.2.2.2 b
  have := Real.log_le_log (Tl_pos hl0.le b) hc
  rw [Real.log_exp] at this; linarith

/-- **Part (B) on all of 0 < lam < 1 + sqrt 5**, with no hypotheses: the ceiling log T_b <= |b| f*, rho = e^{f*},
    and the M_n sandwich with a best arm b* = A_j. -/
theorem part_B_full {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) :=
  part_B_of_inputs partB_witnessInput partB_smallInput hl0 hlc

end

end LeanCherry
