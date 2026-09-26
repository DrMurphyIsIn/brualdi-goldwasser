/-
  E1 and E3 from E2.

  * `E1 ⟸ E2` UNIFORMLY: going from `Sg = m·T0` down to `Sg = 0` the linear part drops by
    `m·T0/((N+1)ρ)` while the fold gains at most `(11/50)·m·T0/(K(K+m·T0))` (the positive part is
    1-Lipschitz); since `K ≥ N+1` and `K + d ≥ 2 > (11/50)·rhoB`, the drop dominates.
  * `E3 ⟸ E2` for `a+nl+m ≥ 3`: going up to `Sg = m/2` the fold only shrinks and the linear part
    grows with slope `1/((N+1)ρ) ≤ 11/50` (as `(N+1)·rhoB ≥ 4·(1229/1000) > 50/11`), below the
    right side's slope `11/50`.  The remaining cases `(0,0,1), (1,0,1), (0,1,1), (0,0,2)` close by
    interval-corner rationals.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialM1Piece
import R3Cert.PotentialEBase
import R3Cert.PotentialE2
import R3Cert.PotentialE2Small

namespace R3Cert

open Real

/-- The positive part is 1-Lipschitz from above: `v ≤ u → u₊ − v₊ ≤ u − v`. -/
theorem posPart_sub_le {u v : ℝ} (h : v ≤ u) : max 0 u - max 0 v ≤ u - v := by
  rcases le_total u 0 with hu | hu <;> rcases le_total v 0 with hv | hv
  · rw [max_eq_left hu, max_eq_left hv]; linarith
  · rw [max_eq_left hu, max_eq_right hv]; linarith
  · rw [max_eq_right hu, max_eq_left hv]; linarith
  · rw [max_eq_right hu, max_eq_right hv]

/-- **`E1Bound` follows from `E2Bound`.** -/
theorem e1Bound_of_e2 (hE2 : E2Bound) : E1Bound := by
  intro a nl m hm
  have h2 := hE2 a nl m hm
  rw [starLHS_shape] at h2 ⊢
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr2 := rhoB_lt_123
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hnl0 : (0 : ℝ) ≤ (nl : ℝ) := Nat.cast_nonneg nl
  set Nn : ℝ := (a : ℝ) + nl + m + 1 with hNn
  set Kf : ℝ := Nn + ((a : ℝ) / 3 + nl) with hKf
  set d : ℝ := (m : ℝ) * T0 with hd
  have hNn2 : (2 : ℝ) ≤ Nn := by rw [hNn]; linarith
  have hNnpos : (0 : ℝ) < Nn := by linarith
  have hK2 : (2 : ℝ) ≤ Kf := by rw [hKf]; linarith
  have hKpos : (0 : ℝ) < Kf := by linarith
  have hNK : Nn ≤ Kf := by rw [hKf]; linarith
  have hd0 : (0 : ℝ) < d := by
    rw [hd]; exact mul_pos (by linarith) (by linarith)
  have hKd : (0 : ℝ) < Kf + d := by linarith
  have hK0 : (0 : ℝ) < Kf + 0 := by linarith
  -- fold difference is at most the inverse difference (1-Lipschitz)
  have hinvle : 1 / (Kf + d) ≤ 1 / (Kf + 0) := by
    apply one_div_le_one_div_of_le hK0; linarith
  have hF1 : max 0 (1 / (Kf + 0) - T0) - max 0 (1 / (Kf + d) - T0)
      ≤ (1 / (Kf + 0) - T0) - (1 / (Kf + d) - T0) :=
    posPart_sub_le (u := 1 / (Kf + 0) - T0) (v := 1 / (Kf + d) - T0) (by linarith [hinvle])
  -- the inverse difference in closed form
  have hF2 : 1 / (Kf + 0) - 1 / (Kf + d) = d / ((Kf + 0) * (Kf + d)) := by
    rw [div_sub_div _ _ (ne_of_gt hK0) (ne_of_gt hKd)]
    congr 1
    ring
  -- domination: `(11/50)·d/((Kf+0)(Kf+d)) ≤ (1/(Nn·rhoB))·d`
  have hslack : (0 : ℝ) ≤ (Kf + d) - (11 / 50) * rhoB := by nlinarith [hr2, hK2, hd0]
  have hint1 : (0 : ℝ) ≤ d * Nn * ((Kf + d) - (11 / 50) * rhoB) :=
    mul_nonneg (mul_nonneg hd0.le hNnpos.le) hslack
  have hint2 : (0 : ℝ) ≤ d * (Kf - Nn) * (Kf + d) :=
    mul_nonneg (mul_nonneg hd0.le (by linarith)) hKd.le
  have hF3 : (11 / 50) * (d / ((Kf + 0) * (Kf + d))) ≤ 1 / (Nn * rhoB) * d := by
    have hX : (0 : ℝ) < (Kf + 0) * (Kf + d) := mul_pos hK0 hKd
    have hY : (0 : ℝ) < Nn * rhoB := mul_pos hNnpos rhoB_pos
    rw [show (11 / 50) * (d / ((Kf + 0) * (Kf + d))) = (11 * d / 50) / ((Kf + 0) * (Kf + d))
          from by ring,
        show 1 / (Nn * rhoB) * d = d / (Nn * rhoB) from by ring,
        div_le_div_iff₀ hX hY]
    nlinarith [hint1, hint2]
  linarith [h2, hF1, hF2.le, hF2.ge, hF3]

/-- **Exact `E3` case `(0,0,1)`.** -/
theorem e3_case_001 :
    (1 / 4 - T0) / rhoB + (11 / 50) * max 0 (2 / 5 - T0) ≤ (11 / 50) * (1 / 2 - T0) := by
  have hT1 := T0_gt_229; have hr1 := rhoB_gt_1229
  rw [fold_active (by norm_num : (23 / 100 : ℝ) ≤ 2 / 5)]
  have h1 : (1 / 4 - T0) / rhoB ≤ 11 / 500 := by
    rw [div_le_iff₀ rhoB_pos]
    nlinarith [hT1, hr1]
  linarith [h1]

/-- **Exact `E3` case `(1,0,1)`.** -/
theorem e3_case_101 :
    (5 / 18 - T0) / rhoB + (11 / 50) * max 0 (6 / 23 - T0) ≤ (11 / 50) * (1 / 2 - T0) := by
  have hT1 := T0_gt_229; have hr1 := rhoB_gt_1229
  rw [fold_active (by norm_num : (23 / 100 : ℝ) ≤ 6 / 23)]
  have h1 : (5 / 18 - T0) / rhoB ≤ 121 / 2300 := by
    rw [div_le_iff₀ rhoB_pos]
    nlinarith [hT1, hr1]
  linarith [h1]

/-- **Exact `E3` case `(0,1,1)`** (fold is zero: `2/9 < 229/1000`). -/
theorem e3_case_011 :
    (1 / 2 - T0) / rhoB + (11 / 50) * max 0 (2 / 9 - T0)
      ≤ 229 / 1229 + (11 / 50) * (1 / 2 - T0) := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229; have hr2 := rhoB_lt_123
  rw [fold_zero (by norm_num : (2 / 9 : ℝ) ≤ 229 / 1000), mul_zero, add_zero]
  rw [div_le_iff₀ rhoB_pos]
  nlinarith [hT1, hT2, hr1, hr2,
    mul_nonneg (sub_pos.2 hr2).le (by linarith [hT1] : (0 : ℝ) ≤ T0 - 229 / 1000)]

/-- **Exact `E3` case `(0,0,2)`.** -/
theorem e3_case_002 :
    (1 / 3 - T0) / rhoB + (11 / 50) * max 0 (1 / 4 - T0) ≤ (11 / 50) * (1 - 2 * T0) := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229
  rw [fold_active (by norm_num : (23 / 100 : ℝ) ≤ 1 / 4)]
  have h34 : (0 : ℝ) ≤ 3 / 4 - T0 := by linarith
  have h1 : (1 / 3 - T0) / rhoB ≤ (11 / 50) * (3 / 4 - T0) := by
    rw [div_le_iff₀ rhoB_pos]
    nlinarith [hT1, hT2, hr1, mul_nonneg (sub_nonneg.2 hr1.le) h34]
  linarith [h1]

/-- **`E3Bound` follows from `E2Bound`.** -/
theorem e3Bound_of_e2 (hE2 : E2Bound) : E3Bound := by
  intro a nl m hm
  by_cases h3 : 3 ≤ a + nl + m
  · -- slope argument
    have h2 := hE2 a nl m hm
    rw [starLHS_shape] at h2 ⊢
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h3R : (3 : ℝ) ≤ (a : ℝ) + nl + m := by exact_mod_cast h3
    have hT1 := T0_gt_229; have hT2 := T0_lt_23
    have hr1 := rhoB_gt_1229
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hnl0 : (0 : ℝ) ≤ (nl : ℝ) := Nat.cast_nonneg nl
    set Nn : ℝ := (a : ℝ) + nl + m + 1 with hNn
    set Kf : ℝ := Nn + ((a : ℝ) / 3 + nl) with hKf
    have hNn4 : (4 : ℝ) ≤ Nn := by rw [hNn]; linarith
    have hNnpos : (0 : ℝ) < Nn := by linarith
    have hKpos : (0 : ℝ) < Kf := by rw [hKf]; linarith
    have hdle : (m : ℝ) * T0 ≤ (m : ℝ) / 2 := by
      have := mul_le_mul_of_nonneg_left (le_of_lt (show T0 < 1 / 2 by linarith))
        (by linarith : (0 : ℝ) ≤ (m : ℝ))
      linarith [this]
    -- fold shrinks going up
    have hfold : max 0 (1 / (Kf + (m : ℝ) / 2) - T0) ≤ max 0 (1 / (Kf + (m : ℝ) * T0) - T0) := by
      apply max_le_max le_rfl
      have h1 : 1 / (Kf + (m : ℝ) / 2) ≤ 1 / (Kf + (m : ℝ) * T0) := by
        apply one_div_le_one_div_of_le
        · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ)) (by linarith : (0 : ℝ) ≤ T0)]
        · linarith [hdle]
      linarith [h1]
    -- the linear slope is below 11/50
    have hslope : 1 / (Nn * rhoB) ≤ 11 / 50 := by
      rw [div_le_iff₀ (mul_pos hNnpos rhoB_pos)]
      nlinarith [hNn4, hr1, mul_nonneg (by linarith : (0 : ℝ) ≤ Nn - 4)
        (by linarith : (0 : ℝ) ≤ rhoB - 1229 / 1000)]
    have hgap : (0 : ℝ) ≤ (m : ℝ) / 2 - (m : ℝ) * T0 := by linarith [hdle]
    have hstep := mul_le_mul_of_nonneg_right hslope hgap
    linarith [h2, hfold, hstep]
  · -- the four small cases
    have hcase : (a = 0 ∧ nl = 0 ∧ m = 1) ∨ (a = 1 ∧ nl = 0 ∧ m = 1)
        ∨ (a = 0 ∧ nl = 1 ∧ m = 1) ∨ (a = 0 ∧ nl = 0 ∧ m = 2) := by omega
    rcases hcase with ⟨ha, hn, hmm⟩ | ⟨ha, hn, hmm⟩ | ⟨ha, hn, hmm⟩ | ⟨ha, hn, hmm⟩ <;>
      subst ha <;> subst hn <;> subst hmm <;> unfold starLHS
    · rw [show (((0 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) / 2)
            / (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1) = (1 / 4 : ℝ)
          from by push_cast; norm_num,
        show ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1
              + (((0 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) / 2) = (5 / 2 : ℝ)
          from by push_cast; norm_num,
        show (1 : ℝ) / (5 / 2) = 2 / 5 from by norm_num,
        show ((0 : ℕ) : ℝ) * (-omegaVal) + ((0 : ℕ) : ℝ) * Lval
              + 11 / 50 * (((1 : ℕ) : ℝ) / 2 - ((1 : ℕ) : ℝ) * T0) = 11 / 50 * (1 / 2 - T0)
          from by push_cast; ring]
      exact e3_case_001
    · rw [show (((1 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) / 2)
            / (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1) = (5 / 18 : ℝ)
          from by push_cast; norm_num,
        show ((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1
              + (((1 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) / 2) = (23 / 6 : ℝ)
          from by push_cast; norm_num,
        show (1 : ℝ) / (23 / 6) = 6 / 23 from by norm_num,
        show ((1 : ℕ) : ℝ) * (-omegaVal) + ((0 : ℕ) : ℝ) * Lval
              + 11 / 50 * (((1 : ℕ) : ℝ) / 2 - ((1 : ℕ) : ℝ) * T0)
            = -omegaVal + 11 / 50 * (1 / 2 - T0) from by push_cast; ring]
      have hb : (0 : ℝ) ≤ -omegaVal := le_trans (by norm_num) neg_omega_ge_const
      linarith [e3_case_101]
    · rw [show (((0 : ℕ) : ℝ) / 3 + ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) / 2)
            / (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1) = (1 / 2 : ℝ)
          from by push_cast; norm_num,
        show ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1
              + (((0 : ℕ) : ℝ) / 3 + ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) / 2) = (9 / 2 : ℝ)
          from by push_cast; norm_num,
        show (1 : ℝ) / (9 / 2) = 2 / 9 from by norm_num,
        show ((0 : ℕ) : ℝ) * (-omegaVal) + ((1 : ℕ) : ℝ) * Lval
              + 11 / 50 * (((1 : ℕ) : ℝ) / 2 - ((1 : ℕ) : ℝ) * T0)
            = Lval + 11 / 50 * (1 / 2 - T0) from by push_cast; ring]
      linarith [e3_case_011, Lval_ge_const]
    · rw [show (((0 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) / 2)
            / (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + 1) = (1 / 3 : ℝ)
          from by push_cast; norm_num,
        show ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + 1
              + (((0 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) / 2) = (4 : ℝ)
          from by push_cast; norm_num,
        show (1 : ℝ) / (4 : ℝ) = 1 / 4 from by norm_num,
        show ((0 : ℕ) : ℝ) * (-omegaVal) + ((0 : ℕ) : ℝ) * Lval
              + 11 / 50 * (((2 : ℕ) : ℝ) / 2 - ((2 : ℕ) : ℝ) * T0) = 11 / 50 * (1 - 2 * T0)
          from by push_cast; ring]
      exact e3_case_002

end R3Cert
