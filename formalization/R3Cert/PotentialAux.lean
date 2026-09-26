/-
  Auxiliary facts for the crux `ValidPotentialPlain Pval`: rhoB interval bounds, `Pval = 0` below `T0`,
  and the near-star (all-arm-children) super-solution for `k >= 3` (the easy branch, `Pval = 0` +
  `gVal_nonpos`).  The `k = 0,1,2` near-star cases and the general case follow in later increments.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.ExactCruxes
import R3Cert.Sweep
import R3Cert.JTail
import R3Cert.Potential

namespace R3Cert

open Real

/-- `rhoB < 4/3` (`rhoB^11 = 621/64 < (4/3)^11`), hence `T0 = rhoB - 1 < 1/3`. -/
theorem rhoB_lt_four_thirds : rhoB < 4 / 3 := by
  have h : rhoB ^ 11 < (4 / 3 : ℝ) ^ 11 := by rw [rhoB_pow11]; norm_num
  exact lt_of_pow_lt_pow_left₀ 11 (by norm_num) h

/-- `6/5 < rhoB` (`(6/5)^11 < 621/64`), hence `T0 > 1/5`. -/
theorem rhoB_gt_six_fifths : (6 / 5 : ℝ) < rhoB := by
  have h : (6 / 5 : ℝ) ^ 11 < rhoB ^ 11 := by rw [rhoB_pow11]; norm_num
  exact lt_of_pow_lt_pow_left₀ 11 rhoB_pos.le h

theorem T0_lt_third : T0 < 1 / 3 := by unfold T0; linarith [rhoB_lt_four_thirds]

theorem T0_gt_fifth : (1 / 5 : ℝ) < T0 := by unfold T0; linarith [rhoB_gt_six_fifths]

/-- **`Pval y = 0` for `y <= T0`** (then `y ≠ 1/3` and `y ≠ 1`, and `max 0 (y - T0) = 0`). -/
theorem Pval_zero_of_le_T0 {y : ℝ} (h : y ≤ T0) : Pval y = 0 := by
  have h3 : y ≠ 1 / 3 := by
    intro he; rw [he] at h; linarith [T0_lt_third]
  have h1 : y ≠ 1 := by
    intro he; rw [he] at h; linarith [T0_lt_third]
  rw [Pval_struct y h3 h1, max_eq_left (by linarith : y - T0 ≤ 0)]; ring

/-- **Near-star super-solution, `k >= 3`:** `gVal k + Pval (3/(4k+3)) <= 0`.
    (`3/(4k+3) <= 1/5 < T0`, so `Pval = 0`, and `gVal k <= 0`.) -/
theorem gVal_add_Pval_ge3 {k : ℕ} (hk : 3 ≤ k) :
    gVal k + Pval (3 / (4 * (k : ℝ) + 3)) ≤ 0 := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < 4 * (k : ℝ) + 3 := by linarith
  have hle : 3 / (4 * (k : ℝ) + 3) ≤ T0 := by
    have h5 : 3 / (4 * (k : ℝ) + 3) ≤ 1 / 5 := by
      rw [div_le_iff₀ hden]; linarith
    linarith [T0_gt_fifth]
  rw [Pval_zero_of_le_T0 hle, add_zero]
  exact gVal_nonpos k

end R3Cert
