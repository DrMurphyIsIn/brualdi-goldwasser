/-
  Tight `rhoB` interval and the log-form bounds for `gVal 1`, `gVal 2`, used in the near-star `k = 1, 2`
  super-solution cases (via `log x <= x - 1`).

    gVal 1 = log(7/4)  - 3 log rhoB,   gVal 2 = log(11/4) - 5 log rhoB.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.ExactCruxes
import R3Cert.Sweep
import R3Cert.LemmaA

namespace R3Cert

open Real

/-- `1229/1000 < rhoB` (`(1229/1000)^11 < 621/64`). -/
theorem rhoB_gt_1229 : (1229 / 1000 : ℝ) < rhoB := by
  have h : (1229 / 1000 : ℝ) ^ 11 < rhoB ^ 11 := by rw [rhoB_pow11]; norm_num
  exact lt_of_pow_lt_pow_left₀ 11 rhoB_pos.le h

/-- `rhoB < 123/100` (`621/64 < (123/100)^11`). -/
theorem rhoB_lt_123 : rhoB < 123 / 100 := by
  have h : rhoB ^ 11 < (123 / 100 : ℝ) ^ 11 := by rw [rhoB_pow11]; norm_num
  exact lt_of_pow_lt_pow_left₀ 11 (by norm_num) h

/-- `gVal 1 = log(7/4) - 3 log rhoB`. -/
theorem gVal_one_eq : gVal 1 = Real.log (7 / 4) - 3 * Real.log rhoB := by
  have hL : Lval = Real.log rhoB := logRhoB_local.symm
  have h74 : Real.log (7 / 4) = Real.log (3 / 2) + Real.log 7 - Real.log 6 := by
    rw [show (7 : ℝ) / 4 = 3 / 2 * 7 / 6 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  unfold gVal
  rw [hL]
  have e7 : (4 * ((1 : ℕ) : ℝ) + 3) = 7 := by norm_num
  have e6 : (3 * (((1 : ℕ) : ℝ) + 1)) = 6 := by norm_num
  rw [e7, e6, h74]
  push_cast; ring

/-- `gVal 2 = log(11/4) - 5 log rhoB`. -/
theorem gVal_two_eq : gVal 2 = Real.log (11 / 4) - 5 * Real.log rhoB := by
  have hL : Lval = Real.log rhoB := logRhoB_local.symm
  have h114 : Real.log (11 / 4) = 2 * Real.log (3 / 2) + Real.log 11 - Real.log 9 := by
    rw [show (2 : ℝ) * Real.log (3 / 2) = Real.log ((3 / 2) ^ 2) by rw [Real.log_pow]; norm_num,
        show ((3 / 2 : ℝ)) ^ 2 = 9 / 4 by norm_num,
        show (11 : ℝ) / 4 = 9 / 4 * 11 / 9 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  unfold gVal
  rw [hL]
  have e11 : (4 * ((2 : ℕ) : ℝ) + 3) = 11 := by norm_num
  have e9 : (3 * (((2 : ℕ) : ℝ) + 1)) = 9 := by norm_num
  rw [e11, e9, h114]
  push_cast; ring

/-- `gVal 1 <= (7/4)/rhoB^3 - 1`  (from `log x <= x - 1`). -/
theorem gVal_one_le : gVal 1 ≤ (7 / 4) / rhoB ^ 3 - 1 := by
  have hr3 : (0 : ℝ) < rhoB ^ 3 := pow_pos rhoB_pos 3
  have hpos : (0 : ℝ) < (7 / 4) / rhoB ^ 3 := div_pos (by norm_num) hr3
  have heq : Real.log ((7 / 4) / rhoB ^ 3) = gVal 1 := by
    rw [Real.log_div (by norm_num) (ne_of_gt hr3), Real.log_pow, gVal_one_eq]; push_cast; ring
  linarith [Real.log_le_sub_one_of_pos hpos, heq]

/-- `gVal 2 <= (11/4)/rhoB^5 - 1`. -/
theorem gVal_two_le : gVal 2 ≤ (11 / 4) / rhoB ^ 5 - 1 := by
  have hr5 : (0 : ℝ) < rhoB ^ 5 := pow_pos rhoB_pos 5
  have hpos : (0 : ℝ) < (11 / 4) / rhoB ^ 5 := div_pos (by norm_num) hr5
  have heq : Real.log ((11 / 4) / rhoB ^ 5) = gVal 2 := by
    rw [Real.log_div (by norm_num) (ne_of_gt hr5), Real.log_pow, gVal_two_eq]; push_cast; ring
  linarith [Real.log_le_sub_one_of_pos hpos, heq]

end R3Cert
