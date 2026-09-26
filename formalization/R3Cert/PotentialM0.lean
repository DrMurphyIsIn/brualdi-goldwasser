/-
  The `m = 0` slice of `DeficitNonneg`, part 1: the `nl = 0` column and the tight base cases.

  With no generic children (`m = 0`, hence `Sg = 0`) the deficit inequality is the arm-and-leaf
  family: `−L + log((4a+6nl+3)/(3(a+nl+1))) + Pval(3/(4a+6nl+3)) ≤ a·(−ω) + nl·L`.

  * `nl = 0` column: IDENTICAL to the near-star family — the identity
    `−L + log((4a+3)/(3(a+1))) = gVal a − a·ω` turns it into `nearStar_super a` (already proven,
    including the tie `a = 5`).
  * `(a, nl) = (0, 1)` (the ARM node): exact EQUALITY, by the definition of `ω`.
  * `(a, nl) = (1, 1)`: the last case with a positive fold (`cav = 3/13 > T0`); closed by the
    `log x ≤ x − 1` + `rhoB`-interval pattern.

  The remaining `m = 0` region (`nl ≥ 1`, `4a + 6nl ≥ 12`, where `Pval = 0`) follows in part 2 by
  double induction with two rational-quadratic step lemmas.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialNearStar

namespace R3Cert

open Real

/-- The `nl = 0` log identity: `−L + log((4a+3)/(3(a+1))) = gVal a − a·ω`. -/
theorem m0_log_nl0 (a : ℕ) :
    -Lval + Real.log ((4 * (a : ℝ) + 3) / (3 * ((a : ℝ) + 1))) = gVal a - (a : ℝ) * omegaVal := by
  have hnum : (0 : ℝ) < 4 * (a : ℝ) + 3 := by positivity
  have hden : (0 : ℝ) < 3 * ((a : ℝ) + 1) := by positivity
  rw [Real.log_div (ne_of_gt hnum) (ne_of_gt hden)]
  unfold gVal omegaVal
  ring

/-- **`m = 0`, `nl = 0` column** — exactly the near-star super-solution. -/
theorem deficit_m0_nl0 (a : ℕ) :
    -Lval + Real.log ((4 * (a : ℝ) + 3) / (3 * ((a : ℝ) + 1)))
      + Pval (3 / (4 * (a : ℝ) + 3)) ≤ (a : ℝ) * (-omegaVal) := by
  rw [m0_log_nl0]
  linarith [nearStar_super a]

/-- **`(a, nl) = (0, 1)`: the ARM node — exact equality** (`−L + log(3/2) − ω = L`). -/
theorem deficit_m0_01 :
    -Lval + Real.log ((9 : ℝ) / 6) + Pval (1 / 3) ≤ Lval := by
  rw [Pval_third, show ((9 : ℝ) / 6) = 3 / 2 by norm_num]
  unfold omegaVal
  linarith

/-- `Pval (3/13) = (11/50)·(16/13 − rhoB)` (the cavity `3/13` sits just above `T0`). -/
theorem Pval_313 : Pval (3 / 13) = (11 / 50) * (16 / 13 - rhoB) := by
  have hge : (0 : ℝ) ≤ 3 / 13 - T0 := by
    unfold T0; linarith [rhoB_lt_123]
  rw [Pval_struct (3 / 13) (by norm_num) (by norm_num), max_eq_right hge]
  unfold T0; ring

/-- **`(a, nl) = (1, 1)`** — the last positive-fold base case. -/
theorem deficit_m0_11 :
    -Lval + Real.log ((13 : ℝ) / 9) + Pval (3 / 13) ≤ -omegaVal + Lval := by
  rw [Pval_313]
  -- goal ⟺ log(13/6) − 4L + (11/50)(16/13 − rhoB) ≤ 0
  have hr4 : (0 : ℝ) < rhoB ^ 4 := pow_pos rhoB_pos 4
  have hlog : Real.log ((13 : ℝ) / 9) + Real.log ((3 : ℝ) / 2) = Real.log ((13 : ℝ) / 6) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h4 : Real.log (rhoB ^ 4) = 4 * Lval := by
    rw [Real.log_pow, logRhoB_local]; push_cast; ring
  have hup : Real.log ((13 : ℝ) / 6) - 4 * Lval ≤ (13 / 6) / rhoB ^ 4 - 1 := by
    have hpos : (0 : ℝ) < (13 / 6) / rhoB ^ 4 := div_pos (by norm_num) hr4
    have heq : Real.log ((13 / 6) / rhoB ^ 4) = Real.log ((13 : ℝ) / 6) - 4 * Lval := by
      rw [Real.log_div (by norm_num) (ne_of_gt hr4), h4]
    linarith [Real.log_le_sub_one_of_pos hpos, heq.ge]
  have hpoly : (13 / 6 : ℝ) / rhoB ^ 4 - 1 + (11 / 50) * (16 / 13 - rhoB) ≤ 0 := by
    have hb4 : ((1229 : ℝ) / 1000) ^ 4 ≤ rhoB ^ 4 := by gcongr; exact rhoB_gt_1229.le
    have hb5 : ((1229 : ℝ) / 1000) ^ 5 ≤ rhoB ^ 5 := by gcongr; exact rhoB_gt_1229.le
    have hkey : 13 / 6 - rhoB ^ 4 + (11 / 50) * (16 / 13 - rhoB) * rhoB ^ 4 ≤ 0 := by
      nlinarith [hb4, hb5]
    have hcancel : (13 / 6 : ℝ) / rhoB ^ 4 * rhoB ^ 4 = 13 / 6 :=
      div_mul_cancel₀ _ (ne_of_gt hr4)
    nlinarith [hkey, hcancel, hr4]
  -- assemble: −L + log(13/9) + (11/50)(16/13−ρ) ≤ −ω + L, with ω = log(3/2) − 2L
  have homega : -omegaVal + Lval = 3 * Lval - Real.log ((3 : ℝ) / 2) := by
    unfold omegaVal; ring
  rw [homega]
  linarith [hup, hpoly, hlog]

end R3Cert
