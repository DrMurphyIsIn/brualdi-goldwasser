/-
  E-family foundations: rational-in-`rhoB` budget lower bounds, fold-branch resolvers, and the
  `E2` linear-part identity.

  Everything an endpoint-family proof needs to become a PURE rational inequality in
  `(a, nl, m, rhoB)` over the interval `rhoB ∈ (1229/1000, 123/100)`:
  * `neg_omega_ge` : `−ω ≥ 1 − 3/(2·rhoB²)`  (`log x ≥ 1 − 1/x`)
  * `Lval_ge`      : `L ≥ (rhoB − 1)/rhoB`
  * `fold_zero` / `fold_active` : resolve `(y − T0)₊` once `y` is on a known side of
    `(229/1000, 23/100) ∋ T0`
  * `e2_lin`       : `(C + m·T0)/(N+1) − T0 = (C − T0(a+nl+1))/(N+1)` — kills the `m·T0` coupling.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialM0Region
import R3Cert.PotentialM1Piece

namespace R3Cert

open Real

/-- **Rational budget for arms:** `1 − 3/(2·rhoB²) ≤ −ω`. -/
theorem neg_omega_ge : 1 - 3 / (2 * rhoB ^ 2) ≤ -omegaVal := by
  have hr2 : (0 : ℝ) < rhoB ^ 2 := pow_pos rhoB_pos 2
  have hpos : (0 : ℝ) < 3 / (2 * rhoB ^ 2) := div_pos (by norm_num) (by linarith)
  have h1 : omegaVal = Real.log (3 / (2 * rhoB ^ 2)) := by
    have hne := neg_omega_eq
    rw [show (3 / (2 * rhoB ^ 2) : ℝ) = (2 * rhoB ^ 2 / 3)⁻¹ from (inv_div _ _).symm,
        Real.log_inv]
    linarith [hne]
  have h2 := Real.log_le_sub_one_of_pos hpos
  rw [← h1] at h2
  linarith [h2]

/-- **Rational budget for leaves:** `(rhoB − 1)/rhoB ≤ L`. -/
theorem Lval_ge : (rhoB - 1) / rhoB ≤ Lval := by
  have hpos : (0 : ℝ) < rhoB⁻¹ := inv_pos.2 rhoB_pos
  have h2 := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_inv, logRhoB_local] at h2
  have hsplit : (rhoB - 1) / rhoB = 1 - rhoB⁻¹ := by
    rw [sub_div, div_self (ne_of_gt rhoB_pos), one_div]
  linarith [h2, hsplit.le, hsplit.ge]

/-- **Fold-zero branch:** `y ≤ 229/1000 → (y − T0)₊ = 0` (since `T0 > 229/1000`). -/
theorem fold_zero {y : ℝ} (h : y ≤ 229 / 1000) : max 0 (y - T0) = 0 :=
  max_eq_left (by unfold T0; linarith [rhoB_gt_1229])

/-- **Fold-active branch:** `23/100 ≤ y → (y − T0)₊ = y − T0` (since `T0 < 23/100`). -/
theorem fold_active {y : ℝ} (h : 23 / 100 ≤ y) : max 0 (y - T0) = y - T0 :=
  max_eq_right (by unfold T0; linarith [rhoB_lt_123])

/-- **`E2` linear-part identity:** the `m·T0` coupling cancels,
    `(C + m·T0)/(N+1) − T0 = (C − T0(a+nl+1))/(N+1)`. -/
theorem e2_lin (a nl m : ℕ) :
    ((a : ℝ) / 3 + nl + (m : ℝ) * T0) / ((a : ℝ) + nl + m + 1) - T0
      = ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1)) / ((a : ℝ) + nl + m + 1) := by
  have hN : ((a : ℝ) + nl + m + 1) ≠ 0 := by positivity
  field_simp
  ring

end R3Cert
