/-
  E2 part 1: the kink endpoint family on the main region `4a + 6nl ≥ 10` — THE mathematical heart.

  At the kink `Sg = m·T0` the `m·T0` coupling cancels (`e2_lin`): the linear part becomes
  `J/((N+1)·rhoB)` with `J = a/3 + nl − T0(a+nl+1)` INDEPENDENT of `m`.  On `4a+6nl ≥ 10` the
  cavity is `≤ 1/5 ≤ 229/1000`, so the fold vanishes and the whole family reduces (by
  `m`-monotonicity for `J > 0`, trivially for `J ≤ 0`) to ONE 2-parameter polynomial inequality
  `J ≤ (a·c₁ + nl·c₂)·(a+nl+2)·rhoB` with the constant rational budgets
  `c₁ = 10441/1510441 ≤ −ω`, `c₂ = 229/1229 ≤ L`.  Its `nl = 0` slice is a positive-definite
  quadratic in `a` (vertex `a ≈ 36/7` — the near-star-adjacent tight direction, margin `+0.0047`).

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialM1Piece
import R3Cert.PotentialEBase

namespace R3Cert

open Real

/-- **Constant rational budget for arms:** `10441/1510441 ≤ −ω`. -/
theorem neg_omega_ge_const : (10441 / 1510441 : ℝ) ≤ -omegaVal := by
  have hr2 : (0 : ℝ) < rhoB ^ 2 := pow_pos rhoB_pos 2
  have hb2 : ((1229 : ℝ) / 1000) ^ 2 ≤ rhoB ^ 2 := by gcongr; exact rhoB_gt_1229.le
  have h1 : 3 / (2 * rhoB ^ 2) ≤ 3 / (2 * ((1229 : ℝ) / 1000) ^ 2) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * rhoB ^ 2)
      (by norm_num : (0 : ℝ) < 2 * ((1229 : ℝ) / 1000) ^ 2)]
    nlinarith [hb2]
  have hnum : (1 : ℝ) - 3 / (2 * ((1229 : ℝ) / 1000) ^ 2) = 10441 / 1510441 := by norm_num
  linarith [neg_omega_ge, h1, hnum.le, hnum.ge]

/-- **Constant rational budget for leaves:** `229/1229 ≤ L`. -/
theorem Lval_ge_const : (229 / 1229 : ℝ) ≤ Lval := by
  have h2 : 1 / rhoB ≤ 1000 / 1229 := by
    rw [div_le_div_iff₀ rhoB_pos (by norm_num : (0 : ℝ) < 1229)]
    linarith [rhoB_gt_1229]
  have h3 : (rhoB - 1) / rhoB = 1 - 1 / rhoB := by
    rw [sub_div, div_self (ne_of_gt rhoB_pos)]
  linarith [Lval_ge, h2, h3.le, h3.ge]

/-- **`starLHS` at the kink, `J`-form:** the `m·T0` coupling cancels. -/
theorem starLHS_kink (a nl m : ℕ) :
    starLHS a nl m ((m : ℝ) * T0)
      = ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1)) / (((a : ℝ) + nl + m + 1) * rhoB)
        + (11 / 50) * max 0
            (1 / (((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0) - T0) := by
  have hden : (a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + (m : ℝ) * T0)
      = ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0 := by ring
  unfold starLHS
  rw [e2_lin, div_div, hden]

/-- On `4a + 6nl ≥ 10` the kink cavity is `≤ 1/5 < T0`: the fold vanishes (all `m ≥ 1`). -/
theorem kink_fold_zero (a nl m : ℕ) (hm : 1 ≤ m) (h10 : 10 ≤ 4 * a + 6 * nl) :
    max 0 (1 / (((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0) - T0) = 0 := by
  apply fold_zero
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h10R : (10 : ℝ) ≤ 4 * (a : ℝ) + 6 * (nl : ℝ) := by exact_mod_cast h10
  have hT0 : (229 / 1000 : ℝ) < T0 := by unfold T0; linarith [rhoB_gt_1229]
  have hT0m : (1 : ℝ) * T0 ≤ (m : ℝ) * T0 :=
    mul_le_mul_of_nonneg_right hmR (by linarith : (0 : ℝ) ≤ T0)
  have hD : (5 : ℝ) ≤ ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0 := by
    linarith [hT0m]
  rw [div_le_iff₀ (by linarith :
    (0 : ℝ) < ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0)]
  linarith [hD]

/-- **The 2-parameter polynomial heart:** `J ≤ (a·c₁ + nl·c₂)·(a+nl+2)·rhoB` on `4a+6nl ≥ 10`.
    The `nl = 0` slice is positive-definite in `a` (hint `(7a − 36)²`). -/
theorem e2_poly (a nl : ℕ) (h10 : 10 ≤ 4 * a + 6 * nl) :
    (a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1)
      ≤ ((a : ℝ) * (10441 / 1510441) + (nl : ℝ) * (229 / 1229))
          * (((a : ℝ) + nl + 1) + 1) * rhoB := by
  have hr1 : (1229 / 1000 : ℝ) < rhoB := rhoB_gt_1229
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hnl0 : (0 : ℝ) ≤ (nl : ℝ) := Nat.cast_nonneg nl
  have h10R : (10 : ℝ) ≤ 4 * (a : ℝ) + 6 * (nl : ℝ) := by exact_mod_cast h10
  have hs : (0 : ℝ) ≤ rhoB - 1229 / 1000 := by linarith
  have hslack : (0 : ℝ) ≤ (nl : ℝ) * (4 * (a : ℝ) + 6 * (nl : ℝ) - 10) :=
    mul_nonneg hnl0 (by linarith [h10R])
  unfold T0
  nlinarith [sq_nonneg (7 * (a : ℝ) - 36), hslack, mul_nonneg ha0 hnl0, mul_nonneg hnl0 hnl0,
    mul_nonneg ha0 ha0, mul_nonneg (mul_nonneg ha0 ha0) hs, mul_nonneg (mul_nonneg ha0 hnl0) hs,
    mul_nonneg (mul_nonneg hnl0 hnl0) hs, mul_nonneg ha0 hs, mul_nonneg hnl0 hs, hs, h10R]

/-- **E2 on the main region** `4a + 6nl ≥ 10`, all `m ≥ 1`. -/
theorem e2_main (a nl m : ℕ) (hm : 1 ≤ m) (h10 : 10 ≤ 4 * a + 6 * nl) :
    starLHS a nl m ((m : ℝ) * T0) ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval := by
  rw [starLHS_kink, kink_fold_zero a nl m hm h10, mul_zero, add_zero]
  have hr1 : (1229 / 1000 : ℝ) < rhoB := rhoB_gt_1229
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hnl0 : (0 : ℝ) ≤ (nl : ℝ) := Nat.cast_nonneg nl
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hbudget : (a : ℝ) * (10441 / 1510441) + (nl : ℝ) * (229 / 1229)
      ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval := by
    have h1 := mul_le_mul_of_nonneg_left neg_omega_ge_const ha0
    have h2 := mul_le_mul_of_nonneg_left Lval_ge_const hnl0
    linarith [h1, h2]
  have hb0 : (0 : ℝ) ≤ (a : ℝ) * (10441 / 1510441) + (nl : ℝ) * (229 / 1229) := by positivity
  rcases le_total ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1)) 0 with hJ | hJ
  · -- J ≤ 0: left side nonpositive, budget nonnegative
    have hNpos : (0 : ℝ) < ((a : ℝ) + nl + m + 1) * rhoB :=
      mul_pos (by linarith) rhoB_pos
    have hL0 : ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1))
        / (((a : ℝ) + nl + m + 1) * rhoB) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hJ hNpos.le
    linarith [hL0, hb0, hbudget]
  · -- J > 0: monotone in m down to m = 1, then the polynomial heart
    have hpos1 : (0 : ℝ) < (((a : ℝ) + nl + 1) + 1) * rhoB :=
      mul_pos (by linarith) rhoB_pos
    have hposm : (0 : ℝ) < ((a : ℝ) + nl + m + 1) * rhoB :=
      mul_pos (by linarith) rhoB_pos
    have hd : 1 / (((a : ℝ) + nl + m + 1) * rhoB) ≤ 1 / ((((a : ℝ) + nl + 1) + 1) * rhoB) := by
      apply one_div_le_one_div_of_le hpos1
      have hle : (((a : ℝ) + nl + 1) + 1) ≤ ((a : ℝ) + nl + m + 1) := by linarith
      exact mul_le_mul_of_nonneg_right hle rhoB_pos.le
    have hmono : ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1))
          / (((a : ℝ) + nl + m + 1) * rhoB)
        ≤ ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1))
          / ((((a : ℝ) + nl + 1) + 1) * rhoB) := by
      rw [div_eq_mul_one_div _ ((((a : ℝ) + nl + m + 1)) * rhoB),
          div_eq_mul_one_div _ (((((a : ℝ) + nl + 1) + 1)) * rhoB)]
      exact mul_le_mul_of_nonneg_left hd hJ
    have hkey : ((a : ℝ) / 3 + nl - T0 * ((a : ℝ) + nl + 1))
          / ((((a : ℝ) + nl + 1) + 1) * rhoB)
        ≤ (a : ℝ) * (10441 / 1510441) + (nl : ℝ) * (229 / 1229) := by
      rw [div_le_iff₀ hpos1]
      have := e2_poly a nl h10
      linarith [this]
    linarith [hmono, hkey, hbudget]

end R3Cert
