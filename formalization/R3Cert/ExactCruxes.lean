/-
  R3 (Phi <= 1) -- the EXACT-ARITHMETIC CORE of the finite certificate, formalized in Lean 4 + Mathlib.

  The entire Phi<=1 proof (E0/E1/E2/E3/DEC + the Jensen-reduced adversary sweep) is built on a small set of
  LOAD-BEARING EXACT INEQUALITIES obtained by "clearing the 11th root" of rho_B = (621/64)^(1/11).  Each is a
  pure rational/integer fact and is machine-checked here by `norm_num` / `decide`.  On top of them we prove
  the real-analytic BRIDGES actually used in the argument (omega < 0, C_1 < 1, the E2 Pell decay
  2*rho_B > 1+sqrt 2, and rho_B^2 >= 3/2) by monotonicity of `Real.rpow` / `Real.sqrt`, reducing each to its
  rational crux.

  Every arithmetic goal below was independently verified in exact Python arithmetic
  (Fraction/sympy) before being stated -- see laplacian_ratio/{lemma_proofs,e2_closure,pell_chain_structure,
  rem_tie,gap_interval_certification}.py.  The graph-theoretic DEC permanent identity and the finite interval
  SWEEP (s<=64, j<=500) are stated as `Prop`s with their Python certificates cited; discharging them needs a
  matching-theory development and an interval decision procedure respectively (see AdversarySweep.lean).

  Reference: rho_B^11 = 621/64 = 3^3 * 23 / 2^6,  L = log rho_B = (1/11) log(621/64),
             omega = log(3/2) - 2L,  C_1 = (26/23)/rho_B.
-/
import Mathlib

namespace R3Cert

open Real

/-! ## Layer 1 -- the exact rational / integer cruxes (bulletproof: `norm_num` / `decide`). -/

/-- The base identity: `rho_B^11 = 621/64 = 3^3 * 23 / 2^6`. -/
theorem rhoB_pow11_factor : (621 / 64 : ℚ) = (3 ^ 3 * 23 : ℚ) / 2 ^ 6 := by norm_num

/-- E3 shoulder crux (`rho_B^2 >= 3/2`), cleared: `(3/2)^11 <= (621/64)^2`. -/
theorem e3_crux : (3 / 2 : ℚ) ^ 11 ≤ (621 / 64 : ℚ) ^ 2 := by norm_num

/-- E3 crux is *strict* (gives `omega < 0`): `(3/2)^11 < (621/64)^2`. -/
theorem e3_crux_strict : (3 / 2 : ℚ) ^ 11 < (621 / 64 : ℚ) ^ 2 := by norm_num

/-- R5 single-hub crux (`C_1 < 1`), cleared: `(26/23)^11 < 621/64`. -/
theorem r5_crux : (26 / 23 : ℚ) ^ 11 < (621 / 64 : ℚ) := by norm_num

/-- E2 Pell-decay crux, integer form: `11753^2 > 2 * 5741^2`
    (equivalently `(2 rho_B)^11 = 2^11 * 621/64 = 19872 > (1+sqrt 2)^11 = 8119 + 5741 sqrt 2`). -/
theorem e2_pell_decay_int : (11753 : ℤ) ^ 2 > 2 * 5741 ^ 2 := by decide

/-- `(2 rho_B)^11 = 2^11 * (621/64) = 19872`. -/
theorem two_rhoB_pow11 : (2 : ℚ) ^ 11 * (621 / 64) = 19872 := by norm_num

/-- Near-star tie `R(5) = 1` exactly: `64 * 243 * 23 = 621 * 576`. -/
theorem near_star_tie : (64 * 243 * 23 : ℤ) = 621 * 576 := by decide

/-- Near-star ratio factor `529/486 = 23^2 / (2 * 3^5)`. -/
theorem near_star_ratio : (529 / 486 : ℚ) = (23 ^ 2 : ℚ) / (2 * 3 ^ 5) := by norm_num

/-- Binding-corner crux (A), part 1: `(122948/100000)^11 > 621/64`. -/
theorem corner_rpow : (122948 / 100000 : ℚ) ^ 11 > (621 / 64 : ℚ) := by norm_num

/-- Binding-corner crux (A), part 2: `132 r^2 + 4 r^3 <= 207` at `r = 122948/100000`. -/
theorem corner_poly : 132 * (122948 / 100000 : ℚ) ^ 2 + 4 * (122948 / 100000 : ℚ) ^ 3 ≤ 207 := by
  norm_num

/-- E2 single-cherry leaf `N(1,0)` sits at cavity `3/7 ∈ (2/5, 1/2)`. -/
theorem N10_in_band : (2 / 5 : ℚ) < 3 / 7 ∧ (3 / 7 : ℚ) < 1 / 2 := by
  constructor <;> norm_num

/-! ## Layer 2 -- the real-analytic bridges, reduced to the rational cruxes.

`rho_B := (621/64)^(1/11)` as a real.  The key facts used downstream are proved here from Layer 1 by
monotonicity of `x ↦ x^(11:ℕ)` and `Real.sqrt`. -/

/-- The branching growth rate `rho_B = (621/64)^(1/11)`. -/
noncomputable def rhoB : ℝ := (621 / 64 : ℝ) ^ ((1 : ℝ) / 11)

theorem rhoB_pos : 0 < rhoB := Real.rpow_pos_of_pos (by norm_num) _

/-- `rho_B ^ 11 = 621/64` (undoing the 11th root). -/
theorem rhoB_pow11 : rhoB ^ (11 : ℕ) = 621 / 64 := by
  have h : rhoB ^ (11 : ℕ) = (621 / 64 : ℝ) ^ (((1 : ℝ) / 11) * 11) := by
    rw [rhoB, ← Real.rpow_natCast ((621 / 64 : ℝ) ^ ((1 : ℝ) / 11)) 11, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h]; norm_num

/-- `rho_B^2 >= 3/2` (the E3 shoulder constant), from `e3_crux`. -/
theorem rhoB_sq_ge : (3 / 2 : ℝ) ≤ rhoB ^ 2 := by
  have hb : (0 : ℝ) < rhoB := rhoB_pos
  -- compare 11th powers: (3/2)^11 <= (621/64)^2 = (rhoB^2)^11 = rhoB^22
  have hpow : (3 / 2 : ℝ) ^ (11 : ℕ) ≤ (rhoB ^ 2) ^ (11 : ℕ) := by
    have : (rhoB ^ 2) ^ (11 : ℕ) = (621 / 64 : ℝ) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, rhoB_pow11]
    rw [this]; norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (11 : ℕ) ≠ 0) (by positivity) hpow

/-- `omega = log(3/2) - 2*log(rho_B) < 0`, from the strict E3 crux via `log` monotonicity. -/
theorem omega_neg : Real.log (3 / 2) - 2 * Real.log rhoB < 0 := by
  have hb : (0 : ℝ) < rhoB := rhoB_pos
  -- 2 log rhoB = log (rhoB^2), and (3/2) < rhoB^2 strictly
  have hlt : (3 / 2 : ℝ) < rhoB ^ 2 := by
    have hpow : (3 / 2 : ℝ) ^ (11 : ℕ) < (rhoB ^ 2) ^ (11 : ℕ) := by
      have : (rhoB ^ 2) ^ (11 : ℕ) = (621 / 64 : ℝ) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul, rhoB_pow11]
      rw [this]; norm_num
    exact lt_of_pow_lt_pow_left₀ 11 (by positivity) hpow
  have h2 : 2 * Real.log rhoB = Real.log (rhoB ^ 2) := by
    rw [Real.log_pow]; ring
  rw [h2, sub_neg]
  exact Real.log_lt_log (by norm_num) hlt

/-- `C_1 = (26/23)/rho_B < 1` (single hub uniquely optimal), from `r5_crux`. -/
theorem C1_lt_one : (26 / 23 : ℝ) / rhoB < 1 := by
  have hb : (0 : ℝ) < rhoB := rhoB_pos
  rw [div_lt_one hb]
  -- 26/23 < rhoB  ⟺  (26/23)^11 < rhoB^11 = 621/64
  have hpow : (26 / 23 : ℝ) ^ (11 : ℕ) < rhoB ^ (11 : ℕ) := by
    rw [rhoB_pow11]; norm_num
  exact lt_of_pow_lt_pow_left₀ 11 hb.le hpow

/-- E2 chain decay: `2 * rho_B > 1 + sqrt 2` (so every chain amplitude strictly decays; equivalently
    `(2 rho_B)^11 = 19872 > (1+sqrt 2)^11 = 8119 + 5741 sqrt 2`).  Proved with clean rational witnesses:
    `sqrt 2 < 17/12` (since `289 > 288`) and `rho_B > 29/24` (since `(29/24)^11 < 621/64`), whence
    `1 + sqrt 2 < 1 + 17/12 = 29/12 = 2*(29/24) < 2*rho_B`. -/
theorem e2_two_rhoB_gt : 1 + Real.sqrt 2 < 2 * rhoB := by
  have hb : (0 : ℝ) < rhoB := rhoB_pos
  -- sqrt 2 < 17/12
  have hsqrt : Real.sqrt 2 < 17 / 12 := by
    rw [show (17 / 12 : ℝ) = Real.sqrt ((17 / 12) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- rho_B > 29/24  ⟺  (29/24)^11 < rho_B^11 = 621/64
  have hrho : (29 / 24 : ℝ) < rhoB := by
    have hpow : (29 / 24 : ℝ) ^ (11 : ℕ) < rhoB ^ (11 : ℕ) := by
      rw [rhoB_pow11]; norm_num
    exact lt_of_pow_lt_pow_left₀ 11 hb.le hpow
  calc 1 + Real.sqrt 2 < 1 + 17 / 12 := by linarith
    _ = 2 * (29 / 24) := by norm_num
    _ < 2 * rhoB := by linarith

end R3Cert
