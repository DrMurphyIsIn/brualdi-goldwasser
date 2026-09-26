/-
  LEMMA A (arithmetic core), toward the explicit-potential proof of `Phi <= 1`.

  From proof_via_explicit_potential.py / lemma_A_proof.py: the charge of a node with `a` arms, `nl in {0,1}`
  leaf, and `m` structural children ALL at cavity `T0 = rhoB - 1` is nonpositive.  Exponentiating and using
  `1 + T0 = rhoB`, this reduces to

      chi(T0) <= 0   <=>   m * (Cval a nl - rhoB) + Bval a nl >= 0,
      Cval a nl = rhoB^(1+nl+2a) * (2/3)^a,   Bval a nl = (a+nl+1) * Cval a nl - (4a/3 + 2nl + 1).

  Since `m >= 0`, it suffices to show  `Cval a nl >= rhoB`  and  `Bval a nl >= 0`.  This file proves the two
  ELEMENTARY pieces (from the already-proven `rhoB_sq_ge : 3/2 <= rhoB^2`):
    * `Cval_ge_rhoB`      (Step 1: C >= r),
    * `Bval_a1_nonneg`    (Step 2: B(a,1) >= 0, the nl=1 case),
    * `lemmaA_arith_of_B0`(combination, conditional on the near-star case `Bval a 0 >= 0`).
  The remaining piece `Bval a 0 >= 0` is EXACTLY the near-star bound `gVal_nonpos` (g(a) = gVal a; the
  connection is `Bval a 0 >= 0  <=>  gVal a <= 0`); it is wired in a follow-up increment.

  All proofs are genuine (no `sorry`, no `Prop := True`).
-/
import Mathlib
import R3Cert.ExactCruxes
import R3Cert.Sweep
import R3Cert.JTail

namespace R3Cert

open Real

/-- `log rhoB = Lval` (`rhoB^11 = 621/64`). -/
theorem logRhoB_local : Real.log rhoB = Lval := by
  have h : (11 : ℝ) * Real.log rhoB = Real.log (621 / 64) := by
    rw [← rhoB_pow11, Real.log_pow]; push_cast; ring
  unfold Lval; linarith

/-- `rhoB > 1` (from `3/2 <= rhoB^2`). -/
theorem rhoB_gt_one : (1 : ℝ) < rhoB := by
  nlinarith [rhoB_sq_ge, rhoB_pos, sq_nonneg (rhoB - 1)]

theorem rhoB_ge_one : (1 : ℝ) ≤ rhoB := le_of_lt rhoB_gt_one

/-- The geometric base `rhoB^2 * (2/3) >= 1`. -/
theorem base_ge_one : (1 : ℝ) ≤ rhoB ^ 2 * (2 / 3) := by
  nlinarith [rhoB_sq_ge]

/-- `C(a,nl) = rhoB^(1+nl+2a) * (2/3)^a`. -/
noncomputable def Cval (a nl : ℕ) : ℝ := rhoB ^ (1 + nl + 2 * a) * (2 / 3) ^ a

/-- `B(a,nl) = (a+nl+1) * C(a,nl) - (4a/3 + 2nl + 1)`. -/
noncomputable def Bval (a nl : ℕ) : ℝ :=
  ((a : ℝ) + (nl : ℝ) + 1) * Cval a nl - (4 * (a : ℝ) / 3 + 2 * (nl : ℝ) + 1)

/-- Factorization `C(a,nl) = rhoB * (rhoB^nl * (rhoB^2 * (2/3))^a)`. -/
theorem Cval_factor (a nl : ℕ) :
    Cval a nl = rhoB * (rhoB ^ nl * (rhoB ^ 2 * (2 / 3)) ^ a) := by
  unfold Cval
  rw [mul_pow, ← pow_mul]
  have h : rhoB ^ (1 + nl + 2 * a) = rhoB * rhoB ^ nl * rhoB ^ (2 * a) := by
    rw [pow_add, pow_add, pow_one]
  rw [h]; ring

/-- **Step 1: `C(a,nl) >= rhoB`.** -/
theorem Cval_ge_rhoB (a nl : ℕ) : rhoB ≤ Cval a nl := by
  rw [Cval_factor]
  have h1 : (1 : ℝ) ≤ rhoB ^ nl := one_le_pow₀ rhoB_ge_one
  have h2 : (1 : ℝ) ≤ (rhoB ^ 2 * (2 / 3)) ^ a := one_le_pow₀ base_ge_one
  have hprod : (1 : ℝ) ≤ rhoB ^ nl * (rhoB ^ 2 * (2 / 3)) ^ a := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ rhoB ^ nl * (rhoB ^ 2 * (2 / 3)) ^ a :=
          mul_le_mul h1 h2 (by norm_num) (le_trans (by norm_num) h1)
  nlinarith [rhoB_pos, hprod]

/-- `C(a,nl)` is positive. -/
theorem Cval_pos (a nl : ℕ) : 0 < Cval a nl := lt_of_lt_of_le rhoB_pos (Cval_ge_rhoB a nl)

/-- **Step 2: `B(a,1) >= 0`** (the `nl = 1` case, elementary; no tie). -/
theorem Bval_a1_nonneg (a : ℕ) : 0 ≤ Bval a 1 := by
  have hbase : (1 : ℝ) ≤ (rhoB ^ 2 * (2 / 3)) ^ a := one_le_pow₀ base_ge_one
  -- C(a,1) = rhoB^2 * (rhoB^2*(2/3))^a  >=  rhoB^2  >=  3/2
  have hC : Cval a 1 = rhoB ^ 2 * (rhoB ^ 2 * (2 / 3)) ^ a := by
    unfold Cval
    rw [mul_pow, ← pow_mul]
    have h : rhoB ^ (1 + 1 + 2 * a) = rhoB ^ 2 * rhoB ^ (2 * a) := by
      rw [show 1 + 1 + 2 * a = 2 + 2 * a from by ring, pow_add]
    rw [h]; ring
  have hCge : (3 / 2 : ℝ) ≤ Cval a 1 := by
    rw [hC]
    calc (3 / 2 : ℝ) = (3 / 2) * 1 := by ring
      _ ≤ rhoB ^ 2 * (rhoB ^ 2 * (2 / 3)) ^ a :=
          mul_le_mul rhoB_sq_ge hbase (by norm_num) (by nlinarith [rhoB_sq_ge])
  -- B(a,1) = (a+2) C(a,1) - (4a/3+3) >= (a+2)(3/2) - (4a/3+3) = a/6 >= 0
  have hCpos : 0 < Cval a 1 := Cval_pos a 1
  have hcast : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  unfold Bval
  have hlow : ((a : ℝ) + 1 + 1) * Cval a 1 ≥ ((a : ℝ) + 1 + 1) * (3 / 2) := by
    apply mul_le_mul_of_nonneg_left hCge
    positivity
  push_cast
  nlinarith [hlow, hcast]

/-- `C(a,0) = rhoB^(1+2a) * (2/3)^a` (the `nl = 0` case; `1+0+2a` reduces to `1+2a`). -/
theorem Cval_nl0 (a : ℕ) : Cval a 0 = rhoB ^ (1 + 2 * a) * (2 / 3) ^ a := rfl

/-- **Step 3: `B(a,0) >= 0`** -- EXACTLY the near-star bound `gVal_nonpos` (`g(a) = gVal a`).
    Connection: `log((3/2)^a (4a+3)) - log(rhoB^(1+2a) · 3(a+1)) = gVal a`. -/
theorem Bval_a0_nonneg (a : ℕ) : 0 ≤ Bval a 0 := by
  have hp1 : (0 : ℝ) < (3 / 2 : ℝ) ^ a := by positivity
  have hp2 : (0 : ℝ) < 4 * (a : ℝ) + 3 := by positivity
  have hp3 : (0 : ℝ) < rhoB ^ (1 + 2 * a) := pow_pos rhoB_pos _
  have hp4 : (0 : ℝ) < 3 * ((a : ℝ) + 1) := by positivity
  have hA : (0 : ℝ) < (3 / 2 : ℝ) ^ a * (4 * (a : ℝ) + 3) := mul_pos hp1 hp2
  have hB : (0 : ℝ) < rhoB ^ (1 + 2 * a) * (3 * ((a : ℝ) + 1)) := mul_pos hp3 hp4
  have hlogeq : Real.log ((3 / 2 : ℝ) ^ a * (4 * (a : ℝ) + 3))
      - Real.log (rhoB ^ (1 + 2 * a) * (3 * ((a : ℝ) + 1))) = gVal a := by
    rw [Real.log_mul hp1.ne' hp2.ne', Real.log_mul hp3.ne' hp4.ne',
        Real.log_pow, Real.log_pow, logRhoB_local]
    unfold gVal; push_cast; ring
  have hg : Real.log ((3 / 2 : ℝ) ^ a * (4 * (a : ℝ) + 3))
      ≤ Real.log (rhoB ^ (1 + 2 * a) * (3 * ((a : ℝ) + 1))) := by
    have h0 := gVal_nonpos a; linarith
  have key : (3 / 2 : ℝ) ^ a * (4 * (a : ℝ) + 3) ≤ rhoB ^ (1 + 2 * a) * (3 * ((a : ℝ) + 1)) := by
    have h := Real.exp_le_exp.mpr hg
    rwa [Real.exp_log hA, Real.exp_log hB] at h
  have hk := mul_le_mul_of_nonneg_right key (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ a)
  have hmul : (3 / 2 : ℝ) ^ a * (2 / 3) ^ a = 1 := by rw [← mul_pow]; norm_num
  have hLHS : ((3 / 2 : ℝ) ^ a * (4 * (a : ℝ) + 3)) * (2 / 3) ^ a = 4 * (a : ℝ) + 3 := by
    have e : ((3 / 2 : ℝ) ^ a * (4 * (a : ℝ) + 3)) * (2 / 3) ^ a
        = ((3 / 2 : ℝ) ^ a * (2 / 3) ^ a) * (4 * (a : ℝ) + 3) := by ring
    rw [e, hmul, one_mul]
  have hRHS : (rhoB ^ (1 + 2 * a) * (3 * ((a : ℝ) + 1))) * (2 / 3) ^ a
      = 3 * ((a : ℝ) + 1) * (rhoB ^ (1 + 2 * a) * (2 / 3) ^ a) := by ring
  rw [hLHS, hRHS, ← Cval_nl0 a] at hk
  -- hk : 4a+3 ≤ 3(a+1) * Cval a 0
  unfold Bval
  push_cast
  nlinarith [hk]

/-- **Combination (conditional on the near-star case).**  Given `Bval a 0 >= 0`, Lemma A's arithmetic
    inequality `m*(C - r) + B >= 0` holds for all `m` (and all `nl in {0,1}`). -/
theorem lemmaA_arith_of_B0 (a nl m : ℕ) (hnl : nl ≤ 1) (hB0 : 0 ≤ Bval a 0) :
    0 ≤ (m : ℝ) * (Cval a nl - rhoB) + Bval a nl := by
  have hCr : 0 ≤ Cval a nl - rhoB := by linarith [Cval_ge_rhoB a nl]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB : 0 ≤ Bval a nl := by
    rcases (by omega : nl = 0 ∨ nl = 1) with h | h
    · subst h; exact hB0
    · subst h; exact Bval_a1_nonneg a
  have : 0 ≤ (m : ℝ) * (Cval a nl - rhoB) := mul_nonneg hm hCr
  linarith

/-- **Lemma A (arithmetic), unconditional:** for all `a`, `nl <= 1`, `m`,
    `m*(Cval a nl - rhoB) + Bval a nl >= 0`.  (`chi_v(y=T0) <= 0` in exponentiated form.) -/
theorem lemmaA_arith (a nl m : ℕ) (hnl : nl ≤ 1) :
    0 ≤ (m : ℝ) * (Cval a nl - rhoB) + Bval a nl :=
  lemmaA_arith_of_B0 a nl m hnl (Bval_a0_nonneg a)

end R3Cert
