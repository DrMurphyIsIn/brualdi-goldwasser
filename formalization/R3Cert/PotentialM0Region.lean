/-
  The `m = 0` slice of `DeficitNonneg`, part 2: the `Pval`-free region and the COMPLETE `m = 0` slice.

  On the region `nl ≥ 1`, `4a + 6nl ≥ 12` the cavity `3/(4a+6nl+3) ≤ 1/5 < T0` gives `Pval = 0`, and
  the slice is the pure log bound `H0bound`.  It is proven by DOUBLE INDUCTION from the two bases
  `(2,1)` (`⟺ 51/16 ≤ rhoB⁶`) and `(0,2)` (`⟺ 5/3 ≤ rhoB³`), with two step lemmas: each step is a
  cross-multiplied rational-quadratic inequality in `(a, nl)` against a power of `rhoB` — all
  coefficients positive in `(a, nl−1)`, so `nlinarith` closes them from `rhoB ≥ 1229/1000`.

  `deficit_m0` then assembles: `nl = 0` column (= near-star), the two positive-fold bases `(0,1)`
  (exact tie) and `(1,1)`, and the region.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialM0

namespace R3Cert

open Real

/-- The `Pval`-free `m = 0` bound. -/
def H0bound (a nl : ℕ) : Prop :=
  -Lval + Real.log ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)))
    ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval

/-- `−ω = log(2·rhoB²/3)` (the `a`-step budget). -/
theorem neg_omega_eq : -omegaVal = Real.log (2 * rhoB ^ 2 / 3) := by
  have hr2 : (0 : ℝ) < rhoB ^ 2 := pow_pos rhoB_pos 2
  have h2 : Real.log (2 * rhoB ^ 2 / 3) = Real.log 2 + 2 * Real.log rhoB - Real.log 3 := by
    rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < 2 * rhoB ^ 2)) (by norm_num : (3 : ℝ) ≠ 0),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hr2), Real.log_pow]
    push_cast; ring
  have h32 : Real.log ((3 : ℝ) / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  unfold omegaVal
  rw [h32, h2, logRhoB_local]
  ring

/-- **`a`-step** (valid for `nl ≥ 1`): `H0bound a nl → H0bound (a+1) nl`. -/
theorem m0_step_a (a nl : ℕ) (hnl : 1 ≤ nl) (h : H0bound a nl) : H0bound (a + 1) nl := by
  unfold H0bound at h ⊢
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hz : (0 : ℝ) ≤ (nl : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (nl : ℝ) := by exact_mod_cast hnl
    linarith
  have hr2 : (0 : ℝ) < rhoB ^ 2 := pow_pos rhoB_pos 2
  have hb2 : ((1229 : ℝ) / 1000) ^ 2 ≤ rhoB ^ 2 := by gcongr; exact rhoB_gt_1229.le
  have hBpos : (0 : ℝ) < 3 * ((a : ℝ) + (nl : ℝ) + 1) := by linarith
  have hB'pos : (0 : ℝ) < 3 * (((a : ℝ) + 1) + (nl : ℝ) + 1) := by linarith
  have hApos : (0 : ℝ) < 4 * (a : ℝ) + 6 * (nl : ℝ) + 3 := by linarith
  have hA'pos : (0 : ℝ) < 4 * ((a : ℝ) + 1) + 6 * (nl : ℝ) + 3 := by linarith
  have hcpos : (0 : ℝ) < 2 * rhoB ^ 2 / 3 := by linarith
  have hABpos : (0 : ℝ) < (4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)) :=
    div_pos hApos hBpos
  have hle : (4 * ((a : ℝ) + 1) + 6 * (nl : ℝ) + 3) / (3 * (((a : ℝ) + 1) + (nl : ℝ) + 1))
      ≤ ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)))
        * (2 * rhoB ^ 2 / 3) := by
    rw [div_le_iff₀ hB'pos,
        show ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)))
              * (2 * rhoB ^ 2 / 3) * (3 * (((a : ℝ) + 1) + (nl : ℝ) + 1))
            = ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) * (2 * rhoB ^ 2) * (((a : ℝ) + 1) + (nl : ℝ) + 1))
                / (3 * ((a : ℝ) + (nl : ℝ) + 1)) from by ring,
        le_div_iff₀ hBpos]
    nlinarith [mul_nonneg (mul_nonneg hApos.le
        (by linarith : (0 : ℝ) ≤ ((a : ℝ) + 1) + (nl : ℝ) + 1)) (sub_nonneg.2 hb2),
      ha0, hz, mul_nonneg ha0 ha0, mul_nonneg ha0 hz, mul_nonneg hz hz]
  have hlog := Real.log_le_log (div_pos hA'pos hB'pos) hle
  rw [Real.log_mul (ne_of_gt hABpos) (ne_of_gt hcpos), ← neg_omega_eq] at hlog
  push_cast at h ⊢
  linarith [hlog, h]

/-- **`nl`-step** (valid for `nl ≥ 1`): `H0bound a nl → H0bound a (nl+1)`. -/
theorem m0_step_nl (a nl : ℕ) (hnl : 1 ≤ nl) (h : H0bound a nl) : H0bound a (nl + 1) := by
  unfold H0bound at h ⊢
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hz : (0 : ℝ) ≤ (nl : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (nl : ℝ) := by exact_mod_cast hnl
    linarith
  have hBpos : (0 : ℝ) < 3 * ((a : ℝ) + (nl : ℝ) + 1) := by linarith
  have hB'pos : (0 : ℝ) < 3 * ((a : ℝ) + ((nl : ℝ) + 1) + 1) := by linarith
  have hApos : (0 : ℝ) < 4 * (a : ℝ) + 6 * (nl : ℝ) + 3 := by linarith
  have hA'pos : (0 : ℝ) < 4 * (a : ℝ) + 6 * ((nl : ℝ) + 1) + 3 := by linarith
  have hABpos : (0 : ℝ) < (4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)) :=
    div_pos hApos hBpos
  have hle : (4 * (a : ℝ) + 6 * ((nl : ℝ) + 1) + 3) / (3 * ((a : ℝ) + ((nl : ℝ) + 1) + 1))
      ≤ ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1))) * rhoB := by
    rw [div_le_iff₀ hB'pos,
        show ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1))) * rhoB
              * (3 * ((a : ℝ) + ((nl : ℝ) + 1) + 1))
            = ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) * rhoB * ((a : ℝ) + (nl : ℝ) + 2) * 3)
                / (3 * ((a : ℝ) + (nl : ℝ) + 1)) from by ring,
        le_div_iff₀ hBpos]
    nlinarith [mul_nonneg (mul_nonneg hApos.le
        (by linarith : (0 : ℝ) ≤ (a : ℝ) + (nl : ℝ) + 2)) (sub_nonneg.2 rhoB_gt_1229.le),
      ha0, hz, mul_nonneg ha0 ha0, mul_nonneg ha0 hz, mul_nonneg hz hz]
  have hlog := Real.log_le_log (div_pos hA'pos hB'pos) hle
  rw [Real.log_mul (ne_of_gt hABpos) (ne_of_gt rhoB_pos), logRhoB_local] at hlog
  push_cast at h ⊢
  linarith [hlog, h]

/-- Base `(2, 1)`: `⟺ log(17/12) + 2·log(3/2) ≤ 6L ⟸ 51/16 ≤ rhoB⁶`. -/
theorem H0_21 : H0bound 2 1 := by
  unfold H0bound
  have h6 : (51 / 16 : ℝ) ≤ rhoB ^ 6 := by
    have hb6 : ((1229 : ℝ) / 1000) ^ 6 ≤ rhoB ^ 6 := by gcongr; exact rhoB_gt_1229.le
    nlinarith [hb6]
  have hlog6 : Real.log (rhoB ^ 6) = 6 * Lval := by
    rw [Real.log_pow, logRhoB_local]; push_cast; ring
  have hkey : Real.log ((51 : ℝ) / 16) ≤ 6 * Lval := by
    rw [← hlog6]; exact Real.log_le_log (by norm_num) h6
  have hsplit : Real.log ((51 : ℝ) / 16) = Real.log ((17 : ℝ) / 12) + 2 * Real.log ((3 : ℝ) / 2) := by
    rw [show ((51 : ℝ) / 16) = (17 / 12) * (3 / 2) ^ 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  norm_num
  unfold omegaVal
  linarith [hkey, hsplit]

/-- Base `(0, 2)`: `⟺ log(5/3) ≤ 3L ⟸ 5/3 ≤ rhoB³`. -/
theorem H0_02 : H0bound 0 2 := by
  unfold H0bound
  have h3 : (5 / 3 : ℝ) ≤ rhoB ^ 3 := by
    have hb3 : ((1229 : ℝ) / 1000) ^ 3 ≤ rhoB ^ 3 := by gcongr; exact rhoB_gt_1229.le
    nlinarith [hb3]
  have hlog3 : Real.log (rhoB ^ 3) = 3 * Lval := by
    rw [Real.log_pow, logRhoB_local]; push_cast; ring
  have hkey : Real.log ((5 : ℝ) / 3) ≤ 3 * Lval := by
    rw [← hlog3]; exact Real.log_le_log (by norm_num) h3
  norm_num
  linarith [hkey]

theorem H0_row1 (a : ℕ) (ha : 2 ≤ a) : H0bound a 1 := by
  induction a, ha using Nat.le_induction with
  | base => exact H0_21
  | succ n hn ih => exact m0_step_a n 1 le_rfl ih

theorem H0_col0 (nl : ℕ) (hnl : 2 ≤ nl) : H0bound 0 nl := by
  induction nl, hnl using Nat.le_induction with
  | base => exact H0_02
  | succ n hn ih => exact m0_step_nl 0 n (by omega) ih

theorem H0_gen (a nl : ℕ) (hnl : 2 ≤ nl) : H0bound a nl := by
  induction a with
  | zero => exact H0_col0 nl hnl
  | succ n ih => exact m0_step_a n nl (by omega) ih

/-- **`H0` on the whole `Pval`-free region** `nl ≥ 1`, `4a + 6nl ≥ 12`. -/
theorem H0_region (a nl : ℕ) (hnl : 1 ≤ nl) (hreg : 12 ≤ 4 * a + 6 * nl) : H0bound a nl := by
  rcases (by omega : 2 ≤ nl ∨ (nl = 1 ∧ 2 ≤ a)) with h2 | ⟨hnl1, ha2⟩
  · exact H0_gen a nl h2
  · subst hnl1; exact H0_row1 a ha2

/-- On the region the cavity is `≤ 1/5 < T0`, so `Pval = 0`. -/
theorem Pval_m0_zero (a nl : ℕ) (hreg : 12 ≤ 4 * a + 6 * nl) :
    Pval (3 / (4 * (a : ℝ) + 6 * (nl : ℝ) + 3)) = 0 := by
  have hregR : (12 : ℝ) ≤ 4 * (a : ℝ) + 6 * (nl : ℝ) := by exact_mod_cast hreg
  have hden : (0 : ℝ) < 4 * (a : ℝ) + 6 * (nl : ℝ) + 3 := by linarith
  refine Pval_zero_of_le_T0 ?_
  have h5 : 3 / (4 * (a : ℝ) + 6 * (nl : ℝ) + 3) ≤ 1 / 5 := by
    rw [div_le_iff₀ hden]; linarith
  linarith [T0_gt_fifth]

/-- **THE COMPLETE `m = 0` SLICE** of `DeficitNonneg`. -/
theorem deficit_m0 (a nl : ℕ) :
    -Lval + Real.log ((4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)))
        + Pval (3 / (4 * (a : ℝ) + 6 * (nl : ℝ) + 3))
      ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval := by
  rcases Nat.eq_zero_or_pos nl with h0 | h1
  · subst h0
    have h := deficit_m0_nl0 a
    have e1 : (4 * (a : ℝ) + 6 * ((0 : ℕ) : ℝ) + 3) = 4 * (a : ℝ) + 3 := by push_cast; ring
    have e2 : (3 * ((a : ℝ) + ((0 : ℕ) : ℝ) + 1)) = 3 * ((a : ℝ) + 1) := by push_cast; ring
    rw [e1, e2]
    push_cast
    linarith [h]
  · by_cases hreg : 12 ≤ 4 * a + 6 * nl
    · have hP0 := Pval_m0_zero a nl hreg
      have hH := H0_region a nl h1 hreg
      unfold H0bound at hH
      rw [hP0]
      linarith [hH]
    · have hcase : (a = 0 ∧ nl = 1) ∨ (a = 1 ∧ nl = 1) := by omega
      rcases hcase with ⟨ha, hnl⟩ | ⟨ha, hnl⟩
      · subst ha; subst hnl
        have h := deficit_m0_01
        have e1 : (4 * ((0 : ℕ) : ℝ) + 6 * ((1 : ℕ) : ℝ) + 3) = 9 := by push_cast; ring
        have e2 : (3 * (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1)) = 6 := by push_cast; ring
        rw [e1, e2, show (3 : ℝ) / 9 = 1 / 3 by norm_num]
        push_cast
        linarith [h]
      · subst ha; subst hnl
        have h := deficit_m0_11
        have e1 : (4 * ((1 : ℕ) : ℝ) + 6 * ((1 : ℕ) : ℝ) + 3) = 13 := by push_cast; ring
        have e2 : (3 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1)) = 9 := by push_cast; ring
        rw [e1, e2]
        push_cast
        linarith [h]

end R3Cert
