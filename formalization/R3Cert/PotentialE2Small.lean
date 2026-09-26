/-
  E2 part 2: the small corner `4a + 6nl ≤ 9` — `(a,nl) ∈ {(0,0), (1,0), (2,0), (0,1)}` — and the
  full `E2Bound`.

  Method: `starLHS_kink` puts the left side in `J/((N+1)·rhoB) + (11/50)·(cav − T0)₊` form; each
  case closes by monotone rational bounds at the interval corners (`T0 ∈ (229/1000, 23/100)`,
  `rhoB ∈ (1229/1000, 123/100)`): the fold resolves by `fold_zero`/`fold_active`, each fraction
  compares against an exact rational corner via `div_le_iff₀`-clearing.  Margins are comfortable
  (`≲ −0.02` for the `≤ 0` cases, budget slack `≳ +0.04` for `(0,1)`).

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialM1Piece
import R3Cert.PotentialEBase
import R3Cert.PotentialE2

namespace R3Cert

open Real

theorem T0_gt_229 : (229 / 1000 : ℝ) < T0 := by unfold T0; linarith [rhoB_gt_1229]

theorem T0_lt_23 : T0 < 23 / 100 := by unfold T0; linarith [rhoB_lt_123]

/-- The constant budgets bound the true budgets (extracted for reuse). -/
theorem budget_const_le (a nl : ℕ) :
    (a : ℝ) * (10441 / 1510441) + (nl : ℝ) * (229 / 1229)
      ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval := by
  have h1 := mul_le_mul_of_nonneg_left neg_omega_ge_const (Nat.cast_nonneg (α := ℝ) a)
  have h2 := mul_le_mul_of_nonneg_left Lval_ge_const (Nat.cast_nonneg (α := ℝ) nl)
  linarith [h1, h2]

/-- **Exact case `(0,0,1)`:** `−T0/(2ρ) + (11/50)(1/(2+T0) − T0) ≤ 0`. -/
theorem e2_case_001 :
    -T0 / (2 * rhoB) + (11 / 50) * max 0 (1 / (2 + T0) - T0) ≤ 0 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229; have hr2 := rhoB_lt_123
  have hden : (0 : ℝ) < 2 + T0 := by linarith
  have hact : (23 / 100 : ℝ) ≤ 1 / (2 + T0) := by
    rw [le_div_iff₀ hden]; nlinarith [hT2]
  rw [fold_active hact]
  have h1 : 1 / (2 + T0) ≤ 1000 / 2229 := by
    rw [div_le_iff₀ hden]; linarith
  have h2 : -T0 / (2 * rhoB) ≤ -(229 / 2460) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * rhoB)]
    nlinarith [hT1, hr2]
  linarith [h1, h2, hT1]

/-- **Exact case `(0,0,2)`:** `−T0/(3ρ) + (11/50)(1/(3+2T0) − T0) ≤ 0`. -/
theorem e2_case_002 :
    -T0 / (3 * rhoB) + (11 / 50) * max 0 (1 / (3 + 2 * T0) - T0) ≤ 0 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229; have hr2 := rhoB_lt_123
  have hden : (0 : ℝ) < 3 + 2 * T0 := by linarith
  have hact : (23 / 100 : ℝ) ≤ 1 / (3 + 2 * T0) := by
    rw [le_div_iff₀ hden]; nlinarith [hT2]
  rw [fold_active hact]
  have h1 : 1 / (3 + 2 * T0) ≤ 1000 / 3458 := by
    rw [div_le_iff₀ hden]; linarith
  have h2 : -T0 / (3 * rhoB) ≤ -(229 / 3690) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 3 * rhoB)]
    nlinarith [hT1, hr2]
  linarith [h1, h2, hT1]

/-- **Exact case `(1,0,1)`:** `(1/3 − 2T0)/(3ρ) + (11/50)(1/(10/3+T0) − T0) ≤ 0`. -/
theorem e2_case_101 :
    (1 / 3 - 2 * T0) / (3 * rhoB) + (11 / 50) * max 0 (1 / (10 / 3 + T0) - T0) ≤ 0 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229; have hr2 := rhoB_lt_123
  have hden : (0 : ℝ) < 10 / 3 + T0 := by linarith
  have hact : (23 / 100 : ℝ) ≤ 1 / (10 / 3 + T0) := by
    rw [le_div_iff₀ hden]; nlinarith [hT2]
  rw [fold_active hact]
  have h1 : 1 / (10 / 3 + T0) ≤ 3000 / 10687 := by
    rw [div_le_iff₀ hden]; linarith
  have h2 : (1 / 3 - 2 * T0) / (3 * rhoB) ≤ -(33 / 1000) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 3 * rhoB)]
    nlinarith [hT1, hr2]
  linarith [h1, h2, hT1]

/-- **Exact case `(0,1,1)`:** `(1 − 2T0)/(3ρ) + (11/50)(1/(4+T0) − T0) ≤ 229/1229`. -/
theorem e2_case_011 :
    (1 - 2 * T0) / (3 * rhoB) + (11 / 50) * max 0 (1 / (4 + T0) - T0) ≤ 229 / 1229 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229; have hr2 := rhoB_lt_123
  have hden : (0 : ℝ) < 4 + T0 := by linarith
  have hact : (23 / 100 : ℝ) ≤ 1 / (4 + T0) := by
    rw [le_div_iff₀ hden]; nlinarith [hT2]
  rw [fold_active hact]
  have h1 : 1 / (4 + T0) ≤ 1000 / 4229 := by
    rw [div_le_iff₀ hden]; linarith
  have h2 : (1 - 2 * T0) / (3 * rhoB) ≤ 542 / 3687 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 3 * rhoB)]
    nlinarith [hT1, hr1]
  linarith [h1, h2, hT1]

/-- **`(0,0)` tail** (`m ≥ 3`): fold-zero and the linear term is negative. -/
theorem e2_tail_00 (m : ℕ) (hm3 : 3 ≤ m) :
    -T0 / (((m : ℝ) + 1) * rhoB)
      + (11 / 50) * max 0 (1 / (((m : ℝ) + 1) + (m : ℝ) * T0) - T0) ≤ 0 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hmT : (m : ℝ) * (229 / 1000) ≤ (m : ℝ) * T0 :=
    mul_le_mul_of_nonneg_left hT1.le (by linarith)
  have hDpos : (0 : ℝ) < ((m : ℝ) + 1) + (m : ℝ) * T0 := by nlinarith [hmT]
  have hfz : max 0 (1 / (((m : ℝ) + 1) + (m : ℝ) * T0) - T0) = 0 := by
    apply fold_zero
    rw [div_le_iff₀ hDpos]
    nlinarith [hmT]
  rw [hfz, mul_zero, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (mul_pos (by linarith : (0 : ℝ) < (m : ℝ) + 1) rhoB_pos).le

/-- **`(1,0)` tail** (`m ≥ 2`): fold-zero and `J = 1/3 − 2T0 < 0`. -/
theorem e2_tail_10 (m : ℕ) (hm2 : 2 ≤ m) :
    (1 / 3 - 2 * T0) / (((m : ℝ) + 2) * rhoB)
      + (11 / 50) * max 0 (1 / (((m : ℝ) + 7 / 3) + (m : ℝ) * T0) - T0) ≤ 0 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmT : (m : ℝ) * (229 / 1000) ≤ (m : ℝ) * T0 :=
    mul_le_mul_of_nonneg_left hT1.le (by linarith)
  have hDpos : (0 : ℝ) < ((m : ℝ) + 7 / 3) + (m : ℝ) * T0 := by nlinarith [hmT]
  have hfz : max 0 (1 / (((m : ℝ) + 7 / 3) + (m : ℝ) * T0) - T0) = 0 := by
    apply fold_zero
    rw [div_le_iff₀ hDpos]
    nlinarith [hmT]
  rw [hfz, mul_zero, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (mul_pos (by linarith : (0 : ℝ) < (m : ℝ) + 2) rhoB_pos).le

/-- **`(2,0)` tail** (all `m ≥ 1`): fold-zero and `J = 2/3 − 3T0 < 0`. -/
theorem e2_tail_20 (m : ℕ) (hm : 1 ≤ m) :
    (2 / 3 - 3 * T0) / (((m : ℝ) + 3) * rhoB)
      + (11 / 50) * max 0 (1 / (((m : ℝ) + 11 / 3) + (m : ℝ) * T0) - T0) ≤ 0 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmT : (m : ℝ) * (229 / 1000) ≤ (m : ℝ) * T0 :=
    mul_le_mul_of_nonneg_left hT1.le (by linarith)
  have hDpos : (0 : ℝ) < ((m : ℝ) + 11 / 3) + (m : ℝ) * T0 := by nlinarith [hmT]
  have hfz : max 0 (1 / (((m : ℝ) + 11 / 3) + (m : ℝ) * T0) - T0) = 0 := by
    apply fold_zero
    rw [div_le_iff₀ hDpos]
    nlinarith [hmT]
  rw [hfz, mul_zero, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (mul_pos (by linarith : (0 : ℝ) < (m : ℝ) + 3) rhoB_pos).le

/-- **`(0,1)` tail** (`m ≥ 2`): fold-zero and `J = 1 − 2T0` fits inside the leaf budget. -/
theorem e2_tail_01 (m : ℕ) (hm2 : 2 ≤ m) :
    (1 - 2 * T0) / (((m : ℝ) + 2) * rhoB)
      + (11 / 50) * max 0 (1 / (((m : ℝ) + 3) + (m : ℝ) * T0) - T0) ≤ 229 / 1229 := by
  have hT1 := T0_gt_229; have hT2 := T0_lt_23
  have hr1 := rhoB_gt_1229
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmT : (m : ℝ) * (229 / 1000) ≤ (m : ℝ) * T0 :=
    mul_le_mul_of_nonneg_left hT1.le (by linarith)
  have hDpos : (0 : ℝ) < ((m : ℝ) + 3) + (m : ℝ) * T0 := by nlinarith [hmT]
  have hfz : max 0 (1 / (((m : ℝ) + 3) + (m : ℝ) * T0) - T0) = 0 := by
    apply fold_zero
    rw [div_le_iff₀ hDpos]
    nlinarith [hmT]
  rw [hfz, mul_zero, add_zero]
  rw [div_le_iff₀ (mul_pos (by linarith : (0 : ℝ) < (m : ℝ) + 2) rhoB_pos)]
  -- `1 − 2T0 ≤ (229/1229)·(m+2)·ρ`: LHS ≤ 542/1000, RHS ≥ (229/1229)·4·(1229/1000) = 916/1000
  nlinarith [hT1, hr1, mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2)
    (by linarith : (0 : ℝ) ≤ rhoB - 1229 / 1000)]

/-- **`E2Bound` holds.** -/
theorem e2Bound_holds : E2Bound := by
  intro a nl m hm
  by_cases h10 : 10 ≤ 4 * a + 6 * nl
  · exact e2_main a nl m hm h10
  have hcase : (a = 0 ∧ nl = 0) ∨ (a = 1 ∧ nl = 0) ∨ (a = 2 ∧ nl = 0) ∨ (a = 0 ∧ nl = 1) := by
    omega
  rcases hcase with ⟨ha, hn⟩ | ⟨ha, hn⟩ | ⟨ha, hn⟩ | ⟨ha, hn⟩
  · -- (0,0)
    subst ha; subst hn
    rw [starLHS_kink]
    rw [show (((0 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) - T0 * (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + 1))
          / ((((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + (m : ℝ) + 1) * rhoB)
        = -T0 / (((m : ℝ) + 1) * rhoB) from by push_cast; ring,
      show ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + (m : ℝ) + 1 + (((0 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ))
        = (m : ℝ) + 1 from by push_cast; ring,
      show ((0 : ℕ) : ℝ) * (-omegaVal) + ((0 : ℕ) : ℝ) * Lval = 0 from by push_cast; ring]
    rcases (by omega : m = 1 ∨ m = 2 ∨ 3 ≤ m) with h | h | h
    · subst h
      rw [show (((1 : ℕ) : ℝ) + 1) * rhoB = 2 * rhoB from by push_cast; ring,
        show ((1 : ℕ) : ℝ) + 1 + ((1 : ℕ) : ℝ) * T0 = 2 + T0 from by push_cast; ring]
      exact e2_case_001
    · subst h
      rw [show (((2 : ℕ) : ℝ) + 1) * rhoB = 3 * rhoB from by push_cast; ring,
        show ((2 : ℕ) : ℝ) + 1 + ((2 : ℕ) : ℝ) * T0 = 3 + 2 * T0 from by push_cast; ring]
      exact e2_case_002
    · exact e2_tail_00 m h
  · -- (1,0)
    subst ha; subst hn
    rw [starLHS_kink]
    rw [show (((1 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) - T0 * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + 1))
          / ((((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + (m : ℝ) + 1) * rhoB)
        = (1 / 3 - 2 * T0) / (((m : ℝ) + 2) * rhoB) from by push_cast; ring,
      show ((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + (m : ℝ) + 1 + (((1 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ))
        = (m : ℝ) + 7 / 3 from by push_cast; ring,
      show ((1 : ℕ) : ℝ) * (-omegaVal) + ((0 : ℕ) : ℝ) * Lval = -omegaVal from by push_cast; ring]
    have hb : (0 : ℝ) ≤ -omegaVal := le_trans (by norm_num) neg_omega_ge_const
    rcases (by omega : m = 1 ∨ 2 ≤ m) with h | h
    · subst h
      rw [show (((1 : ℕ) : ℝ) + 2) * rhoB = 3 * rhoB from by push_cast; ring,
        show ((1 : ℕ) : ℝ) + 7 / 3 + ((1 : ℕ) : ℝ) * T0 = 10 / 3 + T0 from by push_cast; ring]
      linarith [e2_case_101]
    · linarith [e2_tail_10 m h]
  · -- (2,0)
    subst ha; subst hn
    rw [starLHS_kink]
    rw [show (((2 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ) - T0 * (((2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + 1))
          / ((((2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + (m : ℝ) + 1) * rhoB)
        = (2 / 3 - 3 * T0) / (((m : ℝ) + 3) * rhoB) from by push_cast; ring,
      show ((2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + (m : ℝ) + 1 + (((2 : ℕ) : ℝ) / 3 + ((0 : ℕ) : ℝ))
        = (m : ℝ) + 11 / 3 from by push_cast; ring,
      show ((2 : ℕ) : ℝ) * (-omegaVal) + ((0 : ℕ) : ℝ) * Lval = 2 * (-omegaVal)
        from by push_cast; ring]
    have hb : (0 : ℝ) ≤ 2 * (-omegaVal) := by
      have := neg_omega_ge_const; linarith
    linarith [e2_tail_20 m hm]
  · -- (0,1)
    subst ha; subst hn
    rw [starLHS_kink]
    rw [show (((0 : ℕ) : ℝ) / 3 + ((1 : ℕ) : ℝ) - T0 * (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + 1))
          / ((((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + (m : ℝ) + 1) * rhoB)
        = (1 - 2 * T0) / (((m : ℝ) + 2) * rhoB) from by push_cast; ring,
      show ((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + (m : ℝ) + 1 + (((0 : ℕ) : ℝ) / 3 + ((1 : ℕ) : ℝ))
        = (m : ℝ) + 3 from by push_cast; ring,
      show ((0 : ℕ) : ℝ) * (-omegaVal) + ((1 : ℕ) : ℝ) * Lval = Lval from by push_cast; ring]
    rcases (by omega : m = 1 ∨ 2 ≤ m) with h | h
    · subst h
      rw [show (((1 : ℕ) : ℝ) + 2) * rhoB = 3 * rhoB from by push_cast; ring,
        show ((1 : ℕ) : ℝ) + 3 + ((1 : ℕ) : ℝ) * T0 = 4 + T0 from by push_cast; ring]
      linarith [e2_case_011, Lval_ge_const]
    · linarith [e2_tail_01 m h, Lval_ge_const]

end R3Cert
