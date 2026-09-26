/-
  R3Cert.BGHighDegreeSmall -- the high-degree case for small trees, against the exact table spider.

  `BGSpiderReduction.phiRoot_le_of_armEnv` (with the proved cell cores of `BGSpiderCells`) bounds a
  root with `k ≥ 24` children, one of them a non-atom, by `phiRoot ≤ log(26/23) − 1/75`, for EVERY
  size.  The earlier high-degree theorem needed `n − 1 ≥ 90` only to build its comparison spider.
  Here the comparison spider is the exact table spider `tab n` (`BGSpiderTable`), whose value clears
  the bound at every `25 ≤ n ≤ 90` by the kernel check `highOK`:
      (F · 23/26)^11 · 86 > 75 · (621/64)^(n−1),  F = F (tab n),
  which suffices since `exp (−11/75) ≤ 75/86`.
  Result (`highDegree_small`): a maximum-degree rooting with `k ≥ 24` and a non-atom child, on
  `25 ≤ n ≤ 90` vertices, has `Aobj` strictly below the table spider.
  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGSpiderCells
import R3Cert.BGMaximizerMid

namespace R3Cert
namespace BGHighDegreeSmall

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL R3Cert.BGSpiderOpt R3Cert.BGSpiderRule R3Cert.BGSpiderTable

/-- The proved high-degree envelope bound. -/
theorem phiRoot_high (cs : List BGSCL.Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c) :
    phiRoot cs ≤ Real.log (26 / 23) - 1 / 75 :=
  phiRoot_le_of_armEnv
    (armEnv_of_cells (atomCell0_of_core atomCell0Core_proved)
      (surchargeCell_of_core (by norm_num) surchargeCore_proved) (atomCellMu_of_core atomCellMuCore_proved))
    cs hk hna

/-- The per-`n` integer check. -/
def highOK (n : ℕ) : Bool :=
  Nat.blt (75 * 621 ^ (n - 1) * ((tabV n).2 ^ 11 * 26 ^ 11))
    ((tabV n).1 ^ 11 * 23 ^ 11 * 86 * 64 ^ (n - 1))

theorem highOK_all : (List.range' 25 66).all highOK = true := by decide +kernel

theorem tabV_pos (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 491) : 0 < (tabV n).2 ∧ 0 < (tabV n).1 := by
  have hc := checkN_all n h4 hN
  simp only [checkN, Bool.and_eq_true] at hc
  have hpos : 0 < (row n).1 + (row n).2.2.1 + (row n).2.2.2 := Nat.blt_eq.mp hc.1.1.2
  refine ⟨fden_pos _ _ _ _ hpos, ?_⟩
  simp only [tabV, fnum]; positivity

/-- `F (tab n)` from the table values. -/
theorem F_tab (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 491) :
    (F (tab n) : ℝ) = ((tabV n).1 : ℝ) / (tabV n).2 := by
  have hc := checkN_all n h4 hN
  simp only [checkN, Bool.and_eq_true] at hc
  have hpos : 0 < (row n).1 + (row n).2.2.1 + (row n).2.2.2 := Nat.blt_eq.mp hc.1.1.2
  rw [tab, F_canon_eq _ _ _ _ hpos]; push_cast; rfl

/-- **The high-degree case for `25 ≤ n ≤ 90`.** -/
theorem highDegree_small (cs : List BGSCL.Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (n : ℕ) (hn : bsizeList cs + 1 = n) (h25 : 25 ≤ n) (h90 : n ≤ 90) :
    piRoot cs < (F (tab n) : ℝ) := by
  have hb := phiRoot_high cs hk hna
  have hc : highOK n = true := by
    have := List.all_eq_true.mp highOK_all n (List.mem_range'_1.mpr ⟨h25, by omega⟩)
    exact this
  have hlt := Nat.blt_eq.mp hc
  obtain ⟨hden, hnum⟩ := tabV_pos n (by omega) (by omega)
  set p := ((tabV n).1 : ℝ)
  set q := ((tabV n).2 : ℝ)
  have hp : 0 < p := Nat.cast_pos.mpr hnum
  have hq : 0 < q := Nat.cast_pos.mpr hden
  have hF : (F (tab n) : ℝ) = p / q := F_tab n (by omega) (by omega)
  have hFpos : 0 < p / q := div_pos hp hq
  -- the rational inequality in ℝ: (p/q · 23/26)^11 · 86/75 > (621/64)^(n-1)
  have hineq : ((621 : ℝ) / 64) ^ (n - 1) < (p / q * (23 / 26)) ^ 11 * (86 / 75) := by
    have hlt' : (75 * 621 ^ (n - 1) * ((tabV n).2 ^ 11 * 26 ^ 11) : ℝ)
        < ((tabV n).1 ^ 11 * 23 ^ 11 * 86 * 64 ^ (n - 1) : ℝ) := by exact_mod_cast hlt
    rw [div_pow, mul_pow, div_pow, div_pow]
    rw [div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith [hlt']
  -- logs, in one linear form
  have hlog86 : Real.log (86 / 75) ≤ 11 / 75 := by
    have := Real.add_one_le_exp (11 / 75 : ℝ)
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  set X := ((n - 1 : ℕ) : ℝ) * Real.log (621 / 64) with hX
  have e1 : Real.log (((621 : ℝ) / 64) ^ (n - 1)) = X := by rw [Real.log_pow]
  have e2 : Real.log ((p / q * (23 / 26)) ^ 11 * (86 / 75))
      = 11 * (Real.log (p / q) + Real.log (23 / 26)) + Real.log (86 / 75) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
      Real.log_mul hFpos.ne' (by norm_num)]
    push_cast; ring
  have e3 : Real.log (26 / 23) = - Real.log (23 / 26) := by
    rw [show (26 : ℝ) / 23 = (23 / 26)⁻¹ by norm_num, Real.log_inv]
  have hL := Real.log_lt_log (by positivity) hineq
  rw [e1, e2] at hL
  have hphi : phiRoot cs = Real.log (piRoot cs) - (bsizeList cs : ℝ) * FSTAR := rfl
  have hsz : (bsizeList cs : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [← hn]; simp
  rw [hphi, hsz, FSTAR] at hb
  have hb' : Real.log (piRoot cs) ≤ X / 11 + Real.log (26 / 23) - 1 / 75 := by
    have h := hb
    rw [show ((n - 1 : ℕ) : ℝ) * (Real.log (621 / 64) / 11) = X / 11 by rw [hX]; ring] at h
    linarith
  have hpos := piRoot_pos cs
  rw [hF, ← Real.log_lt_log_iff hpos hFpos]
  linarith [hL, hb', hlog86, e3]

end BGHighDegreeSmall
end R3Cert
