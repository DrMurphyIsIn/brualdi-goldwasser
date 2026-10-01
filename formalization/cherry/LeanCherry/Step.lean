/-
LeanCherry.Step -- the pooled Bellman inequality at lam_c (one vertex with k leaf children and m non-leaf children,
whose non-leaf messages have mean t in [0, 1/2]):

  -k L + m U(t) + log(1 + lam (k + m t)/(k+m+1)) - L  <=  U(1/(k+m+1 + lam (k + m t))).

Everything is derivative-free: tangent bounds for log (log a <= log b + (a-b)/b), a chord bound for 1/s, and the
numerics of LeanCherry.Basic.
-/
import LeanCherry.Basic

open Real

namespace LeanCherry

noncomputable section

lemma log_le_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log a ≤ Real.log b + (a - b) / b := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have : a / b - 1 = (a - b) / b := by field_simp
  linarith

lemma U_le_zero (y : ℝ) : U y ≤ 0 := min_le_left _ _
lemma U_of_le {y : ℝ} (h : y ≤ ych) : U y = 0 := by
  unfold U; apply min_eq_left; exact mul_nonneg kap_pos.le (by linarith)
lemma U_of_ge {y : ℝ} (h : ych ≤ y) : U y = kap * (ych - y) := by
  unfold U; apply min_eq_right; exact mul_nonpos_of_nonneg_of_nonpos kap_pos.le (by linarith)
lemma le_U_iff {x y : ℝ} : x ≤ U y ↔ x ≤ 0 ∧ x ≤ kap * (ych - y) := le_min_iff

lemma φ3_eq : φ ^ 3 = 2 * φ + 1 := by nlinarith [φ_sq]

lemma kap_lo : (0.763 : ℝ) < kap := by
  have h1 := two_div_φ_cube_lt_L; have h2 := φ_bounds
  have hφ3 : φ ^ 3 < 4.2362 := by rw [φ3_eq]; linarith
  have hL : (0.4721 : ℝ) < L := by
    have : 2 / (4.2362:ℝ) < 2 / φ ^ 3 := by
      apply div_lt_div_of_pos_left (by norm_num) (by have := φ_pos; positivity) hφ3
    linarith [show (0.4721:ℝ) < 2 / 4.2362 by norm_num]
  unfold kap; nlinarith [L_pos]
lemma kap_hi : kap < 0.8091 := by
  unfold kap; have := φ_bounds.2; have := L_lt_half; have := L_pos; nlinarith
lemma kap_lt_one : kap < 1 := by linarith [kap_hi]

lemma log_φ_sq : Real.log (φ ^ 2) = 2 * L := by unfold L; rw [Real.log_pow]; norm_num
lemma log_φ_cube : Real.log (φ ^ 3) = 3 * L := by unfold L; rw [Real.log_pow]; norm_num
lemma ych_eq' : ych = 1 / (2 * (φ + 1)) := by unfold ych; rw [φ_sq]

/-- the kink constant C_m := (m phi + 1)/((m+1) phi) - 1 + kap (1/(m phi + 1) - y_ch) is <= 0 for every m >= 1 -/
lemma Cm_nonpos (m : ℝ) (hm : 1 ≤ m) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) :
    (m * φ + 1) / ((m + 1) * φ) - 1 + kap * (1 / (m * φ + 1) - ych) ≤ 0 := by
  have hp := φ_pos; have hk := kap_pos
  rw [ych_eq']
  have hq : (1 - φ) / φ = -1 / (φ + 1) := by
    rw [div_eq_div_iff hp.ne' (by positivity)]; linear_combination (-1 : ℝ) * φ_sq
  rcases hcase with h | h | h
  · subst h
    have e : (1 * φ + 1) / ((1 + 1) * φ) - 1 + kap * (1 / (1 * φ + 1) - 1 / (2 * (φ + 1)))
        = (1 / 2) * ((1 - φ) / φ) + kap / (2 * (φ + 1)) := by field_simp; ring
    rw [e, hq]
    have : (1 / 2) * (-1 / (φ + 1)) + kap / (2 * (φ + 1)) = (kap - 1) / (2 * (φ + 1)) := by field_simp; ring
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [kap_lt_one]) (by positivity)
  · subst h
    have e : (2 * φ + 1) / ((2 + 1) * φ) - 1 + kap * (1 / (2 * φ + 1) - 1 / (2 * (φ + 1)))
        = (1 / 3) * ((1 - φ) / φ) + kap / (2 * (φ + 1) * (2 * φ + 1)) := by field_simp; ring
    rw [e, hq]
    have : (1 / 3) * (-1 / (φ + 1)) + kap / (2 * (φ + 1) * (2 * φ + 1))
        = (3 * kap - 2 * (2 * φ + 1)) / (6 * (φ + 1) * (2 * φ + 1)) := by field_simp; ring
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [kap_lt_one, φ_gt_one]) (by positivity)
  · have hA : (m * φ + 1) / ((m + 1) * φ) - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one (by positivity)]; nlinarith [φ_gt_one]
    have hB : 1 / (m * φ + 1) - 1 / (2 * (φ + 1)) ≤ 0 := by
      rw [sub_nonpos, one_div_le_one_div (by positivity) (by positivity)]; nlinarith [φ_gt_one]
    nlinarith [kap_pos]

/-- the k >= 1 cases -/
lemma step_k_pos (k m t : ℝ) (hk : 1 ≤ k) (hm : 0 ≤ m) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hk12 : k = 1 ∨ 2 ≤ k) :
    -k * L + m * U t + Real.log (1 + lam * (k + m * t) / (k + m + 1)) - L
      ≤ U (1 / (k + m + 1 + lam * (k + m * t))) := by
  have hl := lam_pos; have hL := L_pos
  have hd : 0 < k + m + 1 := by linarith
  have hmt : 0 ≤ m * t := mul_nonneg hm ht0
  have hR0 : 0 ≤ lam * (k + m * t) := mul_nonneg hl.le (by linarith)
  -- U(y_v) = 0
  have hyv : 1 / (k + m + 1 + lam * (k + m * t)) ≤ ych := by
    rw [ych_eq, one_div_le_one_div (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hk hl.le, mul_nonneg hl.le hmt]
  rw [U_of_le hyv]
  have hmU : m * U t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm (U_le_zero t)
  have hpos : 0 < 1 + lam * (k + m * t) / (k + m + 1) := by
    have := div_nonneg hR0 hd.le; linarith
  rcases hk12 with h | h
  · subst h
    have hR : lam * (1 + m * t) / (1 + m + 1) ≤ lam / 2 := by
      rw [div_le_div_iff₀ hd (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left ht1 (mul_nonneg hl.le hm)]
    have : Real.log (1 + lam * (1 + m * t) / (1 + m + 1)) ≤ 2 * L := by
      rw [← log_φ_sq, ← one_add_half_lam]
      exact Real.log_le_log hpos (by linarith)
    linarith
  · have hR : lam * (k + m * t) / (k + m + 1) ≤ lam := by
      rw [div_le_iff₀ hd]
      nlinarith [mul_le_mul_of_nonneg_left ht1 (mul_nonneg hl.le hm), mul_nonneg hl.le hm]
    have hlog : Real.log (1 + lam * (k + m * t) / (k + m + 1)) ≤ 3 * L := by
      rw [← log_φ_cube, ← one_add_lam]
      exact Real.log_le_log hpos (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h hL.le]

end

end LeanCherry
