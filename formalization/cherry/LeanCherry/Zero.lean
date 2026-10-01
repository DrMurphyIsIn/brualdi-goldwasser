/-
LeanCherry.Zero -- the k = 0 case of the pooled Bellman inequality at lam_c (all m >= 1 children non-leaf,
mean message t in [0, 1/2]):

  m U(t) + log(1 + lam (m t)/(m+1)) - L  <=  U(1/(m+1 + lam (m t))).

Notation: D = m+1 + lam (m t) (the parent's 1/message), Dy = m phi + 1 = m+1 + lam (m ych) (its value at t = ych).
Derivative-free: tangent bound for log at D = Dy, the kink constant C_m <= 0, and for m = 1 in region A a convex
quadratic checked at the endpoints of [0.19, 1/2].
-/
import LeanCherry.Step

open Real

namespace LeanCherry

noncomputable section

lemma ych_bounds : (0.19098 : ℝ) < ych ∧ ych < 0.190986 := by
  rw [ych_eq']
  obtain ⟨h1, h2⟩ := φ_bounds
  constructor
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

lemma Dy_eq (m : ℝ) : m * φ + 1 = m + 1 + lam * (m * ych) := by
  linear_combination (-m) * lam_ych'

lemma invφ_eq : 1 / φ = φ - 1 := by
  rw [div_eq_iff φ_pos.ne']; linear_combination (-1 : ℝ) * φ_sq

/-- (*) tangent bound: log(1 + lam (m t)/(m+1)) - L <= C0 + (D - Dy)/Dy -/
lemma star_bound (m t : ℝ) (hm : 1 ≤ m) (ht0 : 0 ≤ t) :
    Real.log (1 + lam * (m * t) / (m + 1)) - L
      ≤ ((m * φ + 1) / ((m + 1) * φ) - 1) + ((m + 1 + lam * (m * t)) - (m * φ + 1)) / (m * φ + 1) := by
  have hp := φ_pos; have hl := lam_pos
  have hm1 : 0 < m + 1 := by linarith
  have hD : 0 < m + 1 + lam * (m * t) := by
    have : 0 ≤ lam * (m * t) := mul_nonneg hl.le (mul_nonneg (by linarith) ht0); linarith
  have hDy : 0 < m * φ + 1 := by nlinarith
  have e1 : 1 + lam * (m * t) / (m + 1) = (m + 1 + lam * (m * t)) / (m + 1) := by field_simp
  rw [e1]
  have htan := log_le_tangent (div_pos hD hm1) (div_pos hDy hm1)
  have e2 : ((m + 1 + lam * (m * t)) / (m + 1) - (m * φ + 1) / (m + 1)) / ((m * φ + 1) / (m + 1))
      = ((m + 1 + lam * (m * t)) - (m * φ + 1)) / (m * φ + 1) := by field_simp
  rw [e2] at htan
  have hlb : Real.log ((m * φ + 1) / (m + 1)) - L ≤ (m * φ + 1) / ((m + 1) * φ) - 1 := by
    unfold L
    rw [← Real.log_div (div_pos hDy hm1).ne' hp.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos (div_pos hDy hm1) hp)
    have e : (m * φ + 1) / (m + 1) / φ = (m * φ + 1) / ((m + 1) * φ) := by field_simp
    rw [e] at h ⊢; exact h
  linarith

lemma C0_nonpos (m : ℝ) (hm : 1 ≤ m) : (m * φ + 1) / ((m + 1) * φ) - 1 ≤ 0 := by
  have hp := φ_pos; have hp1 := φ_gt_one
  rw [sub_nonpos, div_le_one (by positivity)]; nlinarith

/-- generic algebra: (D - Dy)/Dy + k (1/D - 1/Dy) = (D - Dy)(D - k)/(D Dy) -/
lemma region_alg (D Dy k : ℝ) (hD : 0 < D) (hDy : 0 < Dy) :
    (D - Dy) / Dy + k * (1 / D - 1 / Dy) = (D - Dy) * (D - k) / (D * Dy) := by
  field_simp; ring

/-- region B: t <= ych -/
lemma zero_regionB (m t : ℝ) (hm : 1 ≤ m) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) (ht0 : 0 ≤ t)
    (hty : t ≤ ych) :
    Real.log (1 + lam * (m * t) / (m + 1)) - L ≤ U (1 / (m + 1 + lam * (m * t))) := by
  have hp := φ_pos; have hl := lam_pos; have hk := kap_pos; have hk1 := kap_lt_one
  have hDy : 0 < m * φ + 1 := by nlinarith
  have hmt : 0 ≤ lam * (m * t) := mul_nonneg hl.le (mul_nonneg (by linarith) ht0)
  have hD : 0 < m + 1 + lam * (m * t) := by linarith
  have hD2 : 2 ≤ m + 1 + lam * (m * t) := by linarith
  have hDle : (m + 1 + lam * (m * t)) - (m * φ + 1) ≤ 0 := by
    rw [Dy_eq m]
    have : lam * (m * t) ≤ lam * (m * ych) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hty (by linarith)) hl.le
    linarith
  have hstar := star_bound m t hm ht0
  have hC0 := C0_nonpos m hm
  have hCm := Cm_nonpos m hm hcase
  rw [le_U_iff]
  constructor
  · have : ((m + 1 + lam * (m * t)) - (m * φ + 1)) / (m * φ + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hDle hDy.le
    linarith
  · -- C0 + (D-Dy)/Dy + kap(1/D - ych) = [C0 + kap(1/Dy - ych)] + [(D-Dy)/Dy + kap(1/D - 1/Dy)]
    have halg := region_alg (m + 1 + lam * (m * t)) (m * φ + 1) kap hD hDy
    have hneg : ((m + 1 + lam * (m * t)) - (m * φ + 1)) * ((m + 1 + lam * (m * t)) - kap)
        / ((m + 1 + lam * (m * t)) * (m * φ + 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hDle (by linarith))
        (by positivity)
    have e : kap * (ych - 1 / (m + 1 + lam * (m * t)))
        = - (kap * (1 / (m * φ + 1) - ych)) - kap * (1 / (m + 1 + lam * (m * t)) - 1 / (m * φ + 1)) := by ring
    rw [e]
    linarith

/-- region A, m >= 2 -/
lemma zero_regionA_ge2 (m t : ℝ) (hm : 2 ≤ m) (hcase : m = 2 ∨ 3 ≤ m) (hty : ych ≤ t) :
    m * (kap * (ych - t)) + Real.log (1 + lam * (m * t) / (m + 1)) - L
      ≤ U (1 / (m + 1 + lam * (m * t))) := by
  have hp := φ_pos; have hl := lam_pos; have hk := kap_pos; have hy := ych_pos
  have ht0 : 0 ≤ t := by linarith
  have hDy : 0 < m * φ + 1 := by nlinarith
  have hDdiff : (m + 1 + lam * (m * t)) - (m * φ + 1) = lam * m * (t - ych) := by
    rw [Dy_eq m]; ring
  have hD : 0 < m + 1 + lam * (m * t) := by
    have : 0 ≤ lam * (m * t) := mul_nonneg hl.le (mul_nonneg (by linarith) ht0); linarith
  have hstar := star_bound m t (by linarith) ht0
  have hC0 := C0_nonpos m (by linarith)
  have hCm := Cm_nonpos m (by linarith) (by rcases hcase with h | h <;> [exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)])
  -- slope: lam/(m phi + 1) <= lam/(2 phi + 1) = 2/phi^2 < kap
  have hslope : lam / (m * φ + 1) < kap := by
    have h1 : lam / (m * φ + 1) ≤ lam / (2 * φ + 1) :=
      div_le_div_of_nonneg_left hl.le (by positivity) (by nlinarith)
    have h2 : lam / (2 * φ + 1) = 2 / φ ^ 2 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; unfold lam; nlinarith [φ_sq]
    linarith [two_div_φ_sq_lt_kap]
  have hX : 0 ≤ m * (t - ych) := mul_nonneg (by linarith) (by linarith)
  have hterm : ((m + 1 + lam * (m * t)) - (m * φ + 1)) / (m * φ + 1) ≤ kap * (m * (t - ych)) := by
    rw [hDdiff]
    have : lam * m * (t - ych) / (m * φ + 1) = (lam / (m * φ + 1)) * (m * (t - ych)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hslope.le hX
  have hDDy : 1 / (m + 1 + lam * (m * t)) ≤ 1 / (m * φ + 1) := by
    rw [one_div_le_one_div hD hDy]
    have : 0 ≤ lam * m * (t - ych) := mul_nonneg (mul_nonneg hl.le (by linarith)) (by linarith)
    linarith [hDdiff]
  rw [le_U_iff]
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hDDy hk.le]

/-- the m = 1 region-A quadratic: for t in [0.19, 1/2], kap (1/D - t) + t + phi - 2 <= 0 with D = 2 + 2 phi t -/
lemma m1_quad (t : ℝ) (ht0 : 0.19 ≤ t) (ht1 : t ≤ 1 / 2) :
    kap * (1 / (2 + 2 * φ * t) - t) + t + φ - 2 ≤ 0 := by
  obtain ⟨p1, p2⟩ := φ_bounds
  have hk0 := kap_lo; have hk1 := kap_hi
  have hD : 0 < 2 + 2 * φ * t := by nlinarith
  -- multiply through by D: g(t) := kap (1 - t D) + (t + phi - 2) D <= 0
  have e : kap * (1 / (2 + 2 * φ * t) - t) + t + φ - 2
      = (kap * (1 - t * (2 + 2 * φ * t)) + (t + φ - 2) * (2 + 2 * φ * t)) / (2 + 2 * φ * t) := by
    field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg _ hD.le
  -- g is a convex quadratic in t: 0.31 g(t) = (0.5 - t) g(0.19) + (t - 0.19) g(0.5) - 0.31 a (t-0.19)(0.5-t), a = 2 phi (1-kap)
  have g019 : kap * (1 - 0.19 * (2 + 2 * φ * 0.19)) + (0.19 + φ - 2) * (2 + 2 * φ * 0.19) ≤ 0 := by nlinarith
  have g05 : kap * (1 - 0.5 * (2 + 2 * φ * 0.5)) + (0.5 + φ - 2) * (2 + 2 * φ * 0.5) ≤ 0 := by nlinarith
  have hid : 0.31 * (kap * (1 - t * (2 + 2 * φ * t)) + (t + φ - 2) * (2 + 2 * φ * t))
      = (0.5 - t) * (kap * (1 - 0.19 * (2 + 2 * φ * 0.19)) + (0.19 + φ - 2) * (2 + 2 * φ * 0.19))
        + (t - 0.19) * (kap * (1 - 0.5 * (2 + 2 * φ * 0.5)) + (0.5 + φ - 2) * (2 + 2 * φ * 0.5))
        - 0.31 * (2 * φ * (1 - kap)) * ((t - 0.19) * (0.5 - t)) := by ring
  have hA : 0 ≤ 2 * φ * (1 - kap) := by nlinarith
  have hB : 0 ≤ (t - 0.19) * (0.5 - t) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 0.5 - t) g019,
    mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ t - 0.19) g05, mul_nonneg hA hB]

/-- region A, m = 1 -/
lemma zero_regionA_one (t : ℝ) (hty : ych ≤ t) (ht1 : t ≤ 1 / 2) :
    1 * (kap * (ych - t)) + Real.log (1 + lam * (1 * t) / (1 + 1)) - L
      ≤ U (1 / (1 + 1 + lam * (1 * t))) := by
  have hp := φ_pos; have hk := kap_pos; have hk1 := kap_lt_one
  obtain ⟨y1, y2⟩ := ych_bounds
  have ht0 : 0 ≤ t := by linarith
  have ha : 0 < 1 + lam * (1 * t) / (1 + 1) := by
    unfold lam; have : 0 ≤ 2 * φ * (1 * t) / (1 + 1) := by positivity
    linarith
  -- log(a) - L = log(a/phi) <= a/phi - 1 = t + phi - 2
  have hla : Real.log (1 + lam * (1 * t) / (1 + 1)) - L ≤ t + φ - 2 := by
    unfold L
    rw [← Real.log_div ha.ne' hp.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos ha hp)
    have e : (1 + lam * (1 * t) / (1 + 1)) / φ = t + 1 / φ := by unfold lam; field_simp; ring
    rw [e, invφ_eq] at h ⊢
    linarith
  have hDe : 1 + 1 + lam * (1 * t) = 2 + 2 * φ * t := by unfold lam; ring
  rw [le_U_iff, hDe]
  constructor
  · -- linear in t with slope 1 - kap > 0: worst at t = 1/2
    have h1 : kap * (ych - t) + t ≤ kap * (ych - 1 / 2) + 1 / 2 := by nlinarith
    have hy' : ych - 1 / 2 ≤ -0.309 := by linarith
    have h2 : kap * (ych - 1 / 2) ≤ kap * (-0.309) := mul_le_mul_of_nonneg_left hy' hk.le
    have := φ_bounds.2; have := kap_lo
    linarith
  · have hq := m1_quad t (by linarith) ht1
    nlinarith

/-- the k = 0 case -/
theorem step_k_zero (m t : ℝ) (hm : 1 ≤ m) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 2) :
    m * U t + Real.log (1 + lam * (m * t) / (m + 1)) - L ≤ U (1 / (m + 1 + lam * (m * t))) := by
  rcases le_total t ych with hty | hty
  · rw [U_of_le hty, mul_zero, zero_add]
    exact zero_regionB m t hm hcase ht0 hty
  · rw [U_of_ge hty]
    rcases hcase with h | h | h
    · subst h; exact zero_regionA_one t hty ht1
    · exact zero_regionA_ge2 m t (by linarith) (Or.inl h) hty
    · exact zero_regionA_ge2 m t (by linarith) (Or.inr h) hty

end

end LeanCherry
