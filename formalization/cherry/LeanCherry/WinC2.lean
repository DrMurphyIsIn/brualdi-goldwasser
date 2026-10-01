/-
LeanCherry.WinC2 -- the window, part 3: the inequality (C2) by hand, uniformly on the window.

(C2) is the reduced Bellman inequality for roots with no exempt child (k = 0) and 1 <= m <= 7 children,
   log(1 + l m ybar/(m+1)) - F0 + kap max(0, 1/D - y_ch) <= m kap max(0, ybar - y_ch),   D = m + 1 + l m ybar,
which an interval-arithmetic check would otherwise supply. Generic derivative-free lemmas prove it
under explicit hypotheses on the kink constants at ybar = y_ch (C0_m, C_m), the slope l/Dy <= kap (m >= 2) and the m = 1
endpoint values (with E = e^{-F0}); then these hypotheses are verified for every l in [3.22, 1 + sqrt 5) and 1 <= m <= 7.
-/
import LeanCherry.WinConst

open Real

namespace LeanCherry

noncomputable section

/-- an affine function nonpositive at both ends of an interval is nonpositive on it -/
lemma aff_nonpos {α β p q x : ℝ} (hp : α + β * p ≤ 0) (hq : α + β * q ≤ 0) (hx1 : p ≤ x) (hx2 : x ≤ q) :
    α + β * x ≤ 0 := by
  rcases le_total 0 β with h | h <;> nlinarith

/-- chord bound for the convex 1/D on [D1, D2] -/
lemma inv_chord {D D1 D2 : ℝ} (h1 : 0 < D1) (hD1 : D1 ≤ D) (hD2 : D ≤ D2) :
    1 / D ≤ 1 / D1 + 1 / D2 - D / (D1 * D2) := by
  have hD : 0 < D := by linarith
  have h2 : 0 < D2 := by linarith
  have e : 1 / D1 + 1 / D2 - D / (D1 * D2) - 1 / D = - ((D - D1) * (D - D2)) / (D * D1 * D2) := by
    field_simp; ring
  have : 0 ≤ - ((D - D1) * (D - D2)) / (D * D1 * D2) := by
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hD1) (sub_nonneg.2 hD2)]
  linarith

lemma log_frac (l m y : ℝ) (hm : 0 < m + 1) :
    Real.log (1 + l * m * y / (m + 1)) = Real.log ((m + 1 + l * m * y) / (m + 1)) := by
  congr 1; field_simp

/-- region B: ybar <= y_ch -/
lemma c2_regionB {l yc κ F0 m y : ℝ} (hl : 0 < l) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hm : 1 ≤ m) (hy0 : 0 ≤ y)
    (hyy : y ≤ yc)
    (hC0 : Real.log ((m + 1 + l * m * yc) / (m + 1)) ≤ F0)
    (hC : Real.log ((m + 1 + l * m * yc) / (m + 1)) - F0 + κ * (1 / (m + 1 + l * m * yc) - yc) ≤ 0) :
    Real.log (1 + l * m * y / (m + 1)) - F0 + κ * max 0 (1 / (m + 1 + l * m * y) - yc) ≤ m * κ * max 0 (y - yc) := by
  have hm1 : 0 < m + 1 := by linarith
  have hlmy : 0 ≤ l * m * y := by have : 0 ≤ m := by linarith
                                  positivity
  have hD : 2 ≤ m + 1 + l * m * y := by linarith
  have hDy0 : l * m * y ≤ l * m * yc := mul_le_mul_of_nonneg_left hyy (by nlinarith)
  have hDy : 2 ≤ m + 1 + l * m * yc := by linarith
  rw [max_eq_left (by linarith : y - yc ≤ 0), mul_zero, log_frac l m y hm1]
  have hlog : Real.log ((m + 1 + l * m * y) / (m + 1)) ≤ Real.log ((m + 1 + l * m * yc) / (m + 1)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hm1.le)
  rcases le_total (1 / (m + 1 + l * m * y) - yc) 0 with ha | ha
  · rw [max_eq_left ha]; linarith
  · rw [max_eq_right ha]
    have htan := log_le_tangent (by positivity : 0 < (m + 1 + l * m * y) / (m + 1))
      (by positivity : 0 < (m + 1 + l * m * yc) / (m + 1))
    have e : ((m + 1 + l * m * y) / (m + 1) - (m + 1 + l * m * yc) / (m + 1)) / ((m + 1 + l * m * yc) / (m + 1))
        = ((m + 1 + l * m * y) - (m + 1 + l * m * yc)) / (m + 1 + l * m * yc) := by
      field_simp
    rw [e] at htan
    set D := m + 1 + l * m * y
    set Dy := m + 1 + l * m * yc
    have halg : (D - Dy) / Dy + κ * (1 / D - 1 / Dy) = (D - Dy) * (D - κ) / (D * Dy) := by
      field_simp; ring
    have hneg : (D - Dy) * (D - κ) / (D * Dy) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) (by positivity)
    nlinarith

/-- region A, m >= 2 -/
lemma c2_regionA_ge2 {l yc κ F0 m y : ℝ} (hl : 0 < l) (hκ0 : 0 ≤ κ) (hm : 2 ≤ m) (hyc : 0 ≤ yc) (hyy : yc ≤ y)
    (hC0 : Real.log ((m + 1 + l * m * yc) / (m + 1)) ≤ F0)
    (hC : Real.log ((m + 1 + l * m * yc) / (m + 1)) - F0 + κ * (1 / (m + 1 + l * m * yc) - yc) ≤ 0)
    (hslope : l / (m + 1 + l * m * yc) ≤ κ) :
    Real.log (1 + l * m * y / (m + 1)) - F0 + κ * max 0 (1 / (m + 1 + l * m * y) - yc) ≤ m * κ * max 0 (y - yc) := by
  have hm1 : 0 < m + 1 := by linarith
  have hDy : 0 < m + 1 + l * m * yc := by have : 0 ≤ l * m * yc := by positivity
                                          linarith
  have hDD : l * m * yc ≤ l * m * y := mul_le_mul_of_nonneg_left hyy (by nlinarith)
  have hD : 0 < m + 1 + l * m * y := by linarith
  rw [max_eq_right (by linarith : 0 ≤ y - yc), log_frac l m y hm1]
  have htan := log_le_tangent (by positivity : 0 < (m + 1 + l * m * y) / (m + 1))
    (by positivity : 0 < (m + 1 + l * m * yc) / (m + 1))
  have e : ((m + 1 + l * m * y) / (m + 1) - (m + 1 + l * m * yc) / (m + 1)) / ((m + 1 + l * m * yc) / (m + 1))
      = (l / (m + 1 + l * m * yc)) * (m * (y - yc)) := by
    field_simp; ring
  rw [e] at htan
  have hsl : (l / (m + 1 + l * m * yc)) * (m * (y - yc)) ≤ κ * (m * (y - yc)) :=
    mul_le_mul_of_nonneg_right hslope (by nlinarith)
  have hmono : max 0 (1 / (m + 1 + l * m * y) - yc) ≤ max 0 (1 / (m + 1 + l * m * yc) - yc) := by
    apply max_le_max le_rfl
    have : 1 / (m + 1 + l * m * y) ≤ 1 / (m + 1 + l * m * yc) := one_div_le_one_div_of_le hDy (by linarith)
    linarith
  have hkm := mul_le_mul_of_nonneg_left hmono hκ0
  have hbase : Real.log ((m + 1 + l * m * yc) / (m + 1)) - F0 + κ * max 0 (1 / (m + 1 + l * m * yc) - yc) ≤ 0 := by
    rcases le_total (1 / (m + 1 + l * m * yc) - yc) 0 with ha | ha
    · rw [max_eq_left ha]; linarith
    · rw [max_eq_right ha]; exact hC
  nlinarith

/-- region A, m = 1, with E = e^{-F0} -/
lemma c2_regionA_one {l yc κ F0 y : ℝ} (hl : 0 < l) (hκ0 : 0 ≤ κ) (hyc : 0 < yc) (hyc2 : yc < 1 / 2)
    (hyy : yc ≤ y) (hy1 : y ≤ 1 / 2)
    (h0a : (1 + l * yc / 2) * Real.exp (-F0) - 1 ≤ 0)
    (h0b : (1 + l / 4) * Real.exp (-F0) - 1 ≤ κ * (1 / 2 - yc))
    (haa : (1 + l * yc / 2) * Real.exp (-F0) - 1 + κ * (1 / (2 + l * yc) - yc) ≤ 0)
    (hab : (1 + l / 4) * Real.exp (-F0) - 1 + κ * (1 / (2 + l / 2) - yc) - κ * (1 / 2 - yc) ≤ 0) :
    Real.log (1 + l * 1 * y / (1 + 1)) - F0 + κ * max 0 (1 / (1 + 1 + l * 1 * y) - yc) ≤ 1 * κ * max 0 (y - yc) := by
  set E := Real.exp (-F0) with hE
  have hE0 : 0 < E := Real.exp_pos _
  rw [max_eq_right (by linarith : 0 ≤ y - yc)]
  have hy0 : 0 ≤ y := by linarith
  have hx : 0 < 1 + l * 1 * y / (1 + 1) := by
    have : 0 ≤ l * 1 * y / (1 + 1) := div_nonneg (mul_nonneg (mul_nonneg hl.le (by norm_num)) hy0) (by norm_num)
    linarith
  -- log x - F0 = log(x E) <= x E - 1
  have hlog : Real.log (1 + l * 1 * y / (1 + 1)) - F0 ≤ (1 + l * y / 2) * E - 1 := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hx hE0)
    rw [Real.log_mul hx.ne' hE0.ne', hE, Real.log_exp] at h
    have e : 1 + l * 1 * y / (1 + 1) = 1 + l * y / 2 := by ring
    rw [e] at h ⊢; linarith
  rcases le_total (1 / (1 + 1 + l * 1 * y) - yc) 0 with ha | ha
  · rw [max_eq_left ha, mul_zero, add_zero]
    -- f(y) = (E - 1 + kap yc) + (l E/2 - kap) y <= 0 on [yc, 1/2]
    have hf := aff_nonpos (α := E - 1 + κ * yc) (β := l * E / 2 - κ) (p := yc) (q := 1 / 2) (x := y)
      (by nlinarith) (by nlinarith) hyy hy1
    nlinarith
  · rw [max_eq_right ha]
    have hD1 : 0 < 2 + l * yc := by positivity
    have hch := inv_chord (D := 1 + 1 + l * 1 * y) (D2 := 1 + 1 + l * 1 * (1 / 2 : ℝ)) hD1
      (by nlinarith [mul_le_mul_of_nonneg_left hyy hl.le]) (by nlinarith [mul_le_mul_of_nonneg_left hy1 hl.le])
    -- G(y) affine, G(yc) <= 0, G(1/2) <= 0
    set D1 := 2 + l * yc
    set D2 := 1 + 1 + l * 1 * (1 / 2 : ℝ)
    have hD2e : D2 = 2 + l / 2 := by simp only [D2]; ring
    have hD2 : 0 < D2 := by rw [hD2e]; positivity
    have hG := aff_nonpos
      (α := E - 1 + κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - yc) + κ * yc)
      (β := l * E / 2 - κ * l / (D1 * D2) - κ) (p := yc) (q := 1 / 2) (x := y) ?_ ?_ hyy hy1
    · have e : 1 / D1 + 1 / D2 - (1 + 1 + l * 1 * y) / (D1 * D2) = 1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * y := by
        field_simp; ring
      rw [e] at hch
      have hk := mul_le_mul_of_nonneg_left hch hκ0
      have eq : E - 1 + κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - yc) + κ * yc + (l * E / 2 - κ * l / (D1 * D2) - κ) * y
          = (1 + l * y / 2) * E - 1 + κ * ((1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * y) - yc)
            - 1 * κ * (y - yc) := by ring
      have hsplit : κ * (1 / (1 + 1 + l * 1 * y) - yc) = κ * (1 / (1 + 1 + l * 1 * y)) - κ * yc := by ring
      have hsplit2 : κ * ((1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * y) - yc)
          = κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * y) - κ * yc := by ring
      linarith
    · -- at yc: equals haa
      have e1 : 1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * yc = 1 / D1 := by
        simp only [D1]; field_simp; ring
      have : E - 1 + κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - yc) + κ * yc + (l * E / 2 - κ * l / (D1 * D2) - κ) * yc
          = (1 + l * yc / 2) * E - 1 + κ * (1 / (2 + l * yc) - yc) := by
        have : κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - yc) + κ * yc - κ * l / (D1 * D2) * yc - κ * yc
            = κ * ((1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * yc) - yc) := by ring
        rw [e1] at this
        simp only [D1] at this ⊢
        linarith
      linarith
    · have e2 : 1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * (1 / 2) = 1 / D2 := by
        simp only [D1, D2]; field_simp; ring
      have : E - 1 + κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - yc) + κ * yc + (l * E / 2 - κ * l / (D1 * D2) - κ) * (1 / 2)
          = (1 + l / 4) * E - 1 + κ * (1 / (2 + l / 2) - yc) - κ * (1 / 2 - yc) := by
        have : κ * (1 / D1 + 1 / D2 - 2 / (D1 * D2) - yc) + κ * yc - κ * l / (D1 * D2) * (1 / 2) - κ * (1 / 2)
            = κ * ((1 / D1 + 1 / D2 - 2 / (D1 * D2) - l / (D1 * D2) * (1 / 2)) - yc) - κ * (1 / 2 - yc) := by ring
        rw [e2] at this
        rw [hD2e] at this ⊢
        linarith
      linarith

/-! ### verification of the hypotheses on the window -/

namespace InWin

variable {l : ℝ} (H : InWin l)
include H

/-- F0 = f* - eps = f_ch - eps/2 -/
def F0W (l : ℝ) : ℝ := fstar l - epsW l

lemma F0_eq : F0W l = fch l - epsW l / 2 := by unfold F0W; rw [H.fstar_eq]; ring

lemma expF0_le : Real.exp (-F0W l) ≤ 1.000001 / 1.6155 := by
  rw [H.F0_eq, show -(fch l - epsW l / 2) = epsW l / 2 + (-fch l) by ring, Real.exp_add, Real.exp_neg]
  unfold fch; rw [Real.exp_log H.s_pos]
  have h1 := H.exp_half_le; have h2 := H.eps_small; have h3 := H.s_lo
  rw [mul_inv_le_iff₀ H.s_pos]
  have : 1.000001 / 1.6155 * 1.6155 ≤ 1.000001 / 1.6155 * sC l :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  have e : (1.000001 : ℝ) / 1.6155 * 1.6155 = 1.000001 := by norm_num
  linarith

lemma expF0_ge : 1 / 1.61804 ≤ Real.exp (-F0W l) := by
  rw [H.F0_eq, show -(fch l - epsW l / 2) = epsW l / 2 + (-fch l) by ring, Real.exp_add, Real.exp_neg]
  unfold fch; rw [Real.exp_log H.s_pos]
  have h1 := H.exp_half_ge
  have : 1 / 1.61804 ≤ (sC l)⁻¹ := by
    rw [one_div]; exact inv_anti₀ H.s_pos H.s_hi
  nlinarith [inv_pos.mpr H.s_pos]

/-- log(Dy/(m+1)) - F0 <= Dy/((m+1) s) - 1 + eps/2 -/
lemma logC_le (m : ℝ) (hm : 1 ≤ m) :
    Real.log ((m + 1 + l * m * yC l) / (m + 1)) - F0W l ≤ (m + 1 + m * tC l) / ((m + 1) * sC l) - 1 + epsW l / 2 := by
  rw [H.F0_eq]
  have hlt : l * m * yC l = m * tC l := by rw [← H.l_yc]; ring
  rw [hlt]
  have hpos : 0 < (m + 1 + m * tC l) / (m + 1) := by have := tC_nonneg H.pos.le; positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hpos H.s_pos)
  rw [Real.log_div hpos.ne' H.s_pos.ne'] at h
  unfold fch
  have e : (m + 1 + m * tC l) / (m + 1) / sC l = (m + 1 + m * tC l) / ((m + 1) * sC l) := by
    rw [div_div]
  rw [e] at h
  linarith

lemma Dy_eq (m : ℝ) : m + 1 + l * m * yC l = m + 1 + m * tC l := by rw [← H.l_yc]; ring

/-- C0_m for 1 <= m <= 7 -/
lemma C0 (m : ℝ) (hm : 1 ≤ m) (hm7 : m ≤ 7) :
    Real.log ((m + 1 + l * m * yC l) / (m + 1)) ≤ F0W l := by
  have h := H.logC_le m hm
  have hr : (m + 1 + m * tC l) / ((m + 1) * sC l) ≤ 0.954 := by
    rw [div_le_iff₀ (by have := H.s_pos; positivity)]
    nlinarith [H.t_hi, H.s_lo, mul_le_mul_of_nonneg_left H.s_lo (by linarith : (0:ℝ) ≤ m + 1)]
  have := H.eps_small
  linarith

/-- C_m for 1 <= m <= 7 -/
lemma Cm (m : ℝ) (hm : 1 ≤ m) (hm7 : m ≤ 7) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) :
    Real.log ((m + 1 + l * m * yC l) / (m + 1)) - F0W l + kapW l * (1 / (m + 1 + l * m * yC l) - yC l) ≤ 0 := by
  have h := H.logC_le m hm
  rw [H.Dy_eq m] at h ⊢
  have hk0 := H.kap_lo; have hk1 := H.kap_hi
  have he := H.eps_small; have he0 := H.eps_nonneg
  have hs := H.s_pos; have hslo := H.s_lo
  have ht0 := H.t_lo; have ht1 := H.t_hi
  have hy0 := H.yc_lo
  rcases hcase with h1 | h2 | h3
  · subst h1
    have hr : (1 + 1 + 1 * tC l) / ((1 + 1) * sC l) ≤ 0.8103 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hq : 1 / (1 + 1 + 1 * tC l) - yC l ≤ 0.1912 := by
      have : 1 / (1 + 1 + 1 * tC l) ≤ 1 / 2.6168 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hq0 : 0 ≤ 1 / (1 + 1 + 1 * tC l) - yC l := by
      have : 1 / 2.61804 ≤ 1 / (1 + 1 + 1 * tC l) := one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith [H.yc_hi]
    nlinarith [mul_le_mul hk1 hq hq0 (by norm_num)]
  · subst h2
    have hr : (2 + 1 + 2 * tC l) / ((2 + 1) * sC l) ≤ 0.8741 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hq : 1 / (2 + 1 + 2 * tC l) - yC l ≤ 0.0453 := by
      have : 1 / (2 + 1 + 2 * tC l) ≤ 1 / 4.2336 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    rcases le_total 0 (1 / (2 + 1 + 2 * tC l) - yC l) with hq0 | hq0
    · nlinarith [mul_le_mul hk1 hq hq0 (by norm_num)]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos H.kap_pos.le hq0]
  · have hq : 1 / (m + 1 + m * tC l) - yC l ≤ 0 := by
      have : 1 / (m + 1 + m * tC l) ≤ 1 / 5.8504 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
      linarith
    have hr : (m + 1 + m * tC l) / ((m + 1) * sC l) ≤ 0.954 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hslo (by linarith : (0:ℝ) ≤ m + 1)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos H.kap_pos.le hq]

lemma slope (m : ℝ) (hm : 2 ≤ m) : l / (m + 1 + l * m * yC l) ≤ kapW l := by
  rw [H.Dy_eq m, div_le_iff₀ (by nlinarith [H.t_lo])]
  nlinarith [H.kap_lo, H.t_lo, H.hi', mul_le_mul_of_nonneg_left H.t_lo (by linarith : (0:ℝ) ≤ m)]

lemma m1_h0a : (1 + l * yC l / 2) * Real.exp (-F0W l) - 1 ≤ 0 := by
  rw [H.l_yc]
  have := H.expF0_le; have := H.t_hi; have := Real.exp_pos (-F0W l)
  nlinarith

lemma m1_h0b : (1 + l / 4) * Real.exp (-F0W l) - 1 ≤ kapW l * (1 / 2 - yC l) := by
  have h1 := H.expF0_le; have h2 := Real.exp_pos (-F0W l)
  have h3 : (1 + l / 4) * Real.exp (-F0W l) ≤ 1.80903 * (1.000001 / 1.6155) :=
    mul_le_mul (by linarith [H.hi']) h1 h2.le (by norm_num)
  have h4 : 0.776 * 0.30842 ≤ kapW l * (1 / 2 - yC l) :=
    mul_le_mul H.kap_lo (by linarith [H.yc_hi]) (by norm_num) H.kap_pos.le
  norm_num at h3 h4 ⊢
  linarith

lemma m1_haa : (1 + l * yC l / 2) * Real.exp (-F0W l) - 1 + kapW l * (1 / (2 + l * yC l) - yC l) ≤ 0 := by
  rw [H.l_yc]
  have h1 := H.expF0_le; have h2 := Real.exp_pos (-F0W l)
  have h3 : (1 + tC l / 2) * Real.exp (-F0W l) ≤ 1.30902 * (1.000001 / 1.6155) :=
    mul_le_mul (by linarith [H.t_hi]) h1 h2.le (by norm_num)
  have hq : 1 / (2 + tC l) - yC l ≤ 0.19117 := by
    have : 1 / (2 + tC l) ≤ 1 / 2.6168 := one_div_le_one_div_of_le (by norm_num) (by linarith [H.t_lo])
    have : (1:ℝ) / 2.6168 ≤ 0.382147 := by norm_num
    linarith [H.yc_lo]
  have hq0 : 0 ≤ 1 / (2 + tC l) - yC l := by
    have : 1 / 2.61804 ≤ 1 / (2 + tC l) := one_div_le_one_div_of_le (by linarith [H.t_lo]) (by linarith [H.t_hi])
    have : (0.38196 : ℝ) ≤ 1 / 2.61804 := by norm_num
    linarith [H.yc_hi]
  have h4 := mul_le_mul H.kap_hi hq hq0 (by norm_num)
  norm_num at h3 h4 ⊢
  linarith

lemma m1_hab : (1 + l / 4) * Real.exp (-F0W l) - 1 + kapW l * (1 / (2 + l / 2) - yC l) - kapW l * (1 / 2 - yC l) ≤ 0 := by
  have h1 := H.expF0_le; have h2 := Real.exp_pos (-F0W l)
  have h3 : (1 + l / 4) * Real.exp (-F0W l) ≤ 1.80903 * (1.000001 / 1.6155) :=
    mul_le_mul (by linarith [H.hi']) h1 h2.le (by norm_num)
  have hq : 1 / (2 + l / 2) - 1 / 2 ≤ -0.2224 := by
    have : 1 / (2 + l / 2) ≤ 1 / 3.61 := one_div_le_one_div_of_le (by norm_num) (by linarith [H.lo])
    have : (1:ℝ) / 3.61 ≤ 0.27701 := by norm_num
    linarith
  have h4 : kapW l * (1 / (2 + l / 2) - 1 / 2) ≤ 0.776 * (-0.2224) := by
    nlinarith [H.kap_lo]
  have e : kapW l * (1 / (2 + l / 2) - yC l) - kapW l * (1 / 2 - yC l) = kapW l * (1 / (2 + l / 2) - 1 / 2) := by ring
  norm_num at h3 h4 ⊢
  linarith

/-- (C2), all 1 <= m <= 7, every ybar in [0, 1/2] -/
theorem c2 (m : ℝ) (hm : 1 ≤ m) (hm7 : m ≤ 7) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    Real.log (1 + l * m * y / (m + 1)) - F0W l + kapW l * max 0 (1 / (m + 1 + l * m * y) - yC l)
      ≤ m * kapW l * max 0 (y - yC l) := by
  have hk0 := H.kap_pos.le; have hk2 : kapW l ≤ 2 := by linarith [H.kap_hi]
  rcases le_total y (yC l) with hyy | hyy
  · exact c2_regionB H.pos hk0 hk2 hm hy0 hyy (H.C0 m hm hm7) (H.Cm m hm hm7 hcase)
  · rcases hcase with h1 | h2 | h3
    · subst h1
      exact c2_regionA_one H.pos hk0 (by linarith [H.yc_lo]) (by linarith [H.yc_hi]) hyy hy1
        H.m1_h0a H.m1_h0b H.m1_haa H.m1_hab
    · exact c2_regionA_ge2 H.pos hk0 (by linarith) (by linarith [H.yc_lo]) hyy (H.C0 m hm hm7)
        (H.Cm m hm hm7 (Or.inr (Or.inl h2))) (H.slope m (by linarith))
    · exact c2_regionA_ge2 H.pos hk0 (by linarith) (by linarith [H.yc_lo]) hyy (H.C0 m hm hm7)
        (H.Cm m hm hm7 (Or.inr (Or.inr h3))) (H.slope m (by linarith))

end InWin

end

end LeanCherry
