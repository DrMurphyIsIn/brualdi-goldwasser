/-
LeanCherry.PBGap -- F = f_3 on (0, 3/20]: the arm A_3 is a best arm for 0 < lam <= 3/20 (t <= 3/43), by hand.
For j = 1, 2, 4 the comparison f_j <= f_3 reduces, via elementary bounds for log, to a polynomial inequality on
(0, 3/43]; for j >= 5, f_j - f_ch <= (D - sigma/6)/11 <= (f_3 - f_ch).  (This replaces the paper's lem:lam-cross /
thm:lam-ladder(c) on this range; C9 is not needed.)
-/
import LeanCherry.PBWstar

open Real

namespace LeanCherry

noncomputable section

lemma log_ge_quad {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have h1 : 0 < 1 / (1 + x) := by positivity
  have h2 : 1 / (1 + x) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h := log_le_two h1 h2
  rw [one_div, Real.log_inv] at h
  have e : 2 * ((1 + x)⁻¹ - 1) / ((1 + x)⁻¹ + 1) = -(2 * x / (2 + x)) := by
    field_simp; ring
  rw [e] at h
  have h3 : x - x ^ 2 / 2 ≤ 2 * x / (2 + x) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith [pow_nonneg hx 3]
  linarith

lemma log_one_sub_ge {t : ℝ} (h1 : t < 1) : -(t / (1 - t)) ≤ Real.log (1 - t) := by
  have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 - t)
  have hne : (1 - t) ≠ 0 := ne_of_gt (by linarith)
  have e : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by field_simp; ring
  linarith


/-- D(j) as a function of t: log(1 + a t) + log(1 - t)/2 with a = j/(j+1) -/
def DD (t a : ℝ) : ℝ := Real.log (1 + a * t) + Real.log (1 - t) / 2

lemma DD_lo3 {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    3 * t / 4 - (3 * t / 4) ^ 2 / 2 - t / (1 - t) / 2 ≤ DD t (3 / 4) := by
  unfold DD
  have a := log_ge_quad (by positivity : (0:ℝ) ≤ 3 / 4 * t)
  have b := log_one_sub_ge h1
  have e : 3 / 4 * t - (3 / 4 * t) ^ 2 / 2 = 3 * t / 4 - (3 * t / 4) ^ 2 / 2 := by ring
  linarith

lemma cmp1 {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 3 / 43) : DD t (1 / 2) / 3 ≤ DD t (3 / 4) / 7 := by
  have ht1 : t < 1 := by linarith
  have lo := DD_lo3 h0 ht1
  unfold DD at *
  have a1 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + 1 / 2 * t)
  have a2 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 - t)
  have a3 := log_ge_quad (by positivity : (0:ℝ) ≤ 3 / 4 * t)
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

lemma cmp2 {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 3 / 43) : DD t (2 / 3) / 5 ≤ DD t (3 / 4) / 7 := by
  have ht1 : t < 1 := by linarith
  unfold DD
  have a1 := log_one_add_le3 (by positivity : (0:ℝ) ≤ 2 / 3 * t)
  have a2 := log_one_sub_le3 h0.le ht1
  have a3 := log_ge_quad (by positivity : (0:ℝ) ≤ 3 / 4 * t)
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0]

lemma cmp4 {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 3 / 43) : DD t (4 / 5) / 9 ≤ DD t (3 / 4) / 7 := by
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  unfold DD
  have a1 := log_one_add_le3 (by positivity : (0:ℝ) ≤ 4 / 5 * t)
  have a3 := log_ge_quad (by positivity : (0:ℝ) ≤ 3 / 4 * t)
  have a2 := log_one_sub_ge ht1
  have key : 7 * (4 / 5 * t - (4 / 5 * t) ^ 2 / 2 + (4 / 5 * t) ^ 3 / 3)
      - 9 * (3 / 4 * t - (3 / 4 * t) ^ 2 / 2) + t / (1 - t) ≤ 0 := by
    have e : 7 * (4 / 5 * t - (4 / 5 * t) ^ 2 / 2 + (4 / 5 * t) ^ 3 / 3)
        - 9 * (3 / 4 * t - (3 / 4 * t) ^ 2 / 2) + t / (1 - t)
        = t * ((-(23:ℝ) / 20 + 233 / 800 * t + 448 / 375 * t ^ 2) * (1 - t) + 1) / (1 - t) := by
      field_simp; ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ h1t.le
    apply mul_nonpos_of_nonneg_of_nonpos h0.le
    nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

/-- the comparison for the tail: (D - sigma/6)/11 <= D(3)/7 when D <= t/2 - 3t^2/4 + t^3/6 -/
lemma cmp_tail {t D : ℝ} (h0 : 0 < t) (h1 : t ≤ 3 / 43) (hD : D ≤ t / 2 - 3 * t ^ 2 / 4 + t ^ 3 / 6) :
    (D - t / (1 + t) / 6) / 11 ≤ DD t (3 / 4) / 7 := by
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have lo := DD_lo3 h0 ht1
  have hmid : (t / 2 - 3 * t ^ 2 / 4 + t ^ 3 / 6 - t / (1 + t) / 6) / 11
      ≤ (3 * t / 4 - (3 * t / 4) ^ 2 / 2 - t / (1 - t) / 2) / 7 := by
    have e1 : (t / 2 - 3 * t ^ 2 / 4 + t ^ 3 / 6 - t / (1 + t) / 6) / 11
        = t * ((1 / 2 - 3 * t / 4 + t ^ 2 / 6) * (1 + t) - 1 / 6) / (11 * (1 + t)) := by
      field_simp <;> ring
    have e2 : (3 * t / 4 - (3 * t / 4) ^ 2 / 2 - t / (1 - t) / 2) / 7
        = t * ((3 / 4 - 9 * t / 32) * (1 - t) - 1 / 2) / (7 * (1 - t)) := by
      field_simp <;> ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : ((1 / 2 - 3 * t / 4 + t ^ 2 / 6) * (1 + t) - 1 / 6) * (7 * (1 - t))
        ≤ ((3 / 4 - 9 * t / 32) * (1 - t) - 1 / 2) * (11 * (1 + t)) := by
      nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0, mul_pos (mul_pos h0 h0) (mul_pos h0 h0)]
    nlinarith [mul_le_mul_of_nonneg_left hq h0.le]
  have : (D - t / (1 + t) / 6) / 11 ≤ (t / 2 - 3 * t ^ 2 / 4 + t ^ 3 / 6 - t / (1 + t) / 6) / 11 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  linarith

/-- D >= sigma/3 from the elementary bounds, t <= 3/43 -/
lemma D_ge_third {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 3 / 43) :
    t / (1 + t) / 3 ≤ Real.log (1 + t) + Real.log (1 - t) / 2 := by
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have b1 := log_ge_quad h0.le
  have b2 := log_one_sub_ge ht1
  have : t / (1 + t) / 3 ≤ t - t ^ 2 / 2 - t / (1 - t) / 2 := by
    have e1 : t / (1 + t) / 3 = t * (1 - t) / (3 * (1 + t) * (1 - t)) := by field_simp
    have e2 : t - t ^ 2 / 2 - t / (1 - t) / 2 = t * ((1 - t / 2) * (1 - t) - 1 / 2) * (3 * (1 + t)) / (3 * (1 + t) * (1 - t)) := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0]
  linarith

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma Dj_DD (j : ℕ) : Dj l j = DD (tC l) (j / (j + 1)) := by
  unfold Dj DD; rw [H.fch_eq]; ring_nf

/-- the tail: for j >= 5, D(j)/(2j+1) <= (D - sigma/6)/11 -/
lemma tail_bound (ht : tC l ≤ 3 / 43) (j : ℕ) (h5 : 5 ≤ j) : Dj l j / (2 * j + 1) ≤ (Dinf l - sig l / 6) / 11 := by
  have hj5 : (5:ℝ) ≤ j := by exact_mod_cast h5
  have hD := H.Dinf_pos; have hσ := H.sig_pos
  have hDlo : sig l / 3 ≤ Dinf l := by
    rw [H.D_eq_logs, PB.sig_eq]; exact D_ge_third H.t_pos ht
  have hjp : (0:ℝ) < 2 * j + 1 := by positivity
  rcases le_or_gt (Dj l j) 0 with hneg | hpos
  · have : Dj l j / (2 * j + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hjp.le
    have : 0 ≤ (Dinf l - sig l / 6) / 11 := by
      apply div_nonneg _ (by norm_num); linarith
    linarith
  · have hle := Dj_le H.pos.le j
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / ((j : ℝ) + 1) := ⟨_, rfl⟩
    have hz0 : 0 < z := by rw [hz]; positivity
    have hz6 : z ≤ 1 / 6 := by rw [hz]; apply one_div_le_one_div_of_le (by norm_num); linarith
    have hsz : sig l / (j + 1) = sig l * z := by rw [hz]; ring
    rw [hsz] at hle
    have h2j : (2 * (j : ℝ) + 1) = (2 - z) / z := by rw [hz]; field_simp; ring
    have h2z : 0 < 2 - z := by linarith
    have hfrac : Dj l j / (2 * j + 1) ≤ z * (Dinf l - sig l * z) / (2 - z) := by
      rw [h2j, div_div_eq_mul_div, div_le_div_iff₀ h2z h2z]
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ z * (2 - z))
      nlinarith
    have hpos2 : 0 ≤ Dinf l - sig l * (1 / 6 + z) := by nlinarith
    have hmono : z * (Dinf l - sig l * z) ≤ 1 / 6 * (Dinf l - sig l / 6) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 6 - z) hpos2]
    have hnum : 0 ≤ z * (Dinf l - sig l * z) := mul_nonneg hz0.le (by nlinarith)
    have h3 : z * (Dinf l - sig l * z) / (2 - z) ≤ z * (Dinf l - sig l * z) / (11 / 6) :=
      div_le_div_of_nonneg_left hnum (by norm_num) (by linarith)
    have h4 : z * (Dinf l - sig l * z) / (11 / 6) ≤ (Dinf l - sig l / 6) / 11 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith

/-- f_j <= f_3 for every arm, when t <= 3/43 -/
lemma arm_le_three (ht : tC l ≤ 3 / 43) (j : ℕ) (hj : 1 ≤ j) : fArm l j ≤ fArm l 3 := by
  have ht0 := H.t_pos
  rw [fArm_eq H.pos.le, fArm_eq H.pos.le]
  suffices h : Dj l j / (2 * j + 1) ≤ Dj l 3 / (2 * (3:ℕ) + 1) by linarith
  have h3 : Dj l 3 / (2 * ((3:ℕ):ℝ) + 1) = DD (tC l) (3 / 4) / 7 := by
    rw [H.Dj_DD]; norm_num
  rw [h3]
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j) with e | e | e | e | h5
  · subst e; rw [H.Dj_DD]; norm_num; exact cmp1 ht0 ht
  · subst e; rw [H.Dj_DD]; norm_num; exact cmp2 ht0 ht
  · subst e; rw [H.Dj_DD]; norm_num
  · subst e; rw [H.Dj_DD]; norm_num; exact cmp4 ht0 ht
  · have h1 := H.tail_bound ht j h5
    have h2 := cmp_tail ht0 ht H.D_le_cubic
    rw [PB.sig_eq] at h1
    linarith

end PB

/-- **F = f_3 on (0, 3/20]**: A_3 is a best arm -/
theorem fstar_eq_f3 (l : ℝ) (hl0 : 0 < l) (hl : l ≤ 3 / 20) : fstar l = fArm l 3 := by
  have H : PB l := ⟨hl0, by have := sqrt5_bounds.1; linarith⟩
  have ht : tC l ≤ 3 / 43 := by
    unfold tC; rw [div_le_iff₀ (by linarith)]; linarith
  apply le_antisymm _ (fArm_le_fstar hl0 (by norm_num))
  exact csSup_le (armSet_nonempty l) (by rintro x ⟨j, hj, rfl⟩; exact H.arm_le_three ht j hj)

end

end LeanCherry
