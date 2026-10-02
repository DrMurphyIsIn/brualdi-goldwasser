/-
LeanCherry.PBEqSteps -- the equality clause of part (B), part 1: strict versions of the structural Bellman steps
for any leaf-exempt witness of the common shape (PShape):
  step_kpos_lt : k >= 1, strict except for the cherry type (k, m) = (1, 0);
  step_m1_lt   : m = 1, strict;
  step_arm_lt  : m in {2, 3, 4}, the margin exceeds g(A_m) - h(y_m), strictly for ybar /= y_ch;
  arm_at_yc    : the same at ybar = y_ch, non-strictly;
  supp_strict  : a strict supporting line of h at y_ch (the corner of step (a)).
-/
import LeanCherry.PBStruct

open Real

namespace LeanCherry

noncomputable section

open Classical Br

/-- the strict tangent inequality for log -/
lemma log_lt_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Real.log a < Real.log b + (a - b) / b := by
  have hne : a / b ≠ 1 := by
    intro h; apply hab; field_simp at h; linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos ha hb) hne
  rw [Real.log_div ha.ne' hb.ne'] at h
  have : a / b - 1 = (a - b) / b := by field_simp
  linarith

/-- the strict convex-tangent lemma -/
lemma tan_conv_lt {D D0 a : ℝ} (hD : 0 < D) (hD0 : 0 < D0) (_ha : 0 ≤ a) (h2a : 2 * a < D0)
    (hc : a * D0 < D * (D0 - a)) (hne : D ≠ D0) :
    Real.log D + a / D < Real.log D0 + a / D0 + (1 / D0 - a / D0 ^ 2) * (D - D0) := by
  have hlog : Real.log D = Real.log (D / D0) + Real.log D0 := by
    rw [Real.log_div hD.ne' hD0.ne']; ring
  rw [hlog]
  have hsq : 0 < (D - D0) ^ 2 := by
    have : D - D0 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  rcases le_total D0 D with h | h
  · have hx : 1 ≤ D / D0 := by rw [le_div_iff₀ hD0]; linarith
    have hb := log_le_sinh hx
    have e : (D / D0 - (D / D0)⁻¹) / 2 + a / D - a / D0 - (1 / D0 - a / D0 ^ 2) * (D - D0)
        = -((D - D0) ^ 2 * (D0 - 2 * a)) / (2 * D * D0 ^ 2) := by
      field_simp; ring
    have hneg : -((D - D0) ^ 2 * (D0 - 2 * a)) / (2 * D * D0 ^ 2) < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity)
      have := mul_pos hsq (by linarith : (0:ℝ) < D0 - 2 * a)
      linarith
    linarith
  · have hx0 : 0 < D / D0 := by positivity
    have hx : D / D0 ≤ 1 := by rw [div_le_iff₀ hD0]; linarith
    have hb := log_le_two hx0 hx
    have e : 2 * (D / D0 - 1) / (D / D0 + 1) + a / D - a / D0 - (1 / D0 - a / D0 ^ 2) * (D - D0)
        = -((D0 - D) ^ 2 * (D * (D0 - a) - a * D0)) / (D0 ^ 2 * D * (D + D0)) := by
      field_simp; ring
    have hsq' : 0 < (D0 - D) ^ 2 := by
      have : D0 - D ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      positivity
    have hneg : -((D0 - D) ^ 2 * (D * (D0 - a) - a * D0)) / (D0 ^ 2 * D * (D + D0)) < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity)
      have := mul_pos hsq' (by linarith : (0:ℝ) < D * (D0 - a) - a * D0)
      linarith
    linarith

/-- the strict k = 0 Bellman inequality at (m, ybar) -/
def B0lt (l : ℝ) (h : ℝ → ℝ) (m y : ℝ) : Prop :=
  h (1 / (m + 1 + l * (m * y))) < fstar l + m * h y - Real.log (1 + l * (m * y) / (m + 1))

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma yc_le_half : yC l ≤ 1 / 2 := by
  unfold yC; apply one_div_le_one_div_of_le (by norm_num); linarith [H.pos]

/-- below y_ch the witness is strictly below eps -/
lemma h_lt_eps {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) {y : ℝ} (hy0 : 0 ≤ y) (hy : y < yC l) :
    h y < epsW l := by
  have hyc := H.yc_pos
  have hyc2 := H.yc_le_half
  have he := H.eps_pos
  have h0 : h 0 = 0 := Sh.zero 0 (by linarith [H.ydag_ge])
  have hC : h (yC l) ≤ epsW l := by
    have := Sh.up (yC l); rw [sub_self, max_self, mul_zero, add_zero] at this; exact this
  set θ := y / yC l with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hy0 hyc.le
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hyc]; exact hy
  have hcomb : (1 - θ) • (0:ℝ) + θ • yC l = y := by
    simp only [smul_eq_mul, mul_zero, zero_add, hθ]; field_simp
  have hcv := Sh.conv.2 (x := 0) (y := yC l) (by constructor <;> norm_num)
    (by constructor <;> linarith) (by linarith : (0:ℝ) ≤ 1 - θ) hθ0 (by ring)
  rw [hcomb] at hcv
  simp only [smul_eq_mul, h0, mul_zero, zero_add] at hcv
  have : θ * h (yC l) ≤ θ * epsW l := mul_le_mul_of_nonneg_left hC hθ0
  nlinarith

/-- k >= 1, strict except for the cherry type (1, 0) -/
lemma step_kpos_lt {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (k m : ℕ) (y : ℝ) (hk : 1 ≤ k)
    (hnot : ¬ (k = 1 ∧ m = 0)) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    h (1 / ((k:ℝ) + m + 1 + l * (k + m * y))) <
      fstar l + k * fstar l + m * h y - Real.log (1 + l * (k + m * y) / (k + m + 1)) := by
  have hl := H.pos
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm : (0:ℝ) ≤ m := by positivity
  have hmy : 0 ≤ (m:ℝ) * y := mul_nonneg hm hy0
  have hmy2 : (m:ℝ) * y ≤ m / 2 := by nlinarith
  have hhy : 0 ≤ (m:ℝ) * h y := mul_nonneg hm (Sh.nonneg y)
  have hd : 0 < (k:ℝ) + m + 1 := by linarith
  have hR : 0 ≤ l * (k + m * y) := by positivity
  have hyv : 1 / ((k:ℝ) + m + 1 + l * (k + m * y)) ≤ yC l := by
    unfold yC
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hkR hl.le]
  have hhv : h (1 / ((k:ℝ) + m + 1 + l * (k + m * y))) ≤ epsW l := by
    have := Sh.up (1 / ((k:ℝ) + m + 1 + l * (k + m * y)))
    rwa [max_eq_left (by linarith), mul_zero, add_zero] at this
  have hpos : 0 < 1 + l * (k + m * y) / (k + m + 1) := by positivity
  have hF := PB.fstar_eq (l := l)
  have hfp := H.fstar_pos
  have he := H.eps_pos
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with h1 | h2 | h3
  · subst h1
    have hm1 : 1 ≤ m := by omega
    have hm1R : (1:ℝ) ≤ m := by exact_mod_cast hm1
    push_cast at hhv hyv ⊢
    have hr : l * (1 + m * y) / (1 + m + 1) ≤ l / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hlog : Real.log (1 + l * (1 + m * y) / (1 + m + 1)) ≤ 2 * fch l := by
      rw [← log_c_eq hl.le]; exact Real.log_le_log (by positivity) (by linarith)
    have hlt : 1 / ((1:ℝ) + m + 1 + l * (1 + m * y)) < yC l := by
      unfold yC
      apply one_div_lt_one_div_of_lt (by linarith)
      nlinarith
    have hv0 : 0 ≤ 1 / ((1:ℝ) + m + 1 + l * (1 + m * y)) := by positivity
    have := H.h_lt_eps Sh hv0 hlt
    linarith
  · subst h2
    push_cast at hhv ⊢
    have hr : l * (2 + m * y) / (2 + m + 1) ≤ 2 * l / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hlog : Real.log (1 + l * (2 + m * y) / (2 + m + 1)) ≤ 3 * fch l := by
      have : Real.log (1 + 2 * l / 3) ≤ Real.log (sC l ^ 3) := Real.log_le_log (by positivity) H.s_cube
      rw [Real.log_pow] at this
      have h' := Real.log_le_log (by positivity) (by linarith : 1 + l * (2 + m * y) / (2 + m + 1) ≤ 1 + 2 * l / 3)
      unfold fch; push_cast at this; linarith
    linarith
  · have hk3 : (3:ℝ) ≤ k := by exact_mod_cast h3
    have hr : l * (k + m * y) / (k + m + 1) ≤ l := by
      rw [div_le_iff₀ hd]; nlinarith
    have hlog : Real.log (1 + l * (k + m * y) / (k + m + 1)) ≤ 4 * fch l := by
      have h4 : 1 + l ≤ sC l ^ 4 := by
        have : sC l ^ 4 = (1 + l / 2) ^ 2 := by rw [← H.s_sq]; ring
        rw [this]; nlinarith
      have : Real.log (1 + l) ≤ Real.log (sC l ^ 4) := Real.log_le_log (by linarith) h4
      rw [Real.log_pow] at this
      have h' := Real.log_le_log hpos (by linarith : 1 + l * (k + m * y) / (k + m + 1) ≤ 1 + l)
      unfold fch; push_cast at this; linarith
    have hkF : 3 * fstar l ≤ k * fstar l := mul_le_mul_of_nonneg_right hk3 hfp.le
    linarith

end PB

end

end LeanCherry
