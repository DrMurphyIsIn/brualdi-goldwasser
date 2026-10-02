/-
LeanCherry.PBEqSteps2 -- the equality clause of part (B), part 2: strict m = 1 and strict arm-point steps, the arm
point at y_ch, and the strict corner of h at y_ch.
-/
import LeanCherry.PBEqSteps

open Real

namespace LeanCherry

noncomputable section

open Classical Br

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma step_m1_lt {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (C4 : 0 < 8 + 6 * l + 3 * l ^ 2)
    (C5 : 0 < -5 * l ^ 3 - 14 * l ^ 2 + 128 * l + 160)
    (C6 : 0 < 2 - tC l - 2 * tC l ^ 2 - tC l ^ 3) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) : B0lt l h 1 y := by
  unfold B0lt
  have hl := H.pos
  have hk0 := H.kap_pos; have hk1 := H.kap_lt
  have hkl := H.kap_eq_l
  set κ := kapP l with hκdef
  set D := 2 + l * y with hDdef
  have hD2 : 2 ≤ D := by have : 0 ≤ l * y := by positivity
                         linarith
  set D1 := 2 + l / 2 with hD1def
  have hDD1 : D ≤ D1 := by rw [hDdef, hD1def]; nlinarith
  set T0 := 2 + tC l with hT0def
  have ht0 := H.t_pos
  have htl : tC l * (2 + l) = l := by unfold tC; field_simp
  have hT0 : 2 ≤ T0 := by linarith
  have hT0D1 : D1 - T0 = l ^ 2 / (2 * (2 + l)) := by
    rw [hD1def, hT0def]; unfold tC; field_simp; ring
  have hDarg : (1:ℝ) + 1 + l * (1 * y) = D := by rw [hDdef]; ring
  rw [hDarg]
  have hlog : Real.log (1 + l * (1 * y) / (1 + 1)) = Real.log D - Real.log 2 := by
    rw [← Real.log_div (by linarith) (by norm_num)]; congr 1; rw [hDdef]; ring
  rw [hlog]
  clear_value κ D D1 T0
  have hyc : yC l ≤ 1 / D := by
    unfold yC; apply one_div_le_one_div_of_le (by linarith); rw [hDdef]; nlinarith
  have hup := Sh.up (1 / D)
  rw [max_eq_right (by linarith)] at hup
  have hlo := Sh.kap_lo y
  rw [← hκdef] at hup hlo
  -- it suffices that Phi(D) := F + kappa (D - 2)/l - kappa/D - log D + log 2 >= 0
  have hy : y = (D - 2) / l := by rw [hDdef]; field_simp; ring
  suffices hPhi : 0 < fstar l + κ * (D - 2) / l - κ / D - Real.log D + Real.log 2 by
    have e : κ * (y - yC l) - κ * (1 / D - yC l) = κ * (D - 2) / l - κ / D := by rw [hy]; ring
    linarith
  -- tangent lines of Phi
  have tan : ∀ D0 : ℝ, 2 ≤ D0 → ∀ X : ℝ, 2 ≤ X →
      Real.log X + κ / X ≤ Real.log D0 + κ / D0 + (1 / D0 - κ / D0 ^ 2) * (X - D0) := by
    intro D0 hD0 X hX
    apply tan_conv (by linarith) (by linarith) hk0.le (by linarith)
    nlinarith
  have tanPhi : ∀ D0 : ℝ, 2 ≤ D0 → ∀ X : ℝ, 2 ≤ X →
      fstar l + κ * (D0 - 2) / l - κ / D0 - Real.log D0 + Real.log 2
        + (κ / l + κ / D0 ^ 2 - 1 / D0) * (X - D0)
        ≤ fstar l + κ * (X - 2) / l - κ / X - Real.log X + Real.log 2 := by
    intro D0 hD0 X hX
    have := tan D0 hD0 X hX
    have e : κ * (X - 2) / l = κ * (D0 - 2) / l + κ / l * (X - D0) := by field_simp; ring
    rw [e]; nlinarith
  -- the value at D1
  have hfch : -(l ^ 2 / (16 * (2 + l))) ≤ fch l - Real.log (1 + l / 4) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < (1 + l / 2) / (1 + l / 4) ^ 2)
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, log_c_eq hl.le] at h1
    have e : 1 - ((1 + l / 2) / (1 + l / 4) ^ 2)⁻¹ = -(l ^ 2 / (8 * (2 + l))) := by
      field_simp; ring
    rw [e] at h1; push_cast at h1
    have e2 : l ^ 2 / (8 * (2 + l)) = 2 * (l ^ 2 / (16 * (2 + l))) := by field_simp; ring
    linarith
  have hA : l ^ 2 * (8 + 6 * l + 3 * l ^ 2) / (16 * (2 + l) * (4 + l) * (6 + 5 * l))
      ≤ fstar l + κ * (D1 - 2) / l - κ / D1 - Real.log D1 + Real.log 2 := by
    have hlD1 : Real.log D1 - Real.log 2 = Real.log (1 + l / 4) := by
      rw [← Real.log_div (by rw [hD1def]; positivity) (by norm_num)]; congr 1; rw [hD1def]; ring
    have e : -(l ^ 2 / (16 * (2 + l))) + (κ * (D1 - 2) / l - κ / D1)
        = l ^ 2 * (8 + 6 * l + 3 * l ^ 2) / (16 * (2 + l) * (4 + l) * (6 + 5 * l)) := by
      rw [hkl, hD1def]; field_simp; ring
    have := H.fch_le
    linarith
  have hA0 : 0 < l ^ 2 * (8 + 6 * l + 3 * l ^ 2) / (16 * (2 + l) * (4 + l) * (6 + 5 * l)) :=
    div_pos (mul_pos (by positivity) C4) (by positivity)
  have hP1 : κ / l + κ / D1 ^ 2 - 1 / D1 = (l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2) := by
    rw [hkl, hD1def]; field_simp; ring
  have hC5' : 0 < l ^ 2 * (8 + 6 * l + 3 * l ^ 2) / (16 * (2 + l) * (4 + l) * (6 + 5 * l))
      - (l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2) * (l ^ 2 / (2 * (2 + l))) := by
    have e : l ^ 2 * (8 + 6 * l + 3 * l ^ 2) / (16 * (2 + l) * (4 + l) * (6 + 5 * l))
        - (l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2) * (l ^ 2 / (2 * (2 + l)))
        = l ^ 2 * (-5 * l ^ 3 - 14 * l ^ 2 + 128 * l + 160) / (16 * (2 + l) * (4 + l) ^ 2 * (6 + 5 * l)) := by
      field_simp; ring
    rw [e]; positivity
  -- the derivative at T0 is <= 0
  have hP0 : κ / l + κ / T0 ^ 2 - 1 / T0 ≤ 0 := by
    have hk' : κ = l / (3 + 2 * tC l) := by rw [hκdef]; rfl
    have e : κ / l + κ / T0 ^ 2 - 1 / T0 = (l - (2 + tC l) * (1 + tC l)) / ((3 + 2 * tC l) * (2 + tC l) ^ 2) := by
      rw [hk', hT0def]; field_simp; ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have h1t : 0 < 1 - tC l := by linarith [H.t_lt_one]
    have key : (1 - tC l) * (l - (2 + tC l) * (1 + tC l)) = -(2 - tC l - 2 * tC l ^ 2 - tC l ^ 3) := by
      linear_combination (-1 : ℝ) * htl
    by_contra hc; push Not at hc
    have := mul_pos h1t hc
    linarith
  -- Phi > 0 on [T0, D1]
  have hright : ∀ X : ℝ, T0 ≤ X → X ≤ D1 → 0 < fstar l + κ * (X - 2) / l - κ / X - Real.log X + Real.log 2 := by
    intro X hX1 hX2
    have ht := tanPhi D1 (by rw [hD1def]; linarith) X (by linarith)
    rw [hP1] at ht
    rcases le_total ((l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2)) 0 with hp | hp
    · have : 0 ≤ (l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2) * (X - D1) :=
        mul_nonneg_of_nonpos_of_nonpos hp (by linarith)
      linarith
    · have : (l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2) * (l ^ 2 / (2 * (2 + l)))
          ≥ (l ^ 3 + 4 * l ^ 2 - 12 * l - 16) / ((6 + 5 * l) * (4 + l) ^ 2) * (D1 - X) := by
        rw [← hT0D1]; exact mul_le_mul_of_nonneg_left (by linarith) hp
      linarith
  rcases le_total T0 D with hTD | hTD
  · exact hright D hTD hDD1
  · have hTD1 : T0 ≤ D1 := by
      have : 0 ≤ l ^ 2 / (2 * (2 + l)) := by positivity
      linarith
    have h1 := hright T0 le_rfl hTD1
    have h2 := tanPhi T0 hT0 D hD2
    have hDT : D - T0 ≤ 0 := by linarith
    have hm : 0 ≤ (κ / l + κ / T0 ^ 2 - 1 / T0) * (D - T0) := by
      have := mul_le_mul_of_nonpos_right hP0 hDT
      simpa using this
    linarith

lemma step_arm_lt {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h)
    (hsm : sm ≤ l * yA l 4 * (1 - kapP l * yA l 4)) (m : ℕ) (hm2 : 2 ≤ m) (hm4 : m ≤ 4)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) (hyc : y ≠ yC l) :
    h (1 / (m + 1 + l * (m * y))) + (gArm l m - h (yA l m)) <
      fstar l + m * h y - Real.log (1 + l * (m * y) / (m + 1)) := by
  have hl := H.pos; have ht := H.t_pos
  have hk := H.kap_lt; have hk0 := H.kap_pos
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hm4R : (m:ℝ) ≤ 4 := by exact_mod_cast hm4
  have hlt := H.l_yc
  set D := (m:ℝ) + 1 + l * (m * y) with hDdef
  set D0 := (m:ℝ) + 1 + m * tC l with hD0def
  have hD0 : 3 ≤ D0 := by rw [hD0def]; nlinarith
  have hD : (m:ℝ) + 1 ≤ D := by
    have : 0 ≤ l * (m * y) := by positivity
    rw [hDdef]; linarith
  have hDD0 : D - D0 = l * m * (y - yC l) := by rw [hDdef, hD0def]; linear_combination (m:ℝ) * hlt
  have hY : yA l m = 1 / D0 := rfl
  have hmt2 : 2 * tC l ≤ m * tC l := mul_le_mul_of_nonneg_right hmR ht.le
  have hmt4 : m * tC l ≤ 4 * tC l := mul_le_mul_of_nonneg_right hm4R ht.le
  have hD0lo : 3 + 2 * tC l ≤ D0 := by rw [hD0def]; linarith
  have hD0hi : D0 ≤ 5 + 4 * tC l := by rw [hD0def]; linarith
  clear_value D D0
  obtain ⟨a, b, ha0, hak, hz, hp⟩ := Sh.piece (1 / D)
  rw [hz]
  have hpY := hp (yA l m)
  have hDne : D ≠ D0 := by
    intro hDe
    have h0 : l * m * (y - yC l) = 0 := by rw [← hDD0, hDe, sub_self]
    have hlm : l * m ≠ 0 := by positivity
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hlm h1
    · exact hyc (by linarith)
  have htan := tan_conv_lt (D := D) (D0 := D0) (a := a) (by linarith) (by linarith) ha0 (by linarith)
    (by nlinarith) hDne
  have hlogD : Real.log (1 + l * (m * y) / (m + 1)) = Real.log D - Real.log (m + 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]; congr 1; rw [hDdef]; field_simp
  have hlogD0 : Real.log (1 + tC l * m / (m + 1)) = Real.log D0 - Real.log (m + 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]; congr 1; rw [hD0def]; field_simp
  have hgA : gArm l m = fstar l + m * epsW l - (Real.log D0 - Real.log (m + 1)) := by
    unfold gArm; rw [hlogD0]
  rw [hlogD]
  rw [hgA]
  rw [hY] at hpY ⊢
  -- q = Y (1 - a Y), Y = 1/D0
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 1 / D0 := ⟨_, rfl⟩
  rw [← hYdef] at hpY ⊢
  have hq : 1 / D0 - a / D0 ^ 2 = Y * (1 - a * Y) := by rw [hYdef]; field_simp
  rw [hq] at htan
  have hY0 : 0 < Y := by rw [hYdef]; exact one_div_pos.mpr (by linarith)
  have hY2 : Y ≤ yA l 2 := by
    unfold yA; rw [hYdef]; apply one_div_le_one_div_of_le (by positivity); linarith
  have hY4 : yA l 4 ≤ Y := by
    unfold yA; rw [hYdef]; apply one_div_le_one_div_of_le (by linarith); linarith
  have hY13 : Y ≤ 1 / 3 := by rw [hYdef]; exact one_div_le_one_div_of_le (by norm_num) hD0
  have hy4 : 0 < yA l 4 := by unfold yA; positivity
  have hy45 : yA l 4 ≤ 1 / 5 := by unfold yA; apply one_div_le_one_div_of_le (by norm_num); linarith
  -- l q lies between sm and kappa
  have hqk : l * (Y * (1 - a * Y)) ≤ kapP l := by
    rw [PB.kap_eq_y2]
    have : Y * (1 - a * Y) ≤ yA l 2 := by
      have e : Y * (1 - a * Y) = Y - a * Y * Y := by ring
      have : 0 ≤ a * Y * Y := by positivity
      rw [e]; linarith
    exact mul_le_mul_of_nonneg_left this hl.le
  have hqs : sm ≤ l * (Y * (1 - a * Y)) := by
    have h1 : yA l 4 * (1 - kapP l * yA l 4) ≤ Y * (1 - a * Y) := by
      have e : Y * (1 - a * Y) - yA l 4 * (1 - kapP l * yA l 4)
          = (Y - yA l 4) * (1 - a * (Y + yA l 4)) + (kapP l - a) * yA l 4 ^ 2 := by ring
      have h2 : 0 ≤ (Y - yA l 4) * (1 - a * (Y + yA l 4)) := mul_nonneg (by linarith) (by nlinarith)
      have h3 : 0 ≤ (kapP l - a) * yA l 4 ^ 2 := mul_nonneg (by linarith) (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h1 hl.le
    linarith
  -- the lower bound on h(ybar)
  have hlow : l * (Y * (1 - a * Y)) * (y - yC l) ≤ h y - epsW l := by
    rcases le_total (yC l) y with hyc | hyc
    · have := Sh.kap_lo y
      have := mul_le_mul_of_nonneg_right hqk (by linarith : 0 ≤ y - yC l)
      linarith
    · have := Sh.left_lo y
      have := mul_le_mul_of_nonpos_right hqs (by linarith : y - yC l ≤ 0)
      linarith
  have hfin : (m:ℝ) * (l * (Y * (1 - a * Y)) * (y - yC l)) ≤ m * (h y - epsW l) :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  have e : Y * (1 - a * Y) * (D - D0) = m * (l * (Y * (1 - a * Y)) * (y - yC l)) := by rw [hDD0]; ring
  have hY' : a * (1 / D) = a / D := by ring
  have hY'' : a * Y = a / D0 := by rw [hYdef]; ring
  linarith


/-- the arm point at ybar = y_ch: the margin is at least g(A_m) - h(y_m) -/
lemma arm_at_yc {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (m : ℕ) :
    h (1 / (m + 1 + l * (m * yC l))) + (gArm l m - h (yA l m)) ≤
      fstar l + m * h (yC l) - Real.log (1 + l * (m * yC l) / (m + 1)) := by
  have hlt := H.l_yc
  have e1 : (m:ℝ) + 1 + l * (m * yC l) = m + 1 + m * tC l := by rw [← hlt]; ring
  have e2 : l * (m * yC l) / (m + 1) = tC l * m / (m + 1) := by rw [← hlt]; ring
  rw [e1, e2]
  have hYm : yA l m = 1 / (m + 1 + m * tC l) := rfl
  rw [← hYm]
  have hk := Sh.kap_lo (yC l)
  rw [sub_self, mul_zero, add_zero] at hk
  have hm0 : (0:ℝ) ≤ m := by positivity
  have := mul_le_mul_of_nonneg_left hk hm0
  unfold gArm
  linarith

/-- the left slope is strictly below kappa -/
lemma sm_lt_kap {sm : ℝ} (hsm : sm ≤ l * yA l 4 * (1 - kapP l * yA l 4)) : sm < kapP l := by
  have hy4 : 0 < yA l 4 := by unfold yA; have := H.t_pos; positivity
  have hk := H.kap_pos
  have h1 : l * yA l 4 * (1 - kapP l * yA l 4) < l * yA l 4 := by
    have : 0 < l * yA l 4 * (kapP l * yA l 4) := by have := H.pos; positivity
    nlinarith
  have h2 : l * yA l 4 ≤ kapP l := by
    rw [PB.kap_eq_y2]
    apply mul_le_mul_of_nonneg_left _ H.pos.le
    unfold yA; apply one_div_le_one_div_of_le (by have := H.t_pos; positivity); have := H.t_pos; linarith
  linarith

/-- h(y_ch) = eps -/
lemma h_yc {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) : h (yC l) = epsW l := by
  have h1 := Sh.up (yC l); rw [sub_self, max_self, mul_zero, add_zero] at h1
  have h2 := Sh.kap_lo (yC l); rw [sub_self, mul_zero, add_zero] at h2
  linarith

/-- step (a): a strict supporting line of h at the corner y_ch -/
lemma supp_strict {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (hsk : sm < kapP l) :
    ∃ s : ℝ, ∀ y : ℝ, y ≠ yC l → h (yC l) + s * (y - yC l) < h y := by
  refine ⟨(sm + kapP l) / 2, fun y hy => ?_⟩
  rw [H.h_yc Sh]
  rcases lt_or_gt_of_ne hy with h1 | h1
  · have := Sh.left_lo y
    have : (sm + kapP l) / 2 * (y - yC l) < sm * (y - yC l) := by nlinarith
    linarith
  · have := Sh.kap_lo y
    have : (sm + kapP l) / 2 * (y - yC l) < kapP l * (y - yC l) := by nlinarith
    linarith

end PB

end

end LeanCherry
