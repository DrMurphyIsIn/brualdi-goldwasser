/-
LeanCherry.PBStruct -- part (B) on (0, 1 + sqrt 5), the structural lemmas, for any leaf-exempt witness h of the
common shape (PShape): convex, zero up to ydag, below the hinge eps + kappa (y - y_ch)_+, above the last piece
eps + kappa (y - y_ch) and above a left piece eps + sm (y - y_ch), and a maximum of affine pieces of slope in [0, kappa].
  step_kpos : types with a leaf child (k >= 1);
  step_m1   : the single-child type (m = 1);
  step_arm  : m in {2, 3, 4}, the arm-point lemma (each piece is convex in the pooled message, minimal at y_ch);
  witness_of_steps : the Witness from the Bellman steps.
-/
import LeanCherry.PBBasic

open Real

namespace LeanCherry

noncomputable section

open Classical Br

/-- the common shape of the two witnesses -/
structure PShape (l sm : ℝ) (h : ℝ → ℝ) : Prop where
  conv : ConvexOn ℝ (Set.Icc (0:ℝ) (1 / 2)) h
  nonneg : ∀ y, 0 ≤ h y
  zero : ∀ y, y ≤ ydag l → h y = 0
  up : ∀ y, h y ≤ epsW l + kapP l * max 0 (y - yC l)
  kap_lo : ∀ y, epsW l + kapP l * (y - yC l) ≤ h y
  left_lo : ∀ y, epsW l + sm * (y - yC l) ≤ h y
  piece : ∀ z, ∃ a b : ℝ, 0 ≤ a ∧ a ≤ kapP l ∧ h z = a * z + b ∧ ∀ y, a * y + b ≤ h y

/-- the k = 0 Bellman inequality at (m, ybar) -/
def B0 (l : ℝ) (h : ℝ → ℝ) (m y : ℝ) : Prop :=
  h (1 / (m + 1 + l * (m * y))) ≤ fstar l + m * h y - Real.log (1 + l * (m * y) / (m + 1))

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma s_cube : 1 + 2 * l / 3 ≤ sC l ^ 3 := by
  have h := H.s_sq
  have : sC l ^ 3 = sC l * (1 + l / 2) := by rw [← h]; ring
  rw [this]; nlinarith [H.s_ge, H.pos]

/-! ### k >= 1 -/

lemma step_kpos {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (k m y : ℝ) (hk : 1 ≤ k)
    (hk3 : k = 1 ∨ k = 2 ∨ 3 ≤ k) (hm : 0 ≤ m) (hR0 : 0 ≤ m * y) (hR1 : m * y ≤ m / 2) (hh : 0 ≤ m * h y) :
    h (1 / (k + m + 1 + l * (k + m * y))) ≤
      fstar l + k * fstar l + m * h y - Real.log (1 + l * (k + m * y) / (k + m + 1)) := by
  have hl := H.pos
  have hd : 0 < k + m + 1 := by linarith
  have hR : 0 ≤ l * (k + m * y) := by positivity
  have hyv : 1 / (k + m + 1 + l * (k + m * y)) ≤ yC l := by
    unfold yC
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hk hl.le]
  have hhv : h (1 / (k + m + 1 + l * (k + m * y))) ≤ epsW l := by
    have := Sh.up (1 / (k + m + 1 + l * (k + m * y)))
    rwa [max_eq_left (by linarith), mul_zero, add_zero] at this
  have hpos : 0 < 1 + l * (k + m * y) / (k + m + 1) := by positivity
  have hF := PB.fstar_eq (l := l)
  have hfp := H.fstar_pos
  have he := H.eps_nonneg
  rcases hk3 with h1 | h2 | h3
  · subst h1
    have hr : l * (1 + m * y) / (1 + m + 1) ≤ l / 2 := by
      rw [div_le_div_iff₀ hd (by norm_num)]; nlinarith
    have hlog : Real.log (1 + l * (1 + m * y) / (1 + m + 1)) ≤ 2 * fch l := by
      rw [← log_c_eq hl.le]; exact Real.log_le_log hpos (by linarith)
    linarith
  · subst h2
    have hr : l * (2 + m * y) / (2 + m + 1) ≤ 2 * l / 3 := by
      rw [div_le_div_iff₀ hd (by norm_num)]; nlinarith
    have hlog : Real.log (1 + l * (2 + m * y) / (2 + m + 1)) ≤ 3 * fch l := by
      have : Real.log (1 + 2 * l / 3) ≤ Real.log (sC l ^ 3) := Real.log_le_log (by positivity) H.s_cube
      rw [Real.log_pow] at this
      have h' := Real.log_le_log hpos (by linarith : 1 + l * (2 + m * y) / (2 + m + 1) ≤ 1 + 2 * l / 3)
      unfold fch; push_cast at this; linarith
    linarith
  · have hr : l * (k + m * y) / (k + m + 1) ≤ l := by
      rw [div_le_iff₀ hd]; nlinarith
    have hlog : Real.log (1 + l * (k + m * y) / (k + m + 1)) ≤ 4 * fch l := by
      have h4 : 1 + l ≤ sC l ^ 4 := by
        have : sC l ^ 4 = (1 + l / 2) ^ 2 := by rw [← H.s_sq]; ring
        rw [this]; nlinarith
      have : Real.log (1 + l) ≤ Real.log (sC l ^ 4) := Real.log_le_log (by linarith) h4
      rw [Real.log_pow] at this
      have h' := Real.log_le_log hpos (by linarith : 1 + l * (k + m * y) / (k + m + 1) ≤ 1 + l)
      unfold fch; push_cast at this; linarith
    nlinarith

/-! ### the single-child type m = 1 -/

lemma kap_eq_l : kapP l = l * (2 + l) / (6 + 5 * l) := by
  have := H.pos; unfold kapP tC; field_simp; ring

lemma step_m1 {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (C4 : 0 < 8 + 6 * l + 3 * l ^ 2)
    (C5 : 0 < -5 * l ^ 3 - 14 * l ^ 2 + 128 * l + 160)
    (C6 : 0 < 2 - tC l - 2 * tC l ^ 2 - tC l ^ 3) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) : B0 l h 1 y := by
  unfold B0
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
  suffices hPhi : 0 ≤ fstar l + κ * (D - 2) / l - κ / D - Real.log D + Real.log 2 by
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
  · exact (hright D hTD hDD1).le
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

/-! ### the arm points m = 2, 3, 4 -/

lemma step_arm {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h)
    (hsm : sm ≤ l * yA l 4 * (1 - kapP l * yA l 4)) (m : ℕ) (hm2 : 2 ≤ m) (hm4 : m ≤ 4)
    (hg : h (yA l m) ≤ gArm l m) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) : B0 l h m y := by
  unfold B0
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
  have htan := tan_conv (D := D) (D0 := D0) (a := a) (by linarith) (by linarith) ha0 (by linarith)
    (by nlinarith)
  have hlogD : Real.log (1 + l * (m * y) / (m + 1)) = Real.log D - Real.log (m + 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]; congr 1; rw [hDdef]; field_simp
  have hlogD0 : Real.log (1 + tC l * m / (m + 1)) = Real.log D0 - Real.log (m + 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]; congr 1; rw [hD0def]; field_simp
  have hgA : gArm l m = fstar l + m * epsW l - (Real.log D0 - Real.log (m + 1)) := by
    unfold gArm; rw [hlogD0]
  rw [hlogD]
  rw [hY] at hpY hg
  rw [hgA] at hg
  -- q = Y (1 - a Y), Y = 1/D0
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 1 / D0 := ⟨_, rfl⟩
  rw [← hYdef] at hpY hg
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

/-! ### the witness from the Bellman steps -/

theorem witness_of_steps {h : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Icc (0:ℝ) (1 / 2)) h) (hnn : ∀ y, 0 ≤ h y)
    (hk : ∀ (k m : ℕ) (y : ℝ), 1 ≤ k → 0 ≤ y → y ≤ 1 / 2 →
      h (1 / ((k:ℝ) + m + 1 + l * (k + m * y))) ≤
        fstar l + k * fstar l + m * h y - Real.log (1 + l * (k + m * y) / (k + m + 1)))
    (h0 : ∀ (m : ℕ) (y : ℝ), 1 ≤ m → 0 ≤ y → y ≤ 1 / 2 → B0 l h m y) :
    Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) h where
  lam_pos := H.pos
  I_ord := Set.ordConnected_Icc
  I_lo := Set.Ioc_subset_Icc_self
  I_hi := Set.Icc_subset_Icc le_rfl (by norm_num)
  HA_type := by
    intro b b' hb
    simp only [Set.mem_singleton_iff, ← typeOf_leaf_iff {Br.node []}, hb]
  HA_m := by
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [(typeOf_leaf_iff {Br.node []} b).mpr hb]
  H0 := by
    intro a ha; rw [Set.mem_singleton_iff] at ha; rw [ha, gB_leaf]; exact H.fstar_pos.le
  convex := hconv
  bdd := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hnn y⟩
  leaf := fun hh => absurd rfl hh
  bell := by
    intro E m hE hcard _ ybar hy
    have hErep : E = Multiset.replicate E.card (Br.node []) :=
      Multiset.eq_replicate.mpr ⟨rfl, fun a ha => by simpa using hE a ha⟩
    set k := E.card with hk'
    rw [hErep]
    unfold Bellman
    simp only [Multiset.map_replicate, Multiset.sum_replicate, Multiset.card_replicate, msgl_node, gB_leaf]
    simp only [List.length_nil, Nat.cast_zero, zero_add, sumYl, mul_zero, add_zero, div_one, nsmul_eq_mul, mul_one]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hm : 0 < m := by omega
      obtain ⟨ht0, ht1⟩ := hy hm
      rw [hk0]; push_cast
      simp only [zero_add, zero_mul, mul_zero, add_zero]
      have := h0 m ybar hm ht0 ht1
      unfold B0 at this
      simpa [add_comm, add_left_comm, add_assoc] using this
    · rcases Nat.eq_zero_or_pos m with hm0 | hm
      · have hstep := hk k 0 0 hkpos le_rfl (by norm_num)
        rw [hm0]; push_cast at hstep ⊢
        simp only [zero_mul, mul_zero, add_zero, zero_add] at hstep ⊢
        linarith
      · obtain ⟨ht0, ht1⟩ := hy hm
        have hstep := hk k m ybar hkpos ht0 ht1
        linarith

end PB

end

end LeanCherry
