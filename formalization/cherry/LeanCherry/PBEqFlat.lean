/-
LeanCherry.PBEqFlat -- the equality clause of part (B), part 3: the flat tails m >= 5, strictly for ybar /= y_ch
(the linear ramp W* and the kinked ramp W2).
-/
import LeanCherry.PBEqSteps2
import LeanCherry.PBFlat

open Real

namespace LeanCherry

noncomputable section

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma flat_common_lt {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (m : ℕ) (hm : 5 ≤ m) (y : ℝ) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1 / 2) :
    h (1 / (m + 1 + l * (m * y))) = 0 ∧ l * (m * y) / (m + 1) = l * m / (m + 1) * y ∧
    (y ≤ ydag l → B0lt l h m y) ∧ (yC l < y → B0lt l h m y) := by
  have hl := H.pos
  have hmR : (5:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hm1 : (0:ℝ) < m + 1 := by linarith
  have hyv : 1 / (m + 1 + l * (m * y)) ≤ ydag l := by
    have h6 : 6 ≤ m + 1 + l * (m * y) := by
      have : 0 ≤ l * (m * y) := mul_nonneg hl.le (mul_nonneg hm0 hy0)
      linarith
    have : 1 / (m + 1 + l * (m * y)) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) h6
    linarith [H.ydag_ge]
  have hz := Sh.zero _ hyv
  have harg : l * (m * y) / (m + 1) = l * m / (m + 1) * y := by ring
  refine ⟨hz, harg, ?_, ?_⟩
  · intro h1
    unfold B0lt; rw [hz, harg]
    set c := l * m / (m + 1) with hc
    have hc0 : 0 < c := by rw [hc]; positivity
    have hcl : c < l := by rw [hc, div_lt_iff₀ hm1]; nlinarith
    have hyd0 : 0 < ydag l := by linarith [H.ydag_ge]
    have hle1 : c * y ≤ c * ydag l := mul_le_mul_of_nonneg_left h1 hc0.le
    have hle2 : c * ydag l < l * ydag l := mul_lt_mul_of_pos_right hcl hyd0
    have : Real.log (1 + c * y) < Real.log (1 + l * ydag l) :=
      Real.log_lt_log (by positivity) (by linarith)
    rw [H.log_ydag] at this
    have := mul_nonneg hm0 (Sh.nonneg y)
    linarith
  · intro h2
    unfold B0lt; rw [hz, harg]
    set c := l * m / (m + 1) with hc
    have hc0 : 0 < c := by rw [hc]; positivity
    have hyc0 := H.yc_pos
    have hgm := H.gArm_nonneg m (by omega)
    have hcyc : c * yC l = tC l * m / (m + 1) := by rw [hc, ← H.l_yc]; ring
    unfold gArm at hgm
    rw [← hcyc] at hgm
    have hh := Sh.kap_lo y
    have htan := log_lt_tangent (by positivity : 0 < 1 + c * y) (by positivity : 0 < 1 + c * yC l)
      (by intro he; have : c * y = c * yC l := by linarith
          have := mul_left_cancel₀ hc0.ne' this; linarith)
    have e : (1 + c * y - (1 + c * yC l)) / (1 + c * yC l) = (c / (1 + c * yC l)) * (y - yC l) := by
      field_simp; ring
    rw [e] at htan
    have hq : c / (1 + c * yC l) ≤ m * kapP l := by
      have e2 : c / (1 + c * yC l) = l * m / (m + 1 + m * tC l) := by
        rw [hcyc, hc]; field_simp
      rw [e2]
      unfold kapP
      have ht := H.t_pos
      have h3 : 3 + 2 * tC l ≤ m + 1 + m * tC l := by nlinarith
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hl.le hm0)
      linarith
    have hp1 := mul_le_mul_of_nonneg_left hh hm0
    have hp2 := mul_nonneg (by linarith : (0:ℝ) ≤ y - yC l)
      (by linarith : (0:ℝ) ≤ m * kapP l - c / (1 + c * yC l))
    nlinarith

lemma flat_tan_ydag_lt {h : ℝ → ℝ} (s : ℝ) (hs : ∀ y, s * (y - ydag l) ≤ h y) (m : ℕ) (hm : 1 ≤ m)
    (hT : l ≤ s * (1 + m * Real.exp (fstar l))) (y : ℝ) (h1 : ydag l ≤ y) :
    Real.log (1 + l * m / (m + 1) * y) < fstar l + m * h y := by
  have hl := H.pos
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hm1 : (0:ℝ) < m + 1 := by linarith
  have hyd0 : 0 ≤ ydag l := by linarith [H.ydag_ge]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = l * m / (m + 1) := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcl : c ≤ l := by rw [hc, div_le_iff₀ hm1]; nlinarith
  have hclt : c < l := by rw [hc, div_lt_iff₀ hm1]; nlinarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (fstar l) := ⟨_, rfl⟩
  rw [← hEdef] at hT
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have hE1 : l * ydag l = E - 1 := by rw [hEdef]; exact H.l_ydag
  have hcyd0 : 0 ≤ c * ydag l := mul_nonneg hc0.le hyd0
  have hcy0 : 0 ≤ c * y := mul_nonneg hc0.le (by linarith)
  have htan := log_le_tangent (by linarith : 0 < 1 + c * y) (by linarith : 0 < 1 + c * ydag l)
  have e : (1 + c * y - (1 + c * ydag l)) / (1 + c * ydag l) = (c / (1 + c * ydag l)) * (y - ydag l) := by
    field_simp; ring
  rw [e] at htan
  have hmE : 0 < 1 + m * E := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hm0 hE0.le)
  have hcyd : c * ydag l * (m + 1) = m * (E - 1) := by
    calc c * ydag l * (m + 1) = (l * m / (m + 1) * (m + 1)) * ydag l := by rw [hc]; ring
      _ = l * m * ydag l := by rw [div_mul_cancel₀ _ hm1.ne']
      _ = m * (l * ydag l) := by ring
      _ = m * (E - 1) := by rw [hE1]
  have h1' : 1 + c * ydag l = (1 + m * E) / (m + 1) := by
    rw [eq_div_iff hm1.ne']; linear_combination hcyd
  have hq : c / (1 + c * ydag l) ≤ m * s := by
    have e2 : c / (1 + c * ydag l) = l * m / (1 + m * E) := by
      rw [h1', hc, div_div_div_cancel_right₀ hm1.ne']
    rw [e2, div_le_iff₀ hmE]
    have := mul_le_mul_of_nonneg_left hT hm0
    linarith only [this]
  have hlog0 : Real.log (1 + c * ydag l) < fstar l := by
    rw [← H.log_ydag]
    have : c * ydag l < l * ydag l := mul_lt_mul_of_pos_right hclt (by linarith [H.ydag_ge])
    exact Real.log_lt_log (by linarith) (by linarith)
  have hp1 := mul_le_mul_of_nonneg_left (hs y) hm0
  have hp2 := mul_nonneg (by linarith only [h1] : (0:ℝ) ≤ y - ydag l)
    (by linarith only [hq] : (0:ℝ) ≤ m * s - c / (1 + c * ydag l))
  linarith only [htan, hlog0, hp1, hp2]

lemma flat_T_lt {h : ℝ → ℝ} (Sh : PShape l (s1W l) h) (hs1 : ∀ y, s1W l * (y - ydag l) ≤ h y) (m : ℕ)
    (hm : 1 ≤ m) (hc4 : wW l * (1 + l * m * wW l) ≤ yC l) (y : ℝ) (h1 : ydag l ≤ y) (h2 : y < yC l) :
    Real.log (1 + l * m / (m + 1) * y) < fstar l + m * h y := by
  have hl := H.pos
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hm1 : (0:ℝ) < m + 1 := by linarith
  have hyd0 : 0 ≤ ydag l := by linarith [H.ydag_ge]
  have hyc0 := H.yc_pos
  have hgm := H.gArm_nonneg m hm
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = l * m / (m + 1) := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcyc : c * yC l = tC l * m / (m + 1) := by rw [hc, ← H.l_yc]; ring
  unfold gArm at hgm
  rw [← hcyc] at hgm
  have hlyd := H.log_ydag
  have hld : 0 ≤ l * ydag l := mul_nonneg hl.le hyd0
  have hcy0 : 0 ≤ c * y := mul_nonneg hc0.le (by linarith)
  have hcyc0 : 0 < c * yC l := mul_pos hc0 hyc0
  have hsw := H.s1_w
  have hwdef : wW l = yC l - ydag l := rfl
  have hhe : epsW l + s1W l * (y - yC l) ≤ h y := by
    have e : epsW l + s1W l * (y - yC l) = s1W l * (y - ydag l) := by
      rw [← hsw, hwdef]; ring
    linarith [hs1 y]
  have htan := log_lt_tangent (by linarith : 0 < 1 + c * y) (by linarith : 0 < 1 + c * yC l)
    (by intro he; have : c * y = c * yC l := by linarith
        have := mul_left_cancel₀ hc0.ne' this; linarith)
  have e : (1 + c * y - (1 + c * yC l)) / (1 + c * yC l) = (c / (1 + c * yC l)) * (y - yC l) := by
    field_simp; ring
  rw [e] at htan
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = c / (1 + c * yC l) := ⟨_, rfl⟩
  rw [← hqdef] at htan
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hp1 := mul_le_mul_of_nonneg_left hhe hm0
  have hB : fstar l + m * epsW l - Real.log (1 + c * yC l) + (y - yC l) * (m * s1W l - q)
      < fstar l + m * h y - Real.log (1 + c * y) := by linarith
  rcases le_total (m * s1W l) q with hmq | hmq
  · have := mul_nonneg (by linarith : (0:ℝ) ≤ yC l - y) (by linarith : (0:ℝ) ≤ q - m * s1W l)
    linarith
  · have hlow : -(wW l) * (m * s1W l - q) ≤ (y - yC l) * (m * s1W l - q) :=
      mul_le_mul_of_nonneg_right (by rw [hwdef]; linarith) (by linarith)
    have hmw : m * epsW l = wW l * (m * s1W l) := by rw [← hsw]; ring
    have hkey : Real.log (1 + c * yC l) - fstar l ≤ wW l * q := by
      rw [← hlyd]
      have ht2 := log_le_tangent (by linarith : 0 < 1 + c * yC l) (by linarith : 0 < 1 + l * ydag l)
      have hE' : (c * yC l - l * ydag l) * (1 + c * yC l) ≤ wW l * c * (1 + l * ydag l) := by
        have hyd : ydag l = yC l - wW l := by rw [hwdef]; ring
        rw [hyd, hc]
        have hid : wW l * (l * m / (m + 1)) * (1 + l * (yC l - wW l))
            - (l * m / (m + 1) * yC l - l * (yC l - wW l)) * (1 + l * m / (m + 1) * yC l)
            = l / (m + 1) * (yC l - wW l * (1 + l * m * wW l) + l * m / (m + 1) * yC l ^ 2) := by
          field_simp; ring
        have hnn : 0 ≤ l / (m + 1) * (yC l - wW l * (1 + l * m * wW l) + l * m / (m + 1) * yC l ^ 2) := by
          apply mul_nonneg (by positivity)
          have : 0 ≤ l * m / (m + 1) * yC l ^ 2 := by positivity
          linarith
        linarith
      have hfrac : (1 + c * yC l - (1 + l * ydag l)) / (1 + l * ydag l) ≤ wW l * q := by
        rw [div_le_iff₀ (by linarith)]
        have e2 : wW l * q * (1 + l * ydag l) = wW l * c * (1 + l * ydag l) / (1 + c * yC l) := by
          rw [hqdef]; ring
        rw [e2, le_div_iff₀ (by linarith)]
        linarith
      linarith
    linarith

lemma step_flat_lt {h : ℝ → ℝ} (Sh : PShape l (s1W l) h) (hs1 : ∀ y, s1W l * (y - ydag l) ≤ h y)
    (hS4 : uP l ^ 2 * (uP l - epsW l) ≤ epsW l * Real.exp (fstar l) * (Real.exp (fstar l) - 1))
    (m : ℕ) (hm : 5 ≤ m) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) (hyc : y ≠ yC l) : B0lt l h m y := by
  obtain ⟨hz, harg, hlo, hhi⟩ := H.flat_common_lt Sh m hm y hy0 hy1
  rcases le_total y (ydag l) with h1 | h1
  · exact hlo h1
  rcases lt_or_ge (yC l) y with h2 | h2
  · exact hhi h2
  have h2 : y < yC l := lt_of_le_of_ne h2 hyc
  unfold B0lt; rw [hz, harg]
  have key : Real.log (1 + l * m / (m + 1) * y) < fstar l + m * h y := by
    rcases lt_or_ge (s1W l * (1 + m * Real.exp (fstar l))) l with hT | hT
    · exact H.flat_T_lt Sh hs1 m (by omega) (H.flat_c4 hS4 m hT) y h1 h2
    · exact H.flat_tan_ydag_lt (s1W l) hs1 m (by omega) hT y h1
  linarith

lemma step_flat2_lt {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h) (sa h2 sb : ℝ)
    (hsa : ∀ y, sa * (y - ydag l) ≤ h y) (hsb : ∀ y, h2 + sb * (y - yA l 2) ≤ h y)
    (hd2 : ydag l < yA l 2) (h2c : yA l 2 < yC l)
    (hsa2 : sa * (yA l 2 - ydag l) = h2) (hsbC : h2 + sb * (yC l - yA l 2) = epsW l)
    (hT5 : ∀ m : ℕ, 14 ≤ m → l ≤ sa * (1 + m * Real.exp (fstar l)))
    (hNd : ∀ m : ℕ, m ≤ 13 → m * (Real.exp (fstar l) - 1) ≤ (m + 1) * fstar l)
    (hN2 : ∀ m : ℕ, kapP l * m / (m + 1) ≤ fstar l + m * h2)
    (hNC : ∀ m : ℕ, 5 ≤ m → m ≤ 13 → tC l * m / (m + 1) ≤ fstar l + m * epsW l)
    (m : ℕ) (hm : 5 ≤ m) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) (hyc : y ≠ yC l) : B0lt l h m y := by
  obtain ⟨hz, harg, hlo, hhi⟩ := H.flat_common_lt Sh m hm y hy0 hy1
  rcases le_total y (ydag l) with h1 | h1
  · exact hlo h1
  rcases lt_or_ge (yC l) y with h2' | h2'
  · exact hhi h2'
  unfold B0lt; rw [hz, harg]
  have key : Real.log (1 + l * m / (m + 1) * y) < fstar l + m * h y := by
    rcases le_or_gt 14 m with h14 | h13
    · exact H.flat_tan_ydag_lt sa hsa m (by omega) (hT5 m h14) y h1
    · have hm13 : m ≤ 13 := by omega
      have hl := H.pos
      have hmR : (5:ℝ) ≤ m := by exact_mod_cast hm
      have hm1 : (0:ℝ) < m + 1 := by linarith
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = l * m / (m + 1) := ⟨_, rfl⟩
      rw [← hc]
      have hc0 : 0 < c := by rw [hc]; positivity
      have hlog : Real.log (1 + c * y) < c * y := by
        have hy0' : 0 < y := by linarith [H.ydag_ge]
        have hcy : 0 < c * y := mul_pos hc0 hy0'
        have hpos : 0 < 1 + c * y := by linarith
        have := Real.log_lt_sub_one_of_pos hpos (by linarith)
        linarith
      have hcd : c * ydag l = m * (Real.exp (fstar l) - 1) / (m + 1) := by
        rw [hc, ← H.l_ydag]; field_simp
      have hc2 : c * yA l 2 = kapP l * m / (m + 1) := by
        rw [hc, PB.kap_eq_y2]; field_simp
      have hcC : c * yC l = tC l * m / (m + 1) := by
        rw [hc, ← H.l_yc]; field_simp
      have L1 : c * ydag l ≤ fstar l := by
        rw [hcd, div_le_iff₀ hm1]; have := hNd m hm13; linarith
      have L2 : c * yA l 2 ≤ fstar l + m * h2 := by rw [hc2]; exact hN2 m
      have L3 : c * yC l ≤ fstar l + m * epsW l := by rw [hcC]; exact hNC m hm hm13
      have hm0 : (0:ℝ) ≤ m := by linarith
      rcases le_total y (yA l 2) with hy2 | hy2
      · -- h >= sa (y - ydag); the linear function F + m sa (x - ydag) - c x on [ydag, y2]
        have e1 : fstar l - m * sa * ydag l + (m * sa - c) * ydag l = fstar l - c * ydag l := by ring
        have e2 : fstar l - m * sa * ydag l + (m * sa - c) * yA l 2
            = fstar l + m * (sa * (yA l 2 - ydag l)) - c * yA l 2 := by ring
        have e3 : fstar l - m * sa * ydag l + (m * sa - c) * y = fstar l + m * (sa * (y - ydag l)) - c * y := by ring
        have hlin := lin_nonneg (a := fstar l - m * sa * ydag l) (b := m * sa - c) (p := ydag l) (q := yA l 2)
          (x := y) hd2 (by rw [e1]; linarith) (by rw [e2, hsa2]; linarith) h1 hy2
        rw [e3] at hlin
        have := mul_le_mul_of_nonneg_left (hsa y) hm0
        linarith
      · -- h >= h2 + sb (y - y2); the linear function on [y2, y_ch]
        have e1 : fstar l + m * h2 - m * sb * yA l 2 + (m * sb - c) * yA l 2 = fstar l + m * h2 - c * yA l 2 := by
          ring
        have e2 : fstar l + m * h2 - m * sb * yA l 2 + (m * sb - c) * yC l
            = fstar l + m * (h2 + sb * (yC l - yA l 2)) - c * yC l := by ring
        have e3 : fstar l + m * h2 - m * sb * yA l 2 + (m * sb - c) * y
            = fstar l + m * (h2 + sb * (y - yA l 2)) - c * y := by ring
        have hlin := lin_nonneg (a := fstar l + m * h2 - m * sb * yA l 2) (b := m * sb - c) (p := yA l 2)
          (q := yC l) (x := y) h2c (by rw [e1]; linarith) (by rw [e2, hsbC]; linarith) hy2 h2'
        rw [e3] at hlin
        have := mul_le_mul_of_nonneg_left (hsb y) hm0
        linarith
  linarith

end PB

end

end LeanCherry
