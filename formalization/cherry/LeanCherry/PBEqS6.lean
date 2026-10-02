/-
LeanCherry.PBEqS6 -- the equality clause of part (B), part 4: the arm A_2 is never best (f_2 < f_3), and (S6) holds
strictly for both witnesses: h(y_2) < g(A_2).
-/
import LeanCherry.PBEqFlat
import LeanCherry.PBW2

open Real

namespace LeanCherry

noncomputable section

/-- (1 + 2t/3)^7 (1 - t) < (1 + 3t/4)^5 for 0 < t -/
lemma poly_f2_f3 {t : ℝ} (ht : 0 < t) : (1 + 2 * t / 3) ^ 7 * (1 - t) < (1 + 3 * t / 4) ^ 5 := by
  have e : (1 + 3 * t / 4) ^ 5 - (1 + 2 * t / 3) ^ 7 * (1 - t) =
      t * (1/12 + 23/24 * t + 2749/864 * t ^ 2 + 104485/20736 * t ^ 3 + 121249/27648 * t ^ 4
        + 1568/729 * t ^ 5 + 1216/2187 * t ^ 6 + 128/2187 * t ^ 7) := by ring
  have : 0 < t * (1/12 + 23/24 * t + 2749/864 * t ^ 2 + 104485/20736 * t ^ 3 + 121249/27648 * t ^ 4
        + 1568/729 * t ^ 5 + 1216/2187 * t ^ 6 + 128/2187 * t ^ 7) := by positivity
  linarith

namespace PB

variable {l : ℝ} (H : PB l)
include H

/-- g(A_m) = (2m + 1)(f* - f_m) -/
lemma gArm_eq (m : ℕ) : gArm l m = (2 * m + 1) * (fstar l - fArm l m) := by
  rw [fArm_eq H.pos.le]; unfold gArm Dj epsW
  have : (0:ℝ) < 2 * m + 1 := by positivity
  field_simp; ring

/-- f_2 < f_3 -/
lemma fArm2_lt_fArm3 : fArm l 2 < fArm l 3 := by
  have ht := H.t_pos; have ht1 := H.t_lt_one
  rw [fArm_eq H.pos.le, fArm_eq H.pos.le]
  unfold Dj
  rw [H.fch_eq]
  push_cast
  have hp := poly_f2_f3 ht
  have h1 : 0 < 1 + 2 * tC l / 3 := by positivity
  have h2 : 0 < 1 - tC l := by linarith
  have hlog := Real.log_lt_log (by positivity) hp
  rw [Real.log_mul (by positivity) h2.ne', Real.log_pow, Real.log_pow] at hlog
  have e2 : 1 + tC l * 2 / (2 + 1) = 1 + 2 * tC l / 3 := by ring
  have e3 : 1 + tC l * 3 / (3 + 1) = 1 + 3 * tC l / 4 := by ring
  rw [e2, e3]
  push_cast at hlog
  linarith

/-- the arm A_2 is never best: g(A_2) > 0 -/
lemma gArm2_pos : 0 < gArm l 2 := by
  have h := H.gArm_eq 2
  push_cast at h
  rw [h]
  have := H.fArm2_lt_fArm3
  have := fArm_le_fstar H.pos (by norm_num : 1 ≤ 3)
  nlinarith

lemma S6_lt (h3 : 3 / 20 ≤ l) : hS l (yA l 2) < gArm l 2 := by
  have hl := H.pos; have ht := H.t_pos; have ht1 := H.t_lt_one
  have ht43 : 3 / 43 ≤ tC l := by
    unfold tC; rw [le_div_iff₀ (by linarith)]; linarith
  have hc := PBC.cert_S6_full (tC l) ht43 H.t_le'
  rw [H.kap_eq, H.D2_eq] at hc
  have heps := H.eps_pos; have hu := H.u_pos; have hk := H.kap_pos; have hsk := H.s1_le_kap
  have hs1 := H.s1_pos
  -- g(A_2) = (5/2) eps - D(2)
  have hg : gArm l 2 = 5 / 2 * epsW l - Dj l 2 := by
    unfold gArm Dj; rw [PB.fstar_eq]; push_cast
    have : tC l * 2 / (2 + 1) = tC l * 2 / (2 + 1) := rfl
    ring
  have hlyc := H.l_yc
  have hly2 : l * yA l 2 = kapP l := (PB.kap_eq_y2).symm
  have hyc2 : yC l = (1 - tC l) / 2 := by rw [H.one_sub_t]; unfold yC; field_simp
  have hy2 : yA l 2 = 1 / (3 + 2 * tC l) := by unfold yA; ring
  have hshape := H.hS_shape
  -- for t <= 1/2 (y2 <= y_ch): h(y2) = max(0, eps - eps delta/u)
  have low : tC l ≤ 1 / 2 → 0 < epsW l * (3 / 2 + (tC l - kapP l) / uP l) - Dj l 2 → hS l (yA l 2) < gArm l 2 := by
    intro htt hpsi
    have hy2c : yA l 2 ≤ yC l := by
      rw [hy2, hyc2, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hval : s1W l * (yA l 2 - ydag l) = epsW l - epsW l * (tC l - kapP l) / uP l := by
      rw [H.s1_eq]
      have e1 : yA l 2 - ydag l = (yC l - ydag l) - (yC l - yA l 2) := by ring
      rw [e1]
      have hw : yC l - ydag l = uP l / l := H.w_eq
      rw [hw]
      have e2 : l * (yC l - yA l 2) = tC l - kapP l := by linarith
      have hu0 := H.u_pos.ne'
      have hl0 := H.pos.ne'
      calc l * epsW l / uP l * (uP l / l - (yC l - yA l 2))
          = epsW l - epsW l * (l * (yC l - yA l 2)) / uP l := by field_simp
        _ = epsW l - epsW l * (tC l - kapP l) / uP l := by rw [e2]
    have hgA0 := H.gArm2_pos
    unfold hS
    apply max_lt
    · apply max_lt hgA0
      rw [hval, hg]
      have : epsW l * (3 / 2 + (tC l - kapP l) / uP l) = 3 / 2 * epsW l + epsW l * (tC l - kapP l) / uP l := by
        ring
      linarith
    · have h1 : kapP l * (yA l 2 - yC l) ≤ s1W l * (yA l 2 - yC l) :=
        mul_le_mul_of_nonpos_right hsk (by linarith)
      have h2 : epsW l + s1W l * (yA l 2 - yC l) = s1W l * (yA l 2 - ydag l) := by
        have hsw := H.s1_w; unfold wW at hsw; linear_combination -hsw
      rw [hval] at h2
      rw [hg]
      have : epsW l * (3 / 2 + (tC l - kapP l) / uP l) = 3 / 2 * epsW l + epsW l * (tC l - kapP l) / uP l := by
        ring
      linarith
  rcases hc with ⟨hle, hu3, hpsi3⟩ | ⟨_, hle, hall⟩ | ⟨hge, hc8⟩
  · -- C7 regime: Psi is increasing in F, and F >= f3
    apply low (by linarith)
    rw [H.E3_eq] at hu3
    rw [H.E3_eq, H.eps3_eq] at hpsi3
    have hf3 := H.fArm3_le
    have hEle : Real.exp (fArm l 3) ≤ Real.exp (fstar l) := Real.exp_le_exp.mpr hf3
    have huu : uP l ≤ 1 + tC l - Real.exp (fArm l 3) := by unfold uP; linarith
    have hd : 0 ≤ tC l - kapP l := by rw [← H.kap_eq]; exact PBC.delta_nonneg ht.le (by linarith)
    have he3 : 2 * (fArm l 3 - fch l) ≤ epsW l := by unfold epsW; linarith
    have := psi_mono (D2 := Dj l 2) hd hu huu he3 heps.le
    linarith
  · -- the hand step on [t_D2, 1/2]
    apply low hle
    have := hall (epsW l) (Real.exp (fstar l)) heps (by unfold uP at hu; linarith)
    unfold uP; exact this
  · -- C8 regime, lam >= 2: h(y2) = eps + kappa (y2 - y_ch)
    have hup := hshape.up (yA l 2)
    have hy2c : yC l ≤ yA l 2 := by
      rw [hy2, hyc2, div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    rw [max_eq_right (by linarith)] at hup
    rw [hg]
    rw [← hy2, ← hyc2] at hc8
    linarith

end PB

namespace W2Facts

variable {l : ℝ} (W : W2Facts l)
include W

lemma hg2_lt : hT l (yA l 2) < gArm l 2 := by
  have H := W.base
  have hg0 := H.gArm2_pos
  have hss := W.sa_le_sb; have hsk := W.sb_le_kap
  have e1 := W.sa_mul; have e2 := W.sb_mul
  have h2c := W.y2_lt_yc
  have hh : h2v l = 4 / 5 * gArm l 2 := rfl
  unfold hT
  refine max_lt (max_lt (max_lt (by linarith) (by linarith)) (by linarith)) ?_
  have : kapP l * (yA l 2 - yC l) ≤ sbW l * (yA l 2 - yC l) := mul_le_mul_of_nonpos_right hsk (by linarith)
  nlinarith

end W2Facts

end

end LeanCherry
