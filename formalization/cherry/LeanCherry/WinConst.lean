/-
LeanCherry.WinConst -- the window, part 2: the constants of the window witness, with closed-form bounds linear or
quadratic in eta = 1 + sqrt5 - l, for 3.22 <= l < 1 + sqrt 5 (derivative-free enclosures).

  eps = 2(f* - f_ch),  ydag = (e^{f*} - 1)/l (so log(1 + l ydag) = f*),  w = y_ch - ydag,  s1 = eps/w,  kap = f*/t.
  0.00162 eta^2 <= eps <= 0.0034 eta^2,  0.02513 eta <= w <= 0.02534 eta,  s1 <= kap,  0.776 <= kap <= 0.8107,
  and the estimate w (1 + l m w) <= y_ch used for 8 <= m below the tangent threshold.
-/
import LeanCherry.WinArms

open Real

namespace LeanCherry

noncomputable section

open Br

def etaW (l : ℝ) : ℝ := 1 + √5 - l
def epsW (l : ℝ) : ℝ := 2 * (fstar l - fch l)
def ydag (l : ℝ) : ℝ := (Real.exp (fstar l) - 1) / l
def wW (l : ℝ) : ℝ := yC l - ydag l
def s1W (l : ℝ) : ℝ := epsW l / wW l
def kapW (l : ℝ) : ℝ := fstar l / tC l

/-- the window hypothesis -/
structure InWin (l : ℝ) : Prop where
  lo : 3.22 ≤ l
  hi : l < 1 + √5

namespace InWin

variable {l : ℝ} (H : InWin l)
include H

lemma pos : 0 < l := by linarith [H.lo]
lemma hi' : l ≤ 3.2361 := by have := sqrt5_bounds.2; linarith [H.hi]
lemma eta_pos : 0 < etaW l := by unfold etaW; linarith [H.hi]
lemma eta_le : etaW l ≤ 0.0161 := by unfold etaW; have := sqrt5_bounds.2; linarith [H.lo]

lemma t_lo : 0.6168 ≤ tC l := by
  unfold tC; rw [le_div_iff₀ (by linarith [H.lo])]; linarith [H.lo]
lemma t_hi : tC l ≤ 0.61804 := by
  unfold tC; rw [div_le_iff₀ (by linarith [H.lo])]; linarith [H.hi']
lemma yc_lo : 0.19098 ≤ yC l := by
  unfold yC; rw [le_div_iff₀ (by linarith [H.lo])]; linarith [H.hi']
lemma yc_hi : yC l ≤ 0.19158 := by
  unfold yC; rw [div_le_iff₀ (by linarith [H.lo])]; linarith [H.lo]
lemma sig_lo : 0.3814 ≤ sig l := by
  unfold sig; have := H.t_lo; rw [le_div_iff₀ (by linarith)]; linarith
lemma sig_hi : sig l ≤ 0.3820 := by
  unfold sig; have := H.t_lo; have := H.t_hi; rw [div_le_iff₀ (by linarith)]; linarith

lemma s_sq : sC l ^ 2 = 1 + l / 2 := sC_sq H.pos.le
lemma s_pos : 0 < sC l := sC_pos H.pos.le
lemma s_lo : 1.6155 ≤ sC l := by
  have := H.s_sq; have := H.s_pos; nlinarith [H.lo]
lemma s_hi : sC l ≤ 1.61804 := by
  have := H.s_sq; have := H.s_pos; nlinarith [H.hi']
lemma s_le_phi : sC l ≤ φ := by
  have h1 := H.s_sq; have h2 := H.s_pos; have h3 := φ_pos
  have h4 : sC l ^ 2 ≤ φ ^ 2 := by
    rw [h1, φ_sq]; unfold φ goldenRatio; linarith [H.hi]
  nlinarith

lemma fch_lo : 0.4796 ≤ fch l := by
  unfold fch
  rw [Real.le_log_iff_exp_le H.s_pos]
  have hb := Real.exp_bound' (x := (0.4796:ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 6, (0.4796:ℝ) ^ m / m.factorial) +
      (0.4796:ℝ) ^ 6 * (6 + 1) / (Nat.factorial 6 * 6) ≤ 1.6155 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith [H.s_lo]
lemma fch_lt_half : fch l < 1 / 2 := by
  have : fch l ≤ L := by
    unfold fch L; exact Real.log_le_log H.s_pos H.s_le_phi
  linarith [L_lt_half]
lemma fch_pos : 0 < fch l := by linarith [H.fch_lo]

/-! ### D_inf, linear in eta -/

def vW (l : ℝ) : ℝ := (1 + tC l) / sC l - 1

lemma key_id : ((1 + tC l) ^ 2 - sC l ^ 2) * (2 * (2 + l) ^ 2) = l * etaW l * (l + √5 - 1) := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : (2 + l) ≠ 0 := by linarith [H.lo]
  have ht : 1 + tC l = (2 + 2 * l) / (2 + l) := by unfold tC; field_simp; ring
  rw [ht, H.s_sq, div_pow]
  have e : ((2 + 2 * l) ^ 2 / (2 + l) ^ 2 - (1 + l / 2)) * (2 * (2 + l) ^ 2) = 2 * (2 + 2 * l) ^ 2 - (2 + l) ^ 3 := by
    field_simp
  rw [e]; unfold etaW
  linear_combination (-l) * h5

lemma v_eq : vW l * ((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2) = l * etaW l * (l + √5 - 1) := by
  rw [← H.key_id]; unfold vW
  have := H.s_pos
  field_simp
  ring

lemma v_le : vW l ≤ 0.0509 * etaW l := by
  have he := H.eta_pos; have hs := H.s_pos
  have h := H.v_eq
  have hnum : l * (l + √5 - 1) ≤ 14.4725 := by
    have := sqrt5_bounds.2; nlinarith [H.hi', H.lo]
  have hden : 54.4968 * 5.2217 ≤ ((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2) := by
    have ha : 3.2323 ≤ 1 + tC l + sC l := by linarith [H.t_lo, H.s_lo]
    have h1 : 5.2217 ≤ (1 + tC l + sC l) * sC l := by
      nlinarith [mul_le_mul ha H.s_lo (by norm_num) (by linarith)]
    have h2 : 54.4968 ≤ 2 * (2 + l) ^ 2 := by nlinarith [H.lo]
    nlinarith [mul_le_mul h1 h2 (by norm_num) (by linarith)]
  by_contra hc
  push_neg at hc
  have : 0.0509 * etaW l * (54.4968 * 5.2217) < vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) := by
    calc 0.0509 * etaW l * (54.4968 * 5.2217) < vW l * (54.4968 * 5.2217) := by
          exact mul_lt_mul_of_pos_right hc (by norm_num)
      _ ≤ vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) :=
          mul_le_mul_of_nonneg_left hden (by nlinarith)
  have hprod : vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) = l * etaW l * (l + √5 - 1) := by
    rw [← mul_assoc]; exact h
  rw [hprod] at this
  nlinarith

lemma v_ge : 0.0499 * etaW l ≤ vW l := by
  have he := H.eta_pos; have hs := H.s_pos
  have h := H.v_eq
  have hnum : 14.348 ≤ l * (l + √5 - 1) := by
    have := sqrt5_bounds.1; nlinarith [H.hi', H.lo]
  have hden : ((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2) ≤ 54.8336 * 5.2362 := by
    have ha : 1 + tC l + sC l ≤ 3.23608 := by linarith [H.t_hi, H.s_hi]
    have ha0 : 0 ≤ 1 + tC l + sC l := by linarith [H.t_lo, H.s_lo]
    have h1 : (1 + tC l + sC l) * sC l ≤ 5.2362 := by
      nlinarith [mul_le_mul ha H.s_hi H.s_pos.le (by norm_num)]
    have h2 : 2 * (2 + l) ^ 2 ≤ 54.8336 := by nlinarith [H.hi', H.lo]
    have h0 : 0 ≤ (1 + tC l + sC l) * sC l := mul_nonneg ha0 H.s_pos.le
    nlinarith [mul_le_mul h1 h2 (by positivity) (by norm_num)]
  have hprod : vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) = l * etaW l * (l + √5 - 1) := by
    rw [← mul_assoc]; exact h
  by_contra hc
  push_neg at hc
  have hvn : vW l < 0.0499 * etaW l := hc
  rcases le_or_gt (vW l) 0 with hv | hv
  · have : vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hv (mul_nonneg (mul_nonneg (by linarith [H.t_lo, H.s_lo]) H.s_pos.le) (by positivity))
    rw [hprod] at this
    nlinarith [H.lo]
  · have : vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) < 0.0499 * etaW l * (54.8336 * 5.2362) := by
      calc vW l * (((1 + tC l + sC l) * sC l) * (2 * (2 + l) ^ 2)) ≤ vW l * (54.8336 * 5.2362) :=
            mul_le_mul_of_nonneg_left hden hv.le
        _ < 0.0499 * etaW l * (54.8336 * 5.2362) := mul_lt_mul_of_pos_right hvn (by norm_num)
    rw [hprod] at this
    nlinarith

lemma v_pos : 0 < vW l := by have := H.v_ge; have := H.eta_pos; nlinarith

lemma Dinf_eq : Dinf l = Real.log (1 + vW l) := by
  have e : 1 + vW l = (1 + tC l) / sC l := by unfold vW; ring
  unfold Dinf fch
  rw [e, Real.log_div (by have := tC_nonneg H.pos.le; exact ne_of_gt (by linarith)) H.s_pos.ne']

lemma Dinf_le : Dinf l ≤ vW l := by
  rw [H.Dinf_eq]; have := Real.log_le_sub_one_of_pos (by linarith [H.v_pos] : 0 < 1 + vW l); linarith

lemma Dinf_ge : vW l / (1 + vW l) ≤ Dinf l := by
  rw [H.Dinf_eq]
  have hp : 0 < 1 + vW l := by linarith [H.v_pos]
  have := Real.one_sub_inv_le_log_of_pos hp
  have e : 1 - (1 + vW l)⁻¹ = vW l / (1 + vW l) := by field_simp; ring
  linarith

lemma Dinf_pos : 0 < Dinf l := lt_of_lt_of_le (by have := H.v_pos; positivity) H.Dinf_ge

/-! ### eps -/

lemma eps_nonneg : 0 ≤ epsW l := by
  unfold epsW; have := fch_le_fstar H.pos H.Dinf_pos; linarith

lemma eps_le : epsW l ≤ 0.0034 * etaW l ^ 2 := by
  have h := fstar_le H.pos
  have hs := H.sig_lo
  have hD0 : 0 ≤ Dinf l := H.Dinf_pos.le
  have hD : Dinf l ≤ 0.0509 * etaW l := le_trans H.Dinf_le H.v_le
  have hsq : Dinf l ^ 2 ≤ (0.0509 * etaW l) ^ 2 := pow_le_pow_left₀ hD0 hD 2
  have : Dinf l ^ 2 / (4 * sig l) ≤ (0.0509 * etaW l) ^ 2 / (4 * 0.3814) := by
    apply div_le_div₀ (by positivity) hsq (by norm_num) (by linarith)
  have e2 : (0.0509 * etaW l) ^ 2 / (4 * 0.3814) ≤ 0.0017 * etaW l ^ 2 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg (etaW l)]
  unfold epsW
  linarith

lemma eps_ge : 0.00162 * etaW l ^ 2 ≤ epsW l := by
  have h := fstar_gt H.pos H.Dinf_pos
  have he := H.eta_pos; have hel := H.eta_le
  have hv := H.v_le; have hvg := H.v_ge
  -- D_inf >= v/(1+v) >= 0.0499 eta/1.001
  have hD1 : 0.0499 * etaW l / 1.001 ≤ Dinf l := by
    refine le_trans ?_ H.Dinf_ge
    rw [div_le_div_iff₀ (by norm_num) (by linarith [H.v_pos])]
    nlinarith
  have hDu : Dinf l ≤ 0.00082 := by nlinarith [H.Dinf_le]
  have hden : 4 * sig l + 3 * Dinf l ≤ 1.53046 := by nlinarith [H.sig_hi]
  have hsq : (0.0499 * etaW l / 1.001) ^ 2 ≤ Dinf l ^ 2 := pow_le_pow_left₀ (by positivity) hD1 2
  have hfrac : (0.0499 * etaW l / 1.001) ^ 2 / (2 * 1.53046) ≤ Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) := by
    apply div_le_div₀ (by positivity) hsq (by have := sig_pos H.pos; have := H.Dinf_pos; positivity) (by linarith)
  have e2 : 0.00081 * etaW l ^ 2 ≤ (0.0499 * etaW l / 1.001) ^ 2 / (2 * 1.53046) := by
    rw [le_div_iff₀ (by norm_num), div_pow]
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [sq_nonneg (etaW l)]
  unfold epsW
  linarith

lemma eps_pos : 0 < epsW l := by have := H.eps_ge; have := H.eta_pos; nlinarith
lemma eps_small : epsW l ≤ 0.000001 := by have := H.eps_le; have := H.eta_le; have := H.eta_pos; nlinarith

lemma fstar_eq : fstar l = fch l + epsW l / 2 := by unfold epsW; ring

/-! ### ydag and w -/

lemma exp_fstar : Real.exp (fstar l) = sC l * Real.exp (epsW l / 2) := by
  rw [H.fstar_eq, Real.exp_add]; unfold fch; rw [Real.exp_log H.s_pos]

lemma exp_half_ge : 1 ≤ Real.exp (epsW l / 2) := Real.one_le_exp (by have := H.eps_nonneg; linarith)
lemma exp_half_le : Real.exp (epsW l / 2) ≤ 1 + epsW l := by
  have he := H.eps_nonneg; have hs := H.eps_small
  have h := Real.exp_bound_div_one_sub_of_interval (x := epsW l / 2) (by linarith) (by linarith)
  have : 1 / (1 - epsW l / 2) ≤ 1 + epsW l := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

lemma log_ydag : Real.log (1 + l * ydag l) = fstar l := by
  unfold ydag
  have : 1 + l * ((Real.exp (fstar l) - 1) / l) = Real.exp (fstar l) := by
    field_simp [H.pos.ne']; ring
  rw [this, Real.log_exp]

lemma ydag_ge : (sC l - 1) / l ≤ ydag l := by
  unfold ydag; rw [H.exp_fstar]
  apply div_le_div_of_nonneg_right _ H.pos.le
  nlinarith [H.exp_half_ge, H.s_pos]

lemma ydag_lo : 0.19 ≤ ydag l := by
  refine le_trans ?_ H.ydag_ge
  rw [le_div_iff₀ H.pos]; linarith [H.s_lo, H.hi']

lemma ldag_ge : sC l - 1 ≤ l * ydag l := by
  have := H.ydag_ge
  rw [div_le_iff₀ H.pos] at this; linarith

def wPlus (l : ℝ) : ℝ := yC l - (sC l - 1) / l

lemma wPlus_id : wPlus l * (2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l)) = etaW l * (sC l + φ - 1) := by
  have hs := H.s_pos; have hp := φ_pos
  have hsq := H.s_sq
  have hl : l = 2 * (sC l ^ 2 - 1) := by linarith
  have hy : yC l = 1 / (2 * sC l ^ 2) := by unfold yC; rw [hsq]; field_simp
  have hs1 : sC l - 1 ≠ 0 := by have := H.s_lo; intro h; linarith
  have he : etaW l = 2 * (φ ^ 2 - sC l ^ 2) := by
    unfold etaW; rw [φ_sq, hsq]; unfold φ goldenRatio; ring
  unfold wPlus
  rw [hy, he]
  have hl' : (sC l - 1) / l = 1 / (2 * (sC l + 1)) := by
    rw [div_eq_div_iff H.pos.ne' (by positivity)]; linear_combination 2 * hsq
  rw [hl']
  have e1 : (1 / (2 * sC l ^ 2) - 1 / (2 * (sC l + 1))) * (2 * sC l ^ 2 * (sC l + 1)) = sC l + 1 - sC l ^ 2 := by
    field_simp
  rw [e1]
  linear_combination (-2 * (φ + sC l)) * φ_sq

lemma wPlus_le : wPlus l ≤ 0.02534 * etaW l := by
  have hs := H.s_pos; have hp := φ_pos; have he := H.eta_pos
  have h := H.wPlus_id
  have hprod : wPlus l * ((2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l))) = etaW l * (sC l + φ - 1) := by
    rw [← mul_assoc]; exact h
  obtain ⟨p1, p2⟩ := φ_bounds
  have hnum : sC l + φ - 1 ≤ 2.2361 := by linarith [H.s_hi]
  have hden : 88.28 ≤ (2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l)) := by
    have h1 : 2.60984 ≤ sC l ^ 2 := by rw [H.s_sq]; linarith [H.lo]
    have h2 : 2.6155 ≤ sC l + 1 := by linarith [H.s_lo]
    have h3 : 3.2335 ≤ φ + sC l := by linarith [H.s_lo]
    have h4 : 2.60984 * 2.6155 ≤ sC l ^ 2 * (sC l + 1) := mul_le_mul h1 h2 (by norm_num) (by positivity)
    have h5 : 2.60984 * 2.6155 * 3.2335 ≤ sC l ^ 2 * (sC l + 1) * (φ + sC l) :=
      mul_le_mul h4 h3 (by norm_num) (by positivity)
    nlinarith
  by_contra hc; push_neg at hc
  have : 0.02534 * etaW l * 88.28 < wPlus l * ((2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l))) := by
    calc 0.02534 * etaW l * 88.28 < wPlus l * 88.28 := mul_lt_mul_of_pos_right hc (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by nlinarith)
  rw [hprod] at this
  nlinarith

lemma wPlus_ge : 0.02516 * etaW l ≤ wPlus l := by
  have hs := H.s_pos; have hp := φ_pos; have he := H.eta_pos
  have h := H.wPlus_id
  have hprod : wPlus l * ((2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l))) = etaW l * (sC l + φ - 1) := by
    rw [← mul_assoc]; exact h
  obtain ⟨p1, p2⟩ := φ_bounds
  have hnum : 2.2335 ≤ sC l + φ - 1 := by linarith [H.s_lo]
  have hden : (2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l)) ≤ 88.73 := by
    have h1 : sC l ^ 2 ≤ 2.61805 := by rw [H.s_sq]; linarith [H.hi']
    have h2 : sC l + 1 ≤ 2.61804 := by linarith [H.s_hi]
    have h3 : φ + sC l ≤ 3.2361 := by linarith [H.s_hi]
    have h4 : sC l ^ 2 * (sC l + 1) ≤ 2.61805 * 2.61804 := mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h5 : sC l ^ 2 * (sC l + 1) * (φ + sC l) ≤ 2.61805 * 2.61804 * 3.2361 :=
      mul_le_mul h4 h3 (by positivity) (by norm_num)
    nlinarith
  by_contra hc; push_neg at hc
  rcases le_or_gt (wPlus l) 0 with hw | hw
  · have : wPlus l * ((2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hw (by positivity)
    rw [hprod] at this; nlinarith
  · have : wPlus l * ((2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l))) < 0.02516 * etaW l * 88.73 := by
      calc wPlus l * ((2 * sC l ^ 2 * (sC l + 1)) * (2 * (φ + sC l))) ≤ wPlus l * 88.73 :=
            mul_le_mul_of_nonneg_left hden hw.le
        _ < _ := mul_lt_mul_of_pos_right hc (by norm_num)
    rw [hprod] at this; nlinarith

lemma w_eq : wW l = wPlus l - sC l * (Real.exp (epsW l / 2) - 1) / l := by
  unfold wW wPlus ydag; rw [H.exp_fstar]; field_simp; ring

lemma w_le : wW l ≤ 0.02534 * etaW l := by
  rw [H.w_eq]
  have : 0 ≤ sC l * (Real.exp (epsW l / 2) - 1) / l := by
    have := H.exp_half_ge; have := H.s_pos; have := H.pos; positivity
  linarith [H.wPlus_le]

lemma w_ge : 0.02513 * etaW l ≤ wW l := by
  rw [H.w_eq]
  have he := H.eta_pos; have hel := H.eta_le
  have h1 : sC l * (Real.exp (epsW l / 2) - 1) / l ≤ 1.61804 * epsW l / 3.22 := by
    have hx : Real.exp (epsW l / 2) - 1 ≤ epsW l := by linarith [H.exp_half_le]
    have hx0 : 0 ≤ Real.exp (epsW l / 2) - 1 := by linarith [H.exp_half_ge]
    have hm : sC l * (Real.exp (epsW l / 2) - 1) ≤ 1.61804 * epsW l := mul_le_mul H.s_hi hx hx0 (by norm_num)
    calc sC l * (Real.exp (epsW l / 2) - 1) / l ≤ 1.61804 * epsW l / l := div_le_div_of_nonneg_right hm H.pos.le
      _ ≤ 1.61804 * epsW l / 3.22 :=
          div_le_div_of_nonneg_left (by have := H.eps_nonneg; positivity) (by norm_num) H.lo
  have h2 : 1.61804 * epsW l / 3.22 ≤ 0.00003 * etaW l := by
    have h3 := H.eps_le
    have h4 : etaW l ^ 2 ≤ 0.0161 * etaW l := by nlinarith [H.eta_le, H.eta_pos]
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith [H.wPlus_ge]

lemma w_pos : 0 < wW l := by have := H.w_ge; have := H.eta_pos; nlinarith

lemma ydag_lt_yc : ydag l < yC l := by have := H.w_pos; unfold wW at this; linarith

/-! ### s1 and kap -/

lemma s1_nonneg : 0 ≤ s1W l := div_nonneg H.eps_nonneg H.w_pos.le
lemma s1_le : s1W l ≤ 0.0022 := by
  unfold s1W
  rw [div_le_iff₀ H.w_pos]
  have := H.eps_le; have := H.w_ge; have := H.eta_pos; have := H.eta_le
  nlinarith
lemma s1_w : s1W l * wW l = epsW l := by unfold s1W; field_simp [H.w_pos.ne']

lemma fstar_pos : 0 < fstar l := by rw [H.fstar_eq]; have := H.fch_pos; have := H.eps_nonneg; linarith

lemma kap_lo : 0.776 ≤ kapW l := by
  unfold kapW
  rw [le_div_iff₀ (by linarith [H.t_lo])]
  rw [H.fstar_eq]; have := H.eps_nonneg
  nlinarith [H.fch_lo, H.t_hi]
lemma kap_hi : kapW l ≤ 0.8107 := by
  unfold kapW
  rw [div_le_iff₀ (by linarith [H.t_lo])]
  rw [H.fstar_eq]
  nlinarith [H.fch_lt_half, H.t_lo, H.eps_small]
lemma kap_pos : 0 < kapW l := by linarith [H.kap_lo]
lemma s1_le_kap : s1W l ≤ kapW l := by linarith [H.s1_le, H.kap_lo]

/-- kap = (f*/2)/(1/2 - y_ch) -/
lemma kap_eq : kapW l = (fstar l / 2) / (1 / 2 - yC l) := by
  unfold kapW tC yC
  have : (2 + l) ≠ 0 := by linarith [H.lo]
  field_simp
  ring

/-- y_ch in terms of the identity l y_ch = t -/
lemma l_yc : l * yC l = tC l := ltC H.pos.le

/-- the estimate for large m: if m s1 (1 + l ydag) < l, then w (1 + l m w) <= y_ch -/
lemma c4 {m : ℝ} (hm0 : 0 ≤ m) (hm : m * s1W l * (1 + l * ydag l) < l) :
    wW l * (1 + l * m * wW l) ≤ yC l := by
  have hw := H.w_pos; have he := H.eps_pos; have hel := H.eta_le; have hep := H.eta_pos
  have hld : 0.6155 ≤ l * ydag l := by have := H.ldag_ge; linarith [H.s_lo]
  -- m < l w/(eps (1 + l ydag))
  have hA : 0 < 1 + l * ydag l := by linarith
  have hm' : m * epsW l * (1 + l * ydag l) < l * wW l := by
    have : m * s1W l * (1 + l * ydag l) * wW l < l * wW l := mul_lt_mul_of_pos_right hm hw
    have e : m * s1W l * (1 + l * ydag l) * wW l = m * epsW l * (1 + l * ydag l) := by
      rw [← H.s1_w]; ring
    linarith
  -- l m w <= l^2 w^2/(eps (1 + l ydag)) <= 2.6
  have hB : l * m * wW l * (epsW l * (1 + l * ydag l)) ≤ l ^ 2 * wW l ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm'.le (mul_nonneg H.pos.le H.w_pos.le)
    nlinarith
  have hC : l ^ 2 * wW l ^ 2 ≤ 2.6 * (epsW l * (1 + l * ydag l)) := by
    have h1 : l ^ 2 ≤ 10.4724 := by nlinarith [H.hi', H.lo]
    have h2 : wW l ^ 2 ≤ (0.02534 * etaW l) ^ 2 := pow_le_pow_left₀ hw.le H.w_le 2
    have h3 : 0.00162 * etaW l ^ 2 * 1.6155 ≤ epsW l * (1 + l * ydag l) := by
      have := H.eps_ge; nlinarith
    nlinarith
  have hD : l * m * wW l ≤ 2.6 := by
    have hpos : 0 < epsW l * (1 + l * ydag l) := by positivity
    by_contra hc; push_neg at hc
    have : 2.6 * (epsW l * (1 + l * ydag l)) < l * m * wW l * (epsW l * (1 + l * ydag l)) :=
      mul_lt_mul_of_pos_right hc hpos
    linarith
  have hwsmall : wW l ≤ 0.000408 := by nlinarith [H.w_le]
  nlinarith [H.yc_lo]

end InWin

end

end LeanCherry
