/-
LeanCherry.PBBasic -- part (B) on all of (0, 1 + sqrt 5), basic layer: elementary inequalities for log, the
convex-tangent lemma for -log D - a/D, the slope kappa = lam y(A_2) = lam/(3 + 2t), and the enclosures of the
cherry deficit eps = 2(f* - f_ch) valid on the whole range 0 < lam < 1 + sqrt 5.
-/
import LeanCherry.WinBell

open Real

namespace LeanCherry

noncomputable section

/-! ### elementary inequalities -/

lemma log_le_sinh {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  have h0 : 0 < x := by linarith
  have := Real.self_le_sinh_iff.mpr (Real.log_nonneg hx)
  rwa [Real.sinh_log h0] at this

lemma log_le_two {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : Real.log x ≤ 2 * (x - 1) / (x + 1) := by
  let f : ℝ → ℝ := fun x => Real.log x - 2 * (x - 1) / (x + 1)
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt f (1 / x - 4 / (x + 1) ^ 2) x := by
    intro x hx
    have h1 := Real.hasDerivAt_log hx.ne'
    have h2 : HasDerivAt (fun x : ℝ => 2 * (x - 1)) 2 x := by
      simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
    have h3 : HasDerivAt (fun x : ℝ => x + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h4 := h2.div h3 (by linarith : x + 1 ≠ 0)
    have h5 : HasDerivAt f (x⁻¹ - (2 * (x + 1) - 2 * (x - 1) * 1) / (x + 1) ^ 2) x := h1.sub h4
    refine h5.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hx' : (0:ℝ) < x := hx
      rw [(hd x hx').deriv]
      have e : 1 / x - 4 / (x + 1) ^ 2 = (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by
        field_simp; ring
      rw [e]; positivity
  have := hmono hx0 (by norm_num : (1:ℝ) ∈ Set.Ioi 0) hx1
  simp only [f, Real.log_one] at this
  norm_num at this
  linarith

/-- the convex-tangent lemma: D |-> log D + a/D lies below its tangent at D0 (it is concave there),
    provided 2a <= D0 and a D0 <= D (D0 - a) -/
lemma tan_conv {D D0 a : ℝ} (hD : 0 < D) (hD0 : 0 < D0) (_ha : 0 ≤ a) (h2a : 2 * a ≤ D0)
    (hc : a * D0 ≤ D * (D0 - a)) :
    Real.log D + a / D ≤ Real.log D0 + a / D0 + (1 / D0 - a / D0 ^ 2) * (D - D0) := by
  have hlog : Real.log D = Real.log (D / D0) + Real.log D0 := by
    rw [Real.log_div hD.ne' hD0.ne']; ring
  rw [hlog]
  rcases le_total D0 D with h | h
  · have hx : 1 ≤ D / D0 := by rw [le_div_iff₀ hD0]; linarith
    have hb := log_le_sinh hx
    have e : (D / D0 - (D / D0)⁻¹) / 2 + a / D - a / D0 - (1 / D0 - a / D0 ^ 2) * (D - D0)
        = -((D - D0) ^ 2 * (D0 - 2 * a)) / (2 * D * D0 ^ 2) := by
      field_simp; ring
    have hneg : -((D - D0) ^ 2 * (D0 - 2 * a)) / (2 * D * D0 ^ 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have := mul_nonneg (sq_nonneg (D - D0)) (by linarith : (0:ℝ) ≤ D0 - 2 * a)
      linarith
    linarith
  · have hx0 : 0 < D / D0 := by positivity
    have hx : D / D0 ≤ 1 := by rw [div_le_iff₀ hD0]; linarith
    have hb := log_le_two hx0 hx
    have e : 2 * (D / D0 - 1) / (D / D0 + 1) + a / D - a / D0 - (1 / D0 - a / D0 ^ 2) * (D - D0)
        = -((D0 - D) ^ 2 * (D * (D0 - a) - a * D0)) / (D0 ^ 2 * D * (D + D0)) := by
      field_simp; ring
    have hneg : -((D0 - D) ^ 2 * (D * (D0 - a) - a * D0)) / (D0 ^ 2 * D * (D + D0)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have := mul_nonneg (sq_nonneg (D0 - D)) (by linarith : (0:ℝ) ≤ D * (D0 - a) - a * D0)
      linarith
    linarith

/-! ### the parameters on the whole range -/

/-- the slope of the last piece: kappa = lam y(A_2) = lam/(3 + 2t) -/
def kapP (l : ℝ) : ℝ := l / (3 + 2 * tC l)
/-- u = 1 + t - e^{f*} = lam (y_ch - ydag) -/
def uP (l : ℝ) : ℝ := 1 + tC l - Real.exp (fstar l)
/-- the arm message y(A_m) = 1/(m + 1 + m t) -/
def yA (l m : ℝ) : ℝ := 1 / (m + 1 + m * tC l)
/-- the arm deficit g(A_m) = f* + m eps - log(1 + t m/(m+1)) -/
def gArm (l m : ℝ) : ℝ := fstar l + m * epsW l - Real.log (1 + tC l * m / (m + 1))

/-- the range 0 < lam < 1 + sqrt 5 -/
structure PB (l : ℝ) : Prop where
  pos : 0 < l
  lt : l < 1 + √5

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma hi : l < 3.2361 := by have := sqrt5_bounds.2; linarith [H.lt]
lemma t_pos : 0 < tC l := by unfold tC; have := H.pos; positivity
lemma t_le : tC l ≤ 0.6181 := by
  unfold tC; rw [div_le_iff₀ (by linarith [H.pos])]; linarith [H.hi]
lemma t_lt_one : tC l < 1 := by linarith [H.t_le]
lemma yc_pos : 0 < yC l := by unfold yC; have := H.pos; positivity
lemma l_yc : l * yC l = tC l := ltC H.pos.le
lemma one_sub_t : 1 - tC l = 2 / (2 + l) := by
  unfold tC; have := H.pos; field_simp; ring
lemma l_eq : l = 2 * tC l / (1 - tC l) := by
  rw [H.one_sub_t]; unfold tC; have := H.pos; field_simp; try ring
lemma s_sq : sC l ^ 2 = 1 + l / 2 := sC_sq H.pos.le
lemma s_pos : 0 < sC l := sC_pos H.pos.le
lemma s_ge : 1 + l / 6 ≤ sC l := by
  have h := H.s_sq; have h2 := H.s_pos
  nlinarith [H.hi, H.pos, sq_nonneg (sC l - 1 - l / 6)]
lemma s_gt_one : 1 < sC l := by linarith [H.s_ge, H.pos]
lemma s_sq_t : sC l ^ 2 * (1 - tC l) = 1 := by
  rw [H.s_sq, H.one_sub_t]; have := H.pos; field_simp; try ring
lemma fch_eq : fch l = -(Real.log (1 - tC l)) / 2 := by
  have h := H.s_sq_t
  have h1 : Real.log (sC l ^ 2) + Real.log (1 - tC l) = 0 := by
    rw [← Real.log_mul (by have := H.s_pos; positivity) (by linarith [H.t_lt_one]), h, Real.log_one]
  rw [Real.log_pow] at h1
  unfold fch; push_cast at h1; linarith
lemma kap_pos : 0 < kapP l := by unfold kapP; have := H.pos; have := H.t_pos; positivity
omit H in
lemma kap_eq_y2 : kapP l = l * yA l 2 := by unfold kapP yA; ring_nf
lemma kap_lt : kapP l ≤ 0.77 := by
  unfold kapP; rw [div_le_iff₀ (by linarith [H.t_pos])]
  have ht : tC l * (2 + l) = l := by unfold tC; have := H.pos; field_simp
  nlinarith [H.pos, H.hi, H.t_pos]
lemma kap_lt_one : kapP l < 1 := by linarith [H.kap_lt]

/-- D_inf > 0 on the whole range (lam < 1 + sqrt 5) -/
lemma Dinf_pos : 0 < Dinf l := by
  unfold Dinf fch
  have hs := H.s_pos; have ht := H.t_pos
  rw [sub_pos]
  apply Real.log_lt_log hs
  have h5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hl := H.pos; have hlt := H.lt
  -- (1 + t)^2 > 1 + l/2
  have key : sC l ^ 2 < (1 + tC l) ^ 2 := by
    rw [H.s_sq]
    have e : 1 + tC l = (2 + 2 * l) / (2 + l) := by unfold tC; field_simp; ring
    rw [e, div_pow, lt_div_iff₀ (by positivity)]
    have a1 : 0 < 1 + √5 - l := by linarith
    have a2 : 0 < l - 1 + √5 := by linarith [sqrt5_bounds.1]
    have hq : l ^ 2 - 2 * l - 4 < 0 := by nlinarith [mul_pos a1 a2]
    nlinarith
  nlinarith [sq_nonneg (sC l), sq_nonneg (1 + tC l)]
  
lemma fch_le : fch l ≤ fstar l := fch_le_fstar H.pos H.Dinf_pos
omit H in
lemma fstar_eq : fstar l = fch l + epsW l / 2 := by unfold epsW; ring
lemma eps_lower : Dinf l ^ 2 / (4 * sig l + 3 * Dinf l) < epsW l := by
  have h := fstar_gt H.pos H.Dinf_pos
  have e : Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) = Dinf l ^ 2 / (4 * sig l + 3 * Dinf l) / 2 := by
    field_simp
  unfold epsW; linarith
lemma sig_pos : 0 < sig l := LeanCherry.sig_pos H.pos
lemma eps_pos : 0 < epsW l := by
  have := H.eps_lower; have := H.Dinf_pos; have := H.sig_pos
  have : 0 < Dinf l ^ 2 / (4 * sig l + 3 * Dinf l) := by positivity
  linarith
lemma eps_nonneg : 0 ≤ epsW l := H.eps_pos.le
lemma fch_pos : 0 < fch l := Real.log_pos H.s_gt_one
lemma fstar_pos : 0 < fstar l := by rw [PB.fstar_eq]; linarith [H.fch_pos, H.eps_pos]
lemma exp_fch : Real.exp (fch l) = sC l := Real.exp_log H.s_pos
lemma E_eq : Real.exp (fstar l) = sC l * Real.exp (epsW l / 2) := by
  rw [PB.fstar_eq, Real.exp_add, H.exp_fch]
lemma E_ge : sC l ≤ Real.exp (fstar l) := by
  rw [H.E_eq]; have := Real.one_le_exp (by linarith [H.eps_pos] : 0 ≤ epsW l / 2)
  nlinarith [H.s_pos]
lemma l_ydag : l * ydag l = Real.exp (fstar l) - 1 := by
  unfold ydag; field_simp [H.pos.ne']
lemma log_ydag : Real.log (1 + l * ydag l) = fstar l := by
  rw [H.l_ydag]; simp
lemma ydag_ge : 1 / 6 ≤ ydag l := by
  unfold ydag; rw [le_div_iff₀ H.pos]; linarith [H.E_ge, H.s_ge]
lemma one_t_eq : 1 + tC l = sC l * Real.exp (Dinf l) := by
  unfold Dinf
  rw [Real.exp_sub, H.exp_fch, Real.exp_log (by linarith [H.t_pos])]
  field_simp [H.s_pos.ne']
omit H in
lemma sig_eq : sig l = tC l / (1 + tC l) := rfl

/-- D <= sigma/2, i.e. rho <= 1/2 -/
lemma D_le_half_sig : Dinf l ≤ sig l / 2 := by
  have ht := H.t_pos; have ht1 := H.t_lt_one
  have h1 := log_le_sinh (by linarith : (1:ℝ) ≤ 1 + tC l)
  have h2 := log_le_two (by linarith : (0:ℝ) < 1 - tC l) (by linarith)
  have hD : Dinf l = Real.log (1 + tC l) + Real.log (1 - tC l) / 2 := by
    unfold Dinf; rw [H.fch_eq]; ring
  rw [hD, PB.sig_eq]
  have e1 : ((1 + tC l) - (1 + tC l)⁻¹) / 2 = tC l / (1 + tC l) / 2 + tC l / 2 := by
    field_simp; ring
  have e2 : 2 * (1 - tC l - 1) / (1 - tC l + 1) = -(2 * tC l) / (2 - tC l) := by
    rw [show (1:ℝ) - tC l - 1 = -tC l by ring, show (1:ℝ) - tC l + 1 = 2 - tC l by ring]; ring
  rw [e1] at h1; rw [e2] at h2
  have h3 : tC l / 2 ≤ tC l / (2 - tC l) := div_le_div_of_nonneg_left ht.le (by linarith) (by linarith)
  have e3 : -(2 * tC l) / (2 - tC l) / 2 = -(tC l / (2 - tC l)) := by ring
  have h2' : Real.log (1 - tC l) / 2 ≤ -(tC l / (2 - tC l)) := by
    rw [← e3]; linarith
  linarith

/-- the sharp arm bound behind eps <= D^2/(4 sigma - 2 D) -/
lemma fArm_le_sharp (j : ℕ) : fArm l j ≤ fch l + Dinf l ^ 2 / (8 * sig l - 4 * Dinf l) := by
  rw [fArm_eq H.pos.le]
  have hs := H.sig_pos; have hD := H.Dinf_pos; have hh := H.D_le_half_sig
  have hden : 0 < 8 * sig l - 4 * Dinf l := by linarith
  have hq : 0 ≤ Dinf l ^ 2 / (8 * sig l - 4 * Dinf l) := by positivity
  rcases le_or_gt (Dj l j) 0 with hDj | hDj
  · have : Dj l j / (2 * j + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hDj (by positivity)
    linarith
  · have hle := Dj_le H.pos.le j
    set z : ℝ := 1 / ((j : ℝ) + 1) with hz
    have hz0 : 0 < z := by positivity
    have hj1 : (1:ℝ) ≤ j + 1 := by have : (0:ℝ) ≤ j := by positivity
                                   linarith
    have hz1 : z ≤ 1 := by rw [hz, div_le_one (by linarith)]; exact hj1
    have hsz : sig l / (j + 1) = sig l * z := by rw [hz]; ring
    rw [hsz] at hle
    have hDz : 0 < Dinf l - sig l * z := by linarith
    have h2j : (2 * (j : ℝ) + 1) = (2 - z) / z := by rw [hz]; field_simp; ring
    have h2z : 0 < 2 - z := by linarith
    have hfrac : Dj l j / (2 * j + 1) ≤ z * (Dinf l - sig l * z) / (2 - z) := by
      rw [h2j, div_div_eq_mul_div]
      rw [div_le_div_iff₀ h2z h2z]
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ z * (2 - z))
      nlinarith
    have hzr : z * sig l ≤ Dinf l := by nlinarith
    have hfin : z * (Dinf l - sig l * z) / (2 - z) ≤ Dinf l ^ 2 / (8 * sig l - 4 * Dinf l) := by
      rw [div_le_div_iff₀ h2z hden]
      have hA : 4 * sig l * (z * (Dinf l - sig l * z)) ≤ Dinf l ^ 2 := by
        nlinarith [sq_nonneg (Dinf l - 2 * sig l * z)]
      have hB : 0 ≤ 2 * sig l - Dinf l := by linarith
      -- z (D - s z) (8 s - 4 D) <= D^2 (2 - D/s) * ... <= D^2 (2 - z)
      have hC : z * (Dinf l - sig l * z) * (8 * sig l - 4 * Dinf l) * sig l ≤ Dinf l ^ 2 * (2 * sig l - Dinf l) := by
        nlinarith [mul_le_mul_of_nonneg_right hA hB]
      have hE : Dinf l ^ 2 * (2 * sig l - Dinf l) ≤ Dinf l ^ 2 * (2 - z) * sig l := by
        nlinarith [sq_nonneg (Dinf l)]
      have := le_trans hC hE
      nlinarith
    linarith

lemma eps_le_up : epsW l ≤ Dinf l ^ 2 / (4 * sig l - 2 * Dinf l) := by
  have hf : fstar l ≤ fch l + Dinf l ^ 2 / (8 * sig l - 4 * Dinf l) :=
    csSup_le (armSet_nonempty l) (by rintro x ⟨j, _, rfl⟩; exact H.fArm_le_sharp j)
  have e : Dinf l ^ 2 / (8 * sig l - 4 * Dinf l) = Dinf l ^ 2 / (4 * sig l - 2 * Dinf l) / 2 := by
    rw [div_div]; congr 1; ring
  unfold epsW; linarith

lemma eps_le_D6 : epsW l ≤ Dinf l / 6 := by
  have h := H.eps_le_up
  have hs := H.sig_pos; have hD := H.Dinf_pos; have hh := H.D_le_half_sig
  have : Dinf l ^ 2 / (4 * sig l - 2 * Dinf l) ≤ Dinf l / 6 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  linarith

lemma u_eq : uP l = sC l * (Real.exp (Dinf l) - Real.exp (epsW l / 2)) := by
  unfold uP; rw [H.one_t_eq, H.E_eq]; ring

lemma u_ge : sC l * (Dinf l - epsW l / 2) ≤ uP l := by
  rw [H.u_eq]
  have hd : 0 ≤ Dinf l - epsW l / 2 := by linarith [H.eps_le_D6, H.Dinf_pos]
  have h1 : Real.exp (Dinf l) = Real.exp (epsW l / 2) * Real.exp (Dinf l - epsW l / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (Dinf l - epsW l / 2)
  have h3 : 1 ≤ Real.exp (epsW l / 2) := Real.one_le_exp (by linarith [H.eps_pos])
  have : Dinf l - epsW l / 2 ≤ Real.exp (Dinf l) - Real.exp (epsW l / 2) := by
    rw [h1]; nlinarith
  exact mul_le_mul_of_nonneg_left this H.s_pos.le

lemma u_le : uP l ≤ sC l * Real.exp (Dinf l) * (Dinf l - epsW l / 2) := by
  rw [H.u_eq]
  have h1 : Real.exp (epsW l / 2) = Real.exp (Dinf l) * Real.exp (epsW l / 2 - Dinf l) := by
    rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (epsW l / 2 - Dinf l)
  have h3 := Real.exp_pos (Dinf l)
  have : Real.exp (Dinf l) - Real.exp (epsW l / 2) ≤ Real.exp (Dinf l) * (Dinf l - epsW l / 2) := by
    rw [h1]; nlinarith
  have := mul_le_mul_of_nonneg_left this H.s_pos.le
  linarith

lemma u_pos : 0 < uP l := by
  have h := H.u_ge
  have : 0 < Dinf l - epsW l / 2 := by linarith [H.eps_le_D6, H.Dinf_pos]
  have := mul_pos H.s_pos this
  linarith

lemma w_eq : wW l = uP l / l := by
  unfold wW uP; rw [eq_div_iff H.pos.ne']
  have h1 := H.l_yc; have h2 := H.l_ydag
  linarith [show (yC l - ydag l) * l = l * yC l - l * ydag l by ring]

lemma w_pos : 0 < wW l := by rw [H.w_eq]; exact div_pos H.u_pos H.pos
lemma ydag_lt_yc : ydag l < yC l := by have := H.w_pos; unfold wW at this; linarith
lemma s1_eq : s1W l = l * epsW l / uP l := by
  unfold s1W; rw [H.w_eq]; field_simp [H.pos.ne', H.u_pos.ne']
lemma s1_pos : 0 < s1W l := by rw [H.s1_eq]; have := H.u_pos; have := H.eps_pos; have := H.pos; positivity
lemma s1_w : s1W l * wW l = epsW l := by unfold s1W; field_simp [H.w_pos.ne']

/-- the arm deficit is nonnegative -/
lemma gArm_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ gArm l m := by
  have h := fArm_le_fstar H.pos hm
  rw [fArm_eq H.pos.le] at h
  unfold gArm
  unfold Dj at h
  have hp : (0:ℝ) < 2 * m + 1 := by positivity
  have h' : (Real.log (1 + tC l * m / (m + 1)) - fch l) / (2 * m + 1) ≤ fstar l - fch l := by linarith
  rw [div_le_iff₀ hp] at h'
  unfold epsW
  nlinarith [H.fch_le]

end PB

end

end LeanCherry
