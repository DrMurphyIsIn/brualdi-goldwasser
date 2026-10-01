/-
LeanCherry.WinExtBox -- the window extended to [2.35, 3.22], part 2: `WFacts l` for every l in a box [a, b] from rational enclosures.

All hypotheses of `wfacts_of_box` are inequalities between explicit real numerals (checked by norm_num at each
instantiation); the two Taylor-sum conditions pin log s between Fl and Fh.  Enclosures used
(t = l/(2+l), y_ch = 1/(2+l), s = sqrt(1+l/2), sigma = l/(2+2l)):
  Dinf = log((1+t)/s) in [Dl, Vh]  (1 - x^{-1} <= log x <= x - 1);
  eps = 2(f* - f_ch) in [epsl, epsh]  (fstar_gt / fstar_le of WinArms);
  ydag = (s e^{eps/2} - 1)/l, e^{eps/2} <= 1 + eps;  w = y_ch - ydag;  s1 = eps/w;  kap = f*/t;
  log(Dy/(m+1)) - F0 <= Dy/((m+1) s) - 1 + eps/2  and  e^{-F0} = e^{eps/2}/s <= (1 + epsh)/sl  (no further logs).
The proof is split into small lemmas, each with a minimal context.
-/
import LeanCherry.WinExtCore

open Real

namespace LeanCherry

noncomputable section

namespace Box

/-! ### elementary enclosures -/

lemma t_lo {a l : ℝ} (ha : 0 < a) (h : a ≤ l) : a / (2 + a) ≤ tC l := by
  unfold tC; rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma t_hi {b l : ℝ} (hl : 0 < l) (h : l ≤ b) : tC l ≤ b / (2 + b) := by
  unfold tC; rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma yc_lo {b l : ℝ} (hl : 0 < l) (h : l ≤ b) : 1 / (2 + b) ≤ yC l := by
  unfold yC; exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma yc_hi {a l : ℝ} (ha : 0 < a) (h : a ≤ l) : yC l ≤ 1 / (2 + a) := by
  unfold yC; exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma s_lo {a sl l : ℝ} (hl : 0 < l) (h : a ≤ l) (hsl0 : 0 < sl) (hsl : sl ^ 2 ≤ 1 + a / 2) : sl ≤ sC l := by
  have hs2 := sC_sq hl.le; have hs0 := sC_pos hl.le
  have : sl ^ 2 ≤ sC l ^ 2 := by rw [hs2]; linarith
  exact (pow_le_pow_iff_left₀ hsl0.le hs0.le (by norm_num)).mp this

lemma s_hi {b sh l : ℝ} (hl : 0 < l) (h : l ≤ b) (hsh0 : 0 < sh) (hsh : 1 + b / 2 ≤ sh ^ 2) : sC l ≤ sh := by
  have hs2 := sC_sq hl.le; have hs0 := sC_pos hl.le
  have : sC l ^ 2 ≤ sh ^ 2 := by rw [hs2]; linarith
  exact (pow_le_pow_iff_left₀ hs0.le hsh0.le (by norm_num)).mp this

lemma s_ge_one {l : ℝ} (hl : 0 < l) : 1 ≤ sC l := by
  have hs2 := sC_sq hl.le; have hs0 := sC_pos hl.le
  nlinarith

lemma fch_lo {Fl l : ℝ} (hl : 0 < l) (hFl0 : 0 ≤ Fl) (hFl1 : Fl ≤ 1) {sl : ℝ} (hsl' : sl ≤ sC l)
    (hFl : 1 + Fl + Fl ^ 2 / 2 + Fl ^ 3 / 6 + Fl ^ 4 / 24 + Fl ^ 5 / 120 + Fl ^ 6 * 7 / 4320 ≤ sl) : Fl ≤ fch l := by
  unfold fch
  rw [Real.le_log_iff_exp_le (sC_pos hl.le)]
  have hb := Real.exp_bound' hFl0 hFl1 (n := 6) (by norm_num)
  have e : (∑ m ∈ Finset.range 6, Fl ^ m / m.factorial) + Fl ^ 6 * (6 + 1) / (Nat.factorial 6 * 6)
      = 1 + Fl + Fl ^ 2 / 2 + Fl ^ 3 / 6 + Fl ^ 4 / 24 + Fl ^ 5 / 120 + Fl ^ 6 * 7 / 4320 := by
    simp [Finset.sum_range_succ, Nat.factorial]; try ring
  push_cast at hb
  linarith

lemma fch_hi {Fh l : ℝ} (hl : 0 < l) (hFh0 : 0 ≤ Fh) {sh : ℝ} (hsh' : sC l ≤ sh)
    (hFh : sh ≤ 1 + Fh + Fh ^ 2 / 2 + Fh ^ 3 / 6 + Fh ^ 4 / 24 + Fh ^ 5 / 120 + Fh ^ 6 / 720 + Fh ^ 7 / 5040) :
    fch l ≤ Fh := by
  unfold fch
  rw [Real.log_le_iff_le_exp (sC_pos hl.le)]
  have hb := Real.sum_le_exp_of_nonneg hFh0 8
  have e : ∑ i ∈ Finset.range 8, Fh ^ i / (i.factorial : ℝ)
      = 1 + Fh + Fh ^ 2 / 2 + Fh ^ 3 / 6 + Fh ^ 4 / 24 + Fh ^ 5 / 120 + Fh ^ 6 / 720 + Fh ^ 7 / 5040 := by
    simp [Finset.sum_range_succ, Nat.factorial]; try ring
  rw [e] at hb
  linarith

lemma sig_eq {l : ℝ} (hl : 0 < l) : sig l = l / (2 + 2 * l) := by
  unfold sig tC; field_simp; ring

lemma sig_lo {a σl l : ℝ} (ha : 0 < a) (h : a ≤ l) (hσl : σl ≤ a / (2 + 2 * a)) : σl ≤ sig l := by
  rw [sig_eq (by linarith)]; refine le_trans hσl ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma sig_hi {b σh l : ℝ} (hl : 0 < l) (h : l ≤ b) (hσh : b / (2 + 2 * b) ≤ σh) : sig l ≤ σh := by
  rw [sig_eq hl]; refine le_trans ?_ hσh
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma Dinf_eq {l : ℝ} (hl : 0 < l) : Dinf l = Real.log ((1 + tC l) / sC l) := by
  have h1t : 0 < 1 + tC l := by have := tC_nonneg hl.le; linarith
  unfold Dinf fch; rw [Real.log_div h1t.ne' (sC_pos hl.le).ne']

lemma Dinf_hi {b sl Vh l : ℝ} (hl : 0 < l) (h : l ≤ b) (hsl' : sl ≤ sC l) (hsl0 : 0 < sl)
    (hVh : 1 + b / (2 + b) ≤ (1 + Vh) * sl) : Dinf l ≤ Vh := by
  rw [Dinf_eq hl]
  have hs0 := sC_pos hl.le
  have hth := t_hi hl h
  have h1t : 0 < 1 + tC l := by have := tC_nonneg hl.le; linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos h1t hs0)
  have hV : 0 ≤ 1 + Vh := by
    by_contra hc; push_neg at hc
    have : (1 + Vh) * sl < 0 := mul_neg_of_neg_of_pos hc hsl0
    have : 0 ≤ b / (2 + b) := by have := (le_trans hl.le h); positivity
    linarith
  have : (1 + tC l) / sC l ≤ 1 + Vh := by
    rw [div_le_iff₀ hs0]
    nlinarith [mul_le_mul_of_nonneg_left hsl' hV]
  linarith [hlog]

lemma Dinf_lo {a sh Dl l : ℝ} (ha : 0 < a) (h : a ≤ l) (hsh' : sC l ≤ sh) (hsh0 : 0 < sh)
    (hDl : Dl ≤ 1 - sh / (1 + a / (2 + a))) : Dl ≤ Dinf l := by
  have hl : 0 < l := by linarith
  rw [Dinf_eq hl]
  have hs0 := sC_pos hl.le
  have htl := t_lo ha h
  have h1t : 0 < 1 + tC l := by have := tC_nonneg hl.le; linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos h1t hs0)
  have e : ((1 + tC l) / sC l)⁻¹ = sC l / (1 + tC l) := by rw [inv_div]
  rw [e] at h
  have ha0 : 0 < 1 + a / (2 + a) := by positivity
  have : sC l / (1 + tC l) ≤ sh / (1 + a / (2 + a)) := by
    rw [div_le_div_iff₀ h1t ha0]
    nlinarith [mul_le_mul hsh' (by linarith : 1 + a / (2 + a) ≤ 1 + tC l) ha0.le hsh0.le]
  linarith

lemma eps_hi {σl Vh εh l : ℝ} (hl : 0 < l) (hD0 : 0 < Dinf l) (hDh : Dinf l ≤ Vh) (hσl0 : 0 < σl)
    (hsigl : σl ≤ sig l) (hεh : Vh ^ 2 / (2 * σl) ≤ εh) : epsW l ≤ εh := by
  have hfs := fstar_le hl
  unfold epsW
  have hsq : Dinf l ^ 2 ≤ Vh ^ 2 := pow_le_pow_left₀ hD0.le hDh 2
  have : Dinf l ^ 2 / (4 * sig l) ≤ Vh ^ 2 / (4 * σl) :=
    div_le_div₀ (by positivity) hsq (by positivity) (by linarith)
  have e : Vh ^ 2 / (4 * σl) * 2 = Vh ^ 2 / (2 * σl) := by field_simp; try ring
  linarith

lemma eps_lo {σh Dl εl l : ℝ} (hl : 0 < l) (hDl0 : 0 < Dl) (hDl' : Dl ≤ Dinf l) (hsigh : sig l ≤ σh)
    (hεl : εl ≤ Dl ^ 2 / (4 * σh + 3 * Dl)) : εl ≤ epsW l := by
  have hD0 : 0 < Dinf l := lt_of_lt_of_le hDl0 hDl'
  have hsig0 := sig_pos hl
  have hσh0 : 0 < σh := lt_of_lt_of_le hsig0 hsigh
  have hfs := fstar_gt hl hD0
  unfold epsW
  have hmono : Dl ^ 2 / (4 * σh + 3 * Dl) ≤ Dinf l ^ 2 / (4 * sig l + 3 * Dinf l) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Dl ^ 2 ≤ Dinf l ^ 2 := pow_le_pow_left₀ hDl0.le hDl' 2
    have h2 : Dl ^ 2 * sig l ≤ Dinf l ^ 2 * σh := mul_le_mul h1 hsigh hsig0.le (by positivity)
    have h3 : Dl ^ 2 * Dinf l ≤ Dinf l ^ 2 * Dl := by
      have := mul_le_mul_of_nonneg_left hDl' (mul_nonneg hDl0.le hD0.le)
      nlinarith
    nlinarith
  have e : Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) * 2 = Dinf l ^ 2 / (4 * sig l + 3 * Dinf l) := by
    field_simp; try ring
  linarith

lemma exp_half {l : ℝ} (h0 : 0 ≤ epsW l) (h1 : epsW l ≤ 1) :
    1 ≤ Real.exp (epsW l / 2) ∧ Real.exp (epsW l / 2) ≤ 1 + epsW l := by
  refine ⟨Real.one_le_exp (by linarith), ?_⟩
  have h := Real.exp_bound_div_one_sub_of_interval (x := epsW l / 2) (by linarith) (by linarith)
  have : 1 / (1 - epsW l / 2) ≤ 1 + epsW l := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

lemma exp_fstar {l : ℝ} (hl : 0 < l) : Real.exp (fstar l) = sC l * Real.exp (epsW l / 2) := by
  have e : fstar l = fch l + epsW l / 2 := by unfold epsW; ring
  rw [e, Real.exp_add]; unfold fch; rw [Real.exp_log (sC_pos hl.le)]

lemma ydag_eq {l : ℝ} (hl : 0 < l) : ydag l = (sC l * Real.exp (epsW l / 2) - 1) / l := by
  unfold ydag; rw [exp_fstar hl]

lemma ydag_lo {b sl ydl l : ℝ} (hl : 0 < l) (h : l ≤ b) (hsl' : sl ≤ sC l) (he1 : 1 ≤ Real.exp (epsW l / 2))
    (hydl : ydl ≤ (sl - 1) / b) (hydl9 : 1 / 9 ≤ ydl) : ydl ≤ ydag l := by
  rw [ydag_eq hl]; refine le_trans hydl ?_
  have hb : 0 < b := by linarith
  have hsl1 : 0 ≤ sl - 1 := by
    have h1 : (1:ℝ) / 9 ≤ (sl - 1) / b := le_trans hydl9 hydl
    have : 0 < (sl - 1) / b := by linarith
    rcases (div_pos_iff.mp this) with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hs0 := sC_pos hl.le
  have : sl - 1 ≤ sC l * Real.exp (epsW l / 2) - 1 := by nlinarith
  rw [div_le_div_iff₀ hb hl]
  nlinarith

lemma ydag_hi {a sh εh ydh l : ℝ} (ha : 0 < a) (h : a ≤ l) (hsh' : sC l ≤ sh) (hsh0 : 0 < sh)
    (he1 : 1 ≤ Real.exp (epsW l / 2)) (he2 : Real.exp (epsW l / 2) ≤ 1 + εh)
    (hydh : (sh * (1 + εh) - 1) / a ≤ ydh) : ydag l ≤ ydh := by
  have hl : 0 < l := by linarith
  rw [ydag_eq hl]; refine le_trans ?_ hydh
  have hs0 := sC_pos hl.le
  have hs1 := s_ge_one hl
  have hnum : sC l * Real.exp (epsW l / 2) - 1 ≤ sh * (1 + εh) - 1 := by
    have := mul_le_mul hsh' he2 (by linarith) hsh0.le
    linarith
  have hnum0 : 0 ≤ sC l * Real.exp (epsW l / 2) - 1 := by nlinarith
  rw [div_le_div_iff₀ hl ha]
  nlinarith

lemma kap_lo {b Fl εl κl l : ℝ} (hl : 0 < l) (h : l ≤ b) (hfl : Fl ≤ fch l) (hel : εl ≤ epsW l)
    (hFl0 : 0 ≤ Fl) (hεl0 : 0 ≤ εl) (hκl : κl ≤ (Fl + εl / 2) / (b / (2 + b))) : κl ≤ kapW l := by
  have hth := t_hi hl h
  have ht0 : 0 < tC l := by unfold tC; positivity
  have hb0 : 0 < b / (2 + b) := by have : 0 < b := by linarith
                                   positivity
  unfold kapW
  refine le_trans hκl ?_
  rw [div_le_div_iff₀ hb0 ht0]
  have hnum : Fl + εl / 2 ≤ fstar l := by have : fstar l = fch l + epsW l / 2 := by unfold epsW; ring
                                          linarith
  have hn0 : 0 ≤ Fl + εl / 2 := by linarith
  nlinarith [mul_le_mul hnum hth ht0.le (by linarith : 0 ≤ fstar l)]

lemma kap_hi {a Fh εh κh l : ℝ} (ha : 0 < a) (h : a ≤ l) (hfh : fch l ≤ Fh) (heh : epsW l ≤ εh)
    (hf0 : 0 ≤ fstar l) (hκh : (Fh + εh / 2) / (a / (2 + a)) ≤ κh) : kapW l ≤ κh := by
  have hl : 0 < l := by linarith
  have htl := t_lo ha h
  have ht0 : 0 < tC l := by unfold tC; positivity
  have ha0 : 0 < a / (2 + a) := by positivity
  unfold kapW
  refine le_trans ?_ hκh
  rw [div_le_div_iff₀ ht0 ha0]
  have hnum : fstar l ≤ Fh + εh / 2 := by have : fstar l = fch l + epsW l / 2 := by unfold epsW; ring
                                          linarith
  nlinarith [mul_le_mul hnum htl ha0.le (by linarith)]

lemma F0_eq {l : ℝ} : InWin.F0W l = fch l - epsW l / 2 := by unfold InWin.F0W epsW; ring

lemma E_hi {sl εh l : ℝ} (hl : 0 < l) (hsl' : sl ≤ sC l) (hsl0 : 0 < sl) (he2 : Real.exp (epsW l / 2) ≤ 1 + εh) :
    Real.exp (-InWin.F0W l) ≤ (1 + εh) / sl := by
  have hs0 := sC_pos hl.le
  rw [F0_eq, show -(fch l - epsW l / 2) = epsW l / 2 + (-fch l) by ring, Real.exp_add, Real.exp_neg]
  unfold fch; rw [Real.exp_log hs0]
  rw [mul_inv_le_iff₀ hs0]
  have hεh : 0 ≤ 1 + εh := le_trans (by linarith [Real.exp_pos (epsW l / 2)]) he2
  have h2 : (1 + εh) / sl * sl ≤ (1 + εh) / sl * sC l := mul_le_mul_of_nonneg_left hsl' (by positivity)
  have e : (1 + εh) / sl * sl = 1 + εh := by field_simp
  linarith

lemma logC {l m : ℝ} (hl : 0 < l) (hm : 1 ≤ m) :
    Real.log ((m + 1 + l * m * yC l) / (m + 1)) - InWin.F0W l
      ≤ (m + 1 + m * tC l) / ((m + 1) * sC l) - 1 + epsW l / 2 := by
  rw [F0_eq]
  have hlt : l * m * yC l = m * tC l := by rw [← ltC hl.le]; ring
  rw [hlt]
  have hs0 := sC_pos hl.le
  have ht0 := tC_nonneg hl.le
  have hpos : 0 < (m + 1 + m * tC l) / (m + 1) := by
    have : 0 ≤ m * tC l := mul_nonneg (by linarith) ht0
    exact div_pos (by linarith) (by linarith)
  have h := Real.log_le_sub_one_of_pos (div_pos hpos hs0)
  rw [Real.log_div hpos.ne' hs0.ne'] at h
  unfold fch
  have e : (m + 1 + m * tC l) / (m + 1) / sC l = (m + 1 + m * tC l) / ((m + 1) * sC l) := by rw [div_div]
  rw [e] at h
  linarith

lemma ratio_le {b sl l m : ℝ} (hl : 0 < l) (h : l ≤ b) (hm : 1 ≤ m) (hsl0 : 0 < sl) (hsl' : sl ≤ sC l) :
    (m + 1 + m * tC l) / ((m + 1) * sC l) ≤ (m + 1 + m * (b / (2 + b))) / ((m + 1) * sl) := by
  have hth := t_hi hl h
  have ht0 := tC_nonneg hl.le
  have hb0 : 0 ≤ b / (2 + b) := by have : 0 < b := by linarith
                                   positivity
  apply div_le_div₀ (by nlinarith) (by nlinarith) (by positivity)
  exact mul_le_mul_of_nonneg_left hsl' (by linarith)

lemma ratio_mono7 {b sl m : ℝ} (hb : 0 < b) (hsl0 : 0 < sl) (hm : 1 ≤ m) (hm7 : m ≤ 7) :
    (m + 1 + m * (b / (2 + b))) / ((m + 1) * sl) ≤ (8 + 7 * (b / (2 + b))) / (8 * sl) := by
  have hb0 : 0 ≤ b / (2 + b) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 7 - m)) hsl0.le]

lemma Dy_eq {l m : ℝ} (hl : 0 < l) : m + 1 + l * m * yC l = m + 1 + m * tC l := by
  rw [← ltC hl.le]; ring

lemma q1_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : 0 ≤ 1 / (2 + a / (2 + a)) - 1 / (2 + b) := by
  have : a / (2 + a) ≤ b := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2 + a / (2 + a)) (by linarith : 2 + a / (2 + a) ≤ 2 + b)
  linarith

end Box

end

end LeanCherry
