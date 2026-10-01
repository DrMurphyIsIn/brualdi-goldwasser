/-
LeanCherry.WinExtAssemble -- the window extended to [2.35, 3.22], part 3: `WFacts l` on a box from a bundled set of numeral inequalities.

`BoxP` is the list of box constants, `BoxOK p` the list of inequalities between them (each closed by norm_num at
instantiation).  Bundling keeps every tactic context small.
-/
import LeanCherry.WinExtBox

open Real

namespace LeanCherry

noncomputable section

/-- the constants of one box -/
structure BoxP where
  a : ℝ
  b : ℝ
  sl : ℝ
  sh : ℝ
  Fl : ℝ
  Fh : ℝ
  Vh : ℝ
  Dl : ℝ
  σl : ℝ
  σh : ℝ
  εh : ℝ
  εl : ℝ
  ydl : ℝ
  ydh : ℝ
  wl : ℝ
  wh : ℝ
  κl : ℝ
  κh : ℝ
  Gh : ℝ

/-- the inequalities a box must satisfy -/
structure BoxOK (p : BoxP) : Prop where
  ha : 0 < p.a
  hab : p.a ≤ p.b
  hsl0 : 0 < p.sl
  hsl : p.sl ^ 2 ≤ 1 + p.a / 2
  hsh0 : 0 < p.sh
  hsh : 1 + p.b / 2 ≤ p.sh ^ 2
  hFl0 : 0 ≤ p.Fl
  hFl1 : p.Fl ≤ 1
  hFl : 1 + p.Fl + p.Fl ^ 2 / 2 + p.Fl ^ 3 / 6 + p.Fl ^ 4 / 24 + p.Fl ^ 5 / 120 + p.Fl ^ 6 * 7 / 4320 ≤ p.sl
  hFh0 : 0 ≤ p.Fh
  hFh : p.sh ≤ 1 + p.Fh + p.Fh ^ 2 / 2 + p.Fh ^ 3 / 6 + p.Fh ^ 4 / 24 + p.Fh ^ 5 / 120 + p.Fh ^ 6 / 720
    + p.Fh ^ 7 / 5040
  hVh : 1 + p.b / (2 + p.b) ≤ (1 + p.Vh) * p.sl
  hDl0 : 0 < p.Dl
  hDl : p.Dl ≤ 1 - p.sh / (1 + p.a / (2 + p.a))
  hσl0 : 0 < p.σl
  hσl : p.σl ≤ p.a / (2 + 2 * p.a)
  hσh : p.b / (2 + 2 * p.b) ≤ p.σh
  hεh : p.Vh ^ 2 / (2 * p.σl) ≤ p.εh
  hεh1 : p.εh ≤ 1
  hεl0 : 0 < p.εl
  hεl : p.εl ≤ p.Dl ^ 2 / (4 * p.σh + 3 * p.Dl)
  hydl : p.ydl ≤ (p.sl - 1) / p.b
  hydl9 : 1 / 9 ≤ p.ydl
  hydh : (p.sh * (1 + p.εh) - 1) / p.a ≤ p.ydh
  hwl0 : 0 < p.wl
  hwl : p.wl ≤ 1 / (2 + p.b) - p.ydh
  hwh : 1 / (2 + p.a) - p.ydl ≤ p.wh
  hκl0 : 0 < p.κl
  hκl : p.κl ≤ (p.Fl + p.εl / 2) / (p.b / (2 + p.b))
  hκh : (p.Fh + p.εh / 2) / (p.a / (2 + p.a)) ≤ p.κh
  hκh2 : p.κh ≤ 2
  hs1 : p.εh / p.wl ≤ p.κl
  h8 : p.b ≤ 8 * p.κl
  hcube : 1 + 2 * p.b / 3 ≤ p.sl * (1 + p.a / 2)
  hG : p.b ^ 2 * p.wh ^ 2 / (p.εl * (1 + p.a * p.ydl)) ≤ p.Gh
  hc4 : p.wh * (1 + p.Gh) ≤ 1 / (2 + p.b)
  hC0 : (8 + 7 * (p.b / (2 + p.b))) / (8 * p.sl) - 1 + p.εh / 2 ≤ 0
  hC1 : (2 + p.b / (2 + p.b)) / (2 * p.sl) - 1 + p.εh / 2 + p.κh * (1 / (2 + p.a / (2 + p.a)) - 1 / (2 + p.b)) ≤ 0
  hq2 : 0 ≤ 1 / (3 + 2 * (p.a / (2 + p.a))) - 1 / (2 + p.b)
  hC2 : (3 + 2 * (p.b / (2 + p.b))) / (3 * p.sl) - 1 + p.εh / 2
    + p.κh * (1 / (3 + 2 * (p.a / (2 + p.a))) - 1 / (2 + p.b)) ≤ 0
  hq3 : 1 / (4 + 3 * (p.a / (2 + p.a))) ≤ 1 / (2 + p.b)
  hslope : p.b / (3 + 2 * (p.a / (2 + p.a))) ≤ p.κl
  h0a : (1 + p.b / (2 + p.b) / 2) * ((1 + p.εh) / p.sl) ≤ 1
  h0b : (1 + p.b / 4) * ((1 + p.εh) / p.sl) - 1 ≤ p.κl * (1 / 2 - 1 / (2 + p.a))
  haa : (1 + p.b / (2 + p.b) / 2) * ((1 + p.εh) / p.sl) - 1 + p.κh * (1 / (2 + p.a / (2 + p.a)) - 1 / (2 + p.b)) ≤ 0
  habq : (1 + p.b / 4) * ((1 + p.εh) / p.sl) - 1 + p.κl * (1 / (2 + p.a / 2) - 1 / 2) ≤ 0

/-- the derived enclosures at a point l of the box -/
structure BoxEnc (p : BoxP) (l : ℝ) : Prop where
  hl : 0 < l
  htl : p.a / (2 + p.a) ≤ tC l
  hth : tC l ≤ p.b / (2 + p.b)
  hycl : 1 / (2 + p.b) ≤ yC l
  hych : yC l ≤ 1 / (2 + p.a)
  hsl' : p.sl ≤ sC l
  hD0 : 0 < Dinf l
  hel : p.εl ≤ epsW l
  heh : epsW l ≤ p.εh
  he0 : 0 < epsW l
  he2 : Real.exp (epsW l / 2) ≤ 1 + p.εh
  hydlo : p.ydl ≤ ydag l
  hw_lo : p.wl ≤ wW l
  hw_hi : wW l ≤ p.wh
  hkl : p.κl ≤ kapW l
  hkh : kapW l ≤ p.κh
  hs1le : s1W l ≤ p.εh / p.wl
  hE : Real.exp (-InWin.F0W l) ≤ (1 + p.εh) / p.sl

namespace BoxOK

variable {p : BoxP} (H : BoxOK p)
include H

theorem enc {l : ℝ} (hl1 : p.a ≤ l) (hl2 : l ≤ p.b) : BoxEnc p l := by
  have hl : 0 < l := lt_of_lt_of_le H.ha hl1
  have hsl' := Box.s_lo hl hl1 H.hsl0 H.hsl
  have hsh' := Box.s_hi hl hl2 H.hsh0 H.hsh
  have hfl := Box.fch_lo hl H.hFl0 H.hFl1 hsl' H.hFl
  have hfh := Box.fch_hi hl H.hFh0 hsh' H.hFh
  have hsigl := Box.sig_lo H.ha hl1 H.hσl
  have hsigh := Box.sig_hi hl hl2 H.hσh
  have hDh := Box.Dinf_hi hl hl2 hsl' H.hsl0 H.hVh
  have hDl' := Box.Dinf_lo H.ha hl1 hsh' H.hsh0 H.hDl
  have hD0 : 0 < Dinf l := lt_of_lt_of_le H.hDl0 hDl'
  have heh := Box.eps_hi hl hD0 hDh H.hσl0 hsigl H.hεh
  have hel := Box.eps_lo hl H.hDl0 hDl' hsigh H.hεl
  have he0 : 0 < epsW l := lt_of_lt_of_le H.hεl0 hel
  obtain ⟨he1, he2⟩ := Box.exp_half he0.le (le_trans heh H.hεh1)
  have he2' : Real.exp (epsW l / 2) ≤ 1 + p.εh := le_trans he2 (by linarith)
  have hydlo := Box.ydag_lo hl hl2 hsl' he1 H.hydl H.hydl9
  have hydhi := Box.ydag_hi H.ha hl1 hsh' H.hsh0 he1 he2' H.hydh
  have hycl := Box.yc_lo hl hl2
  have hych := Box.yc_hi H.ha hl1
  have hw_lo : p.wl ≤ wW l := by unfold wW; linarith [H.hwl]
  have hw_hi : wW l ≤ p.wh := by unfold wW; linarith [H.hwh]
  have hs1' : 1 ≤ sC l := Box.s_ge_one hl
  have hfs0 : 0 ≤ fstar l := by
    have : fstar l = fch l + epsW l / 2 := by unfold epsW; ring
    have : 0 ≤ fch l := Real.log_nonneg hs1'
    linarith
  have hkl := Box.kap_lo hl hl2 hfl hel H.hFl0 H.hεl0.le H.hκl
  have hkh := Box.kap_hi H.ha hl1 hfh heh hfs0 H.hκh
  have hw0 : 0 < wW l := lt_of_lt_of_le H.hwl0 hw_lo
  have hs1le : s1W l ≤ p.εh / p.wl := by
    unfold s1W; exact div_le_div₀ (by linarith [H.hεh]) heh H.hwl0 hw_lo
  exact ⟨hl, Box.t_lo H.ha hl1, Box.t_hi hl hl2, hycl, hych, hsl', hD0, hel, heh, he0, he2', hydlo, hw_lo, hw_hi,
    hkl, hkh, hs1le, Box.E_hi hl hsl' H.hsl0 he2'⟩

end BoxOK

namespace BoxEnc

variable {p : BoxP} {l : ℝ} (E : BoxEnc p l)
include E

lemma hk0 (H : BoxOK p) : 0 < kapW l := lt_of_lt_of_le H.hκl0 E.hkl
lemma hw0 (H : BoxOK p) : 0 < wW l := lt_of_lt_of_le H.hwl0 E.hw_lo
lemma hlyc : l * yC l = tC l := ltC E.hl.le
lemma hyc0 : 0 < yC l := by unfold yC; have := E.hl; positivity

/-- C0 for real m in [1, 7] -/
lemma C0m (H : BoxOK p) (hl2 : l ≤ p.b) (m : ℝ) (hm : 1 ≤ m) (hm7 : m ≤ 7) :
    Real.log ((m + 1 + l * m * yC l) / (m + 1)) ≤ InWin.F0W l := by
  have h1 := Box.logC E.hl hm (l := l)
  have h2 := Box.ratio_le E.hl hl2 hm H.hsl0 E.hsl'
  have h3 := Box.ratio_mono7 (lt_of_lt_of_le H.ha H.hab) H.hsl0 hm hm7
  have h4 := H.hC0
  have heh := E.heh
  linarith

lemma eps_le_h (_H : BoxOK p) : epsW l ≤ p.εh := E.heh

/-- C_m for real m in [1, 7] -/
lemma Cm (H : BoxOK p) (hl2 : l ≤ p.b) (m : ℝ) (hm : 1 ≤ m) (hm7 : m ≤ 7) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) :
    Real.log ((m + 1 + l * m * yC l) / (m + 1)) - InWin.F0W l + kapW l * (1 / (m + 1 + l * m * yC l) - yC l) ≤ 0 := by
  have hL := Box.logC E.hl hm (l := l)
  have hR := Box.ratio_le E.hl hl2 hm H.hsl0 E.hsl'
  have heh := E.eps_le_h H
  have hk0 := E.hk0 H
  have hkh := E.hkh
  have htl := E.htl
  have hycl := E.hycl
  rw [Box.Dy_eq E.hl] at hL ⊢
  rcases hcase with h1 | h2 | h3
  · subst h1
    have hq : 1 / (1 + 1 + 1 * tC l) - yC l ≤ 1 / (2 + p.a / (2 + p.a)) - 1 / (2 + p.b) := by
      have : 1 / (1 + 1 + 1 * tC l) ≤ 1 / (2 + p.a / (2 + p.a)) :=
        one_div_le_one_div_of_le (by have := H.ha; positivity) (by linarith)
      linarith
    have hq1 := Box.q1_nonneg H.ha H.hab
    have hk := mul_le_mul_of_nonneg_left hq hk0.le
    have hk2 := mul_le_mul_of_nonneg_right hkh hq1
    have e1 : ((1:ℝ) + 1 + 1 * (p.b / (2 + p.b))) / ((1 + 1) * p.sl) = (2 + p.b / (2 + p.b)) / (2 * p.sl) := by ring
    rw [e1] at hR
    have := H.hC1
    linarith
  · subst h2
    have hq : 1 / (2 + 1 + 2 * tC l) - yC l ≤ 1 / (3 + 2 * (p.a / (2 + p.a))) - 1 / (2 + p.b) := by
      have : 1 / (2 + 1 + 2 * tC l) ≤ 1 / (3 + 2 * (p.a / (2 + p.a))) :=
        one_div_le_one_div_of_le (by have := H.ha; positivity) (by linarith)
      linarith
    have hk := mul_le_mul_of_nonneg_left hq hk0.le
    have hk2 := mul_le_mul_of_nonneg_right hkh H.hq2
    have e1 : ((2:ℝ) + 1 + 2 * (p.b / (2 + p.b))) / ((2 + 1) * p.sl) = (3 + 2 * (p.b / (2 + p.b))) / (3 * p.sl) := by
      ring
    rw [e1] at hR
    have := H.hC2
    linarith
  · have hq : 1 / (m + 1 + m * tC l) - yC l ≤ 0 := by
      have h4 : 4 + 3 * (p.a / (2 + p.a)) ≤ m + 1 + m * tC l := by
        have := mul_le_mul h3 htl (by have := H.ha; positivity) (by linarith)
        linarith
      have := one_div_le_one_div_of_le (by have := H.ha; positivity) h4
      have := H.hq3
      linarith
    have h5 := mul_nonpos_of_nonneg_of_nonpos hk0.le hq
    have h6 := Box.ratio_mono7 (lt_of_lt_of_le H.ha H.hab) H.hsl0 (by linarith) hm7 (sl := p.sl)
    have := H.hC0
    linarith

lemma slopem (H : BoxOK p) (hl2 : l ≤ p.b) (m : ℝ) (hm : 2 ≤ m) : l / (m + 1 + l * m * yC l) ≤ kapW l := by
  rw [Box.Dy_eq E.hl]
  have htl := E.htl
  have h3 : 3 + 2 * (p.a / (2 + p.a)) ≤ m + 1 + m * tC l := by
    have := mul_le_mul hm htl (by have := H.ha; positivity) (by linarith)
    linarith
  have : l / (m + 1 + m * tC l) ≤ p.b / (3 + 2 * (p.a / (2 + p.a))) :=
    div_le_div₀ (by linarith [H.ha, H.hab]) hl2 (by have := H.ha; positivity) h3
  have := H.hslope
  have := E.hkl
  linarith

/-- the four m = 1, region A conditions -/
lemma m1 (H : BoxOK p) (hl1 : p.a ≤ l) (hl2 : l ≤ p.b) :
    ((1 + l * yC l / 2) * Real.exp (-InWin.F0W l) - 1 ≤ 0) ∧
    ((1 + l / 4) * Real.exp (-InWin.F0W l) - 1 ≤ kapW l * (1 / 2 - yC l)) ∧
    ((1 + l * yC l / 2) * Real.exp (-InWin.F0W l) - 1 + kapW l * (1 / (2 + l * yC l) - yC l) ≤ 0) ∧
    ((1 + l / 4) * Real.exp (-InWin.F0W l) - 1 + kapW l * (1 / (2 + l / 2) - yC l) - kapW l * (1 / 2 - yC l) ≤ 0) := by
  have hE := E.hE
  have hE0 : 0 < Real.exp (-InWin.F0W l) := Real.exp_pos _
  have hk0 := E.hk0 H
  have hkl := E.hkl
  have hkh := E.hkh
  have hth := E.hth
  have htl := E.htl
  have hycl := E.hycl
  have hych := E.hych
  have hlyc := E.hlyc
  have hεh0 : 0 ≤ p.εh := by have := E.heh; have := E.he0; linarith
  have hfac0 : 0 ≤ (1 + p.εh) / p.sl := by have := H.hsl0; positivity
  have hE1 : (1 + tC l / 2) * Real.exp (-InWin.F0W l) ≤ (1 + p.b / (2 + p.b) / 2) * ((1 + p.εh) / p.sl) :=
    mul_le_mul (by linarith) hE hE0.le (by have hb : 0 < p.b := lt_of_lt_of_le H.ha H.hab; positivity)
  have hE2 : (1 + l / 4) * Real.exp (-InWin.F0W l) ≤ (1 + p.b / 4) * ((1 + p.εh) / p.sl) :=
    mul_le_mul (by linarith) hE hE0.le (by have hb : 0 < p.b := lt_of_lt_of_le H.ha H.hab; positivity)
  have hlyc2 : l * yC l / 2 = tC l / 2 := by rw [hlyc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlyc2]; have := H.h0a; linarith
  · have hq0 : 0 ≤ 1 / 2 - 1 / (2 + p.a) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [H.ha])
    have h2 : p.κl * (1 / 2 - 1 / (2 + p.a)) ≤ kapW l * (1 / 2 - yC l) :=
      mul_le_mul hkl (by linarith) hq0 hk0.le
    have := H.h0b
    linarith
  · rw [hlyc]
    have hq : 1 / (2 + tC l) - yC l ≤ 1 / (2 + p.a / (2 + p.a)) - 1 / (2 + p.b) := by
      have : 1 / (2 + tC l) ≤ 1 / (2 + p.a / (2 + p.a)) :=
        one_div_le_one_div_of_le (by have := H.ha; positivity) (by linarith)
      linarith
    have hq1 := Box.q1_nonneg H.ha H.hab
    have hk := mul_le_mul_of_nonneg_left hq hk0.le
    have hk2 := mul_le_mul_of_nonneg_right hkh hq1
    have := H.haa
    linarith
  · have hq : 1 / (2 + l / 2) - 1 / 2 ≤ 1 / (2 + p.a / 2) - 1 / 2 := by
      have := one_div_le_one_div_of_le (by linarith [H.ha] : (0:ℝ) < 2 + p.a / 2) (by linarith : 2 + p.a / 2 ≤ 2 + l / 2)
      linarith
    have hqn : 1 / (2 + p.a / 2) - 1 / 2 ≤ 0 := by
      rw [sub_nonpos]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [H.ha])
    have hk : kapW l * (1 / (2 + l / 2) - 1 / 2) ≤ p.κl * (1 / (2 + p.a / 2) - 1 / 2) := by
      have := mul_le_mul_of_nonneg_left hq hk0.le
      have := mul_le_mul_of_nonpos_right hkl hqn
      linarith
    have e : kapW l * (1 / (2 + l / 2) - yC l) - kapW l * (1 / 2 - yC l) = kapW l * (1 / (2 + l / 2) - 1 / 2) := by ring
    have := H.habq
    linarith

/-- the (C4) estimate -/
lemma c4 (H : BoxOK p) (hl1 : p.a ≤ l) (hl2 : l ≤ p.b) (m : ℝ) (hm0 : 0 ≤ m)
    (hm : m * s1W l * (1 + l * ydag l) < l) : wW l * (1 + l * m * wW l) ≤ yC l := by
  have hl := E.hl
  have hw0 := E.hw0 H
  have hw_hi := E.hw_hi
  have hydlo := E.hydlo
  have hel := E.hel
  have he0 := E.he0
  have hy0 : 0 ≤ p.ydl := le_trans (by norm_num) H.hydl9
  have hyd0 : 0 ≤ ydag l := le_trans hy0 hydlo
  have hA : 0 < 1 + l * ydag l := by have := mul_nonneg hl.le hyd0; linarith
  have hm' : m * epsW l * (1 + l * ydag l) < l * wW l := by
    have : m * s1W l * (1 + l * ydag l) * wW l < l * wW l := mul_lt_mul_of_pos_right hm hw0
    have e : m * s1W l * (1 + l * ydag l) * wW l = m * epsW l * (1 + l * ydag l) := by
      unfold s1W; field_simp [hw0.ne']
    linarith
  have hB : l * m * wW l * (epsW l * (1 + l * ydag l)) ≤ l ^ 2 * wW l ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm'.le (mul_nonneg hl.le hw0.le)
    nlinarith
  have hden : p.εl * (1 + p.a * p.ydl) ≤ epsW l * (1 + l * ydag l) := by
    have : p.a * p.ydl ≤ l * ydag l := mul_le_mul hl1 hydlo hy0 hl.le
    exact mul_le_mul hel (by linarith) (by have := H.ha; positivity) he0.le
  have hden0 : 0 < p.εl * (1 + p.a * p.ydl) := by have := H.hεl0; have := H.ha; positivity
  have hnum : l ^ 2 * wW l ^ 2 ≤ p.b ^ 2 * p.wh ^ 2 := by
    have h1 : l ^ 2 ≤ p.b ^ 2 := pow_le_pow_left₀ hl.le hl2 2
    have h2 : wW l ^ 2 ≤ p.wh ^ 2 := pow_le_pow_left₀ hw0.le hw_hi 2
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hlmw0 : 0 ≤ l * m * wW l := by positivity
  have hlmw : l * m * wW l ≤ p.Gh := by
    have hX : l * m * wW l * (p.εl * (1 + p.a * p.ydl)) ≤ p.b ^ 2 * p.wh ^ 2 := by
      have : l * m * wW l * (p.εl * (1 + p.a * p.ydl)) ≤ l * m * wW l * (epsW l * (1 + l * ydag l)) :=
        mul_le_mul_of_nonneg_left hden hlmw0
      linarith
    have : l * m * wW l ≤ p.b ^ 2 * p.wh ^ 2 / (p.εl * (1 + p.a * p.ydl)) := by
      rw [le_div_iff₀ hden0]; exact hX
    have := H.hG
    linarith
  have : wW l * (1 + l * m * wW l) ≤ p.wh * (1 + p.Gh) :=
    mul_le_mul hw_hi (by linarith) (by linarith) (by linarith)
  have := H.hc4
  have := E.hycl
  linarith

end BoxEnc

/-- `WFacts l` for every l in a box satisfying `BoxOK` -/
theorem BoxOK.wfacts {p : BoxP} (H : BoxOK p) {l : ℝ} (hl1 : p.a ≤ l) (hl2 : l ≤ p.b) : WFacts l := by
  have E := H.enc hl1 hl2
  have hk0 := E.hk0 H
  refine
    { pos := E.hl
      Dinf_pos := E.hD0
      w_pos := E.hw0 H
      s1_le_kap := le_trans E.hs1le (le_trans H.hs1 E.hkl)
      kap_le_two := le_trans E.hkh H.hκh2
      ydag_ge := le_trans H.hydl9 E.hydlo
      l_le_8kap := le_trans hl2 (le_trans H.h8 (by have := E.hkl; linarith))
      s_cube := ?_
      c4 := fun m hm0 hm => E.c4 H hl1 hl2 m hm0 hm
      c2 := ?_ }
  · have hs2 := sC_sq E.hl.le
    have hs0 := sC_pos E.hl.le
    have : sC l ^ 3 = sC l * (1 + l / 2) := by rw [← hs2]; ring
    rw [this]
    have h1 := mul_le_mul E.hsl' (by linarith : 1 + p.a / 2 ≤ 1 + l / 2) (by linarith [H.ha]) hs0.le
    have := H.hcube
    linarith
  · intro m hm hm7 hcase y hy0 hy1
    have hk2 : kapW l ≤ 2 := le_trans E.hkh H.hκh2
    rcases le_total y (yC l) with hyy | hyy
    · exact c2_regionB E.hl hk0.le hk2 hm hy0 hyy (E.C0m H hl2 m hm hm7) (E.Cm H hl2 m hm hm7 hcase)
    · rcases hcase with h1 | h2 | h3
      · subst h1
        have hyc2 : yC l < 1 / 2 := by
          unfold yC; rw [div_lt_div_iff₀ (by linarith [E.hl]) (by norm_num)]; linarith [E.hl]
        obtain ⟨a1, a2, a3, a4⟩ := E.m1 H hl1 hl2
        exact c2_regionA_one E.hl hk0.le E.hyc0 hyc2 hyy hy1 a1 a2 a3 a4
      · exact c2_regionA_ge2 E.hl hk0.le (by linarith) E.hyc0.le hyy (E.C0m H hl2 m hm hm7)
          (E.Cm H hl2 m hm hm7 (Or.inr (Or.inl h2))) (E.slopem H hl2 m (by linarith))
      · exact c2_regionA_ge2 E.hl hk0.le (by linarith) E.hyc0.le hyy (E.C0m H hl2 m hm hm7)
          (E.Cm H hl2 m hm hm7 (Or.inr (Or.inr h3))) (E.slopem H hl2 m (by linarith))

end

end LeanCherry
