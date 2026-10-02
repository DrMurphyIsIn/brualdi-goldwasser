/-
LeanCherry.PBRowsCore -- the generic row lemmas of the low-degree part (B) certificates.

Scaled quantities (all divided by the power of t at which they vanish), in the variable t:
  phi3 = f3/t = (3 Lm + (3/4) L34)/7,  et = eps/t = ((3/2) L34 - Lm)/7,  D2t = D(2)/t = (2/3) L23 - Lm/2,
  e1 = (E-1)/t = phi3 Xe(t phi3),  h2t = h2/t = (4/5) G2t/7,  L_a(t) = Lg(a t).
Each generic lemma below takes atom enclosures on a box [t1,t2] (from monotonicity and the two endpoint
values) and a single rational inequality, checked by norm_num at each instantiation, and concludes the
condition at every t in the box.
-/
import LeanCherry.PBAtoms

open Real

namespace LeanCherry
namespace PBC

noncomputable section

def phi3 (t : ℝ) : ℝ := (3 * Lm t + 3 / 4 * Lg (3 * t / 4)) / 7
def et (t : ℝ) : ℝ := (3 / 2 * Lg (3 * t / 4) - Lm t) / 7
def D2t (t : ℝ) : ℝ := 2 / 3 * Lg (2 * t / 3) - Lm t / 2
def e1 (t : ℝ) : ℝ := phi3 t * Xe (t * phi3 t)
def h2t (t : ℝ) : ℝ := 4 / 5 * G2t t / 7
/-- `kappa (y2 - yC)/t` -/
def r8 (t : ℝ) : ℝ := (2 * t - 1) * (1 + t) / ((1 - t) * (3 + 2 * t) ^ 2)

/-- atom enclosures at `t` -/
structure Enc (t lmL lmH l34L l34H l23L l23H : ℝ) : Prop where
  hlmL : lmL ≤ Lm t
  hlmH : Lm t ≤ lmH
  hl34L : l34L ≤ Lg (3 * t / 4)
  hl34H : Lg (3 * t / 4) ≤ l34H
  hl23L : l23L ≤ Lg (2 * t / 3)
  hl23H : Lg (2 * t / 3) ≤ l23H

/-- enclosures on a box `[t1, t2]`, `0 < t1` -/
lemma enc_box {t t1 t2 lmL lmH l34L l34H l23L l23H : ℝ} (h0 : 0 < t1) (h1 : t1 ≤ t) (h2 : t ≤ t2) (h3 : t2 < 1)
    (a1 : lmL ≤ Lm t1) (a2 : Lm t2 ≤ lmH) (a3 : l34L ≤ Lg (3 * t2 / 4)) (a4 : Lg (3 * t1 / 4) ≤ l34H)
    (a5 : l23L ≤ Lg (2 * t2 / 3)) (a6 : Lg (2 * t1 / 3) ≤ l23H) : Enc t lmL lmH l34L l34H l23L l23H := by
  have ht : 0 < t := lt_of_lt_of_le h0 h1
  exact ⟨le_trans a1 (Lm_mono h0 h1 (by linarith)), le_trans (Lm_mono ht h2 h3) a2,
    le_trans a3 (Lg_anti (by linarith) (by linarith)), le_trans (Lg_anti (by linarith) (by linarith)) a4,
    le_trans a5 (Lg_anti (by linarith) (by linarith)), le_trans (Lg_anti (by linarith) (by linarith)) a6⟩

/-- enclosures on a box `[0, t2]` (the values at `0` are the limits `1`) -/
lemma enc_box0 {t t2 lmL lmH l34L l34H l23L l23H : ℝ} (ht : 0 < t) (h2 : t ≤ t2) (h3 : t2 < 1)
    (a1 : lmL ≤ 1) (a2 : Lm t2 ≤ lmH) (a3 : l34L ≤ Lg (3 * t2 / 4)) (a4 : 1 ≤ l34H)
    (a5 : l23L ≤ Lg (2 * t2 / 3)) (a6 : 1 ≤ l23H) : Enc t lmL lmH l34L l34H l23L l23H := by
  exact ⟨le_trans a1 (one_le_Lm ht (by linarith)), le_trans (Lm_mono ht h2 h3) a2,
    le_trans a3 (Lg_anti (by linarith) (by linarith)), le_trans (Lg_le_one (by linarith)) a4,
    le_trans a5 (Lg_anti (by linarith) (by linarith)), le_trans (Lg_le_one (by linarith)) a6⟩

namespace Enc

variable {t lmL lmH l34L l34H l23L l23H : ℝ} (E : Enc t lmL lmH l34L l34H l23L l23H)
include E

lemma phi3_lo : (3 * lmL + 3 / 4 * l34L) / 7 ≤ phi3 t := by
  unfold phi3; have := E.hlmL; have := E.hl34L; linarith
lemma phi3_hi : phi3 t ≤ (3 * lmH + 3 / 4 * l34H) / 7 := by
  unfold phi3; have := E.hlmH; have := E.hl34H; linarith
lemma et_lo : (3 / 2 * l34L - lmH) / 7 ≤ et t := by
  unfold et; have := E.hlmH; have := E.hl34L; linarith
lemma et_hi : et t ≤ (3 / 2 * l34H - lmL) / 7 := by
  unfold et; have := E.hlmL; have := E.hl34H; linarith
lemma D2t_hi : D2t t ≤ 2 / 3 * l23H - lmL / 2 := by
  unfold D2t; have := E.hlmL; have := E.hl23H; linarith

end Enc

/-- `Xe (t phi3)` from above -/
lemma xe_hi {t t2 pH xH : ℝ} (ht : 0 < t) (h2 : t ≤ t2) (hp : 0 < phi3 t) (hpH : phi3 t ≤ pH)
    (hx : Xe (t2 * pH) ≤ xH) : Xe (t * phi3 t) ≤ xH :=
  le_trans (Xe_mono (mul_pos ht hp) (mul_le_mul h2 hpH hp.le (by linarith))) hx

/-- `Xe (t phi3)` from below, `0 < t1` -/
lemma xe_lo {t t1 pL xL : ℝ} (h0 : 0 < t1) (h1 : t1 ≤ t) (hpL : 0 < pL) (hp : pL ≤ phi3 t)
    (hx : xL ≤ Xe (t1 * pL)) : xL ≤ Xe (t * phi3 t) :=
  le_trans hx (Xe_mono (mul_pos h0 hpL) (mul_le_mul h1 hp hpL.le (by linarith)))

lemma kt_eq (t : ℝ) : kt t = 2 / ((1 - t) * (3 + 2 * t)) := rfl
lemma q3_eq (t : ℝ) : q3 t = 2 / ((1 - t) * (4 + 3 * t)) := rfl
lemma y4_eq (t : ℝ) : y4 t = 1 / (5 + 4 * t) := rfl

lemma kt_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 0 < kt t := by
  unfold kt; apply div_pos (by norm_num); nlinarith

/-! ### C7: (S6) for `W*`, scaled -/

theorem S6_box {t t1 t2 lmL lmH l34L l34H l23L l23H xL xH : ℝ}
    (h0 : 0 < t1) (h1 : t1 ≤ t) (h2 : t ≤ t2) (h3 : t2 ≤ 1 / 2)
    (E : Enc t lmL lmH l34L l34H l23L l23H)
    (hpL0 : 0 < (3 * lmL + 3 / 4 * l34L) / 7) (hxL0 : 0 ≤ xL)
    (hxH : Xe (t2 * ((3 * lmH + 3 / 4 * l34H) / 7)) ≤ xH)
    (hxL : xL ≤ Xe (t1 * ((3 * lmL + 3 / 4 * l34L) / 7)))
    (c1 : 0 ≤ (3 / 2 * l34L - lmH) / 7)
    (c2 : 0 < 1 - (3 * lmH + 3 / 4 * l34H) / 7 * xH)
    (c3 : 0 ≤ 1 - 2 / ((1 - t2) * (3 + 2 * t2)))
    (fin : 0 < (3 / 2 * l34L - lmH) / 7 * (3 / 2 + (1 - 2 / ((1 - t2) * (3 + 2 * t2))) /
      (1 - (3 * lmL + 3 / 4 * l34L) / 7 * xL)) - (2 / 3 * l23H - lmL / 2)) :
    0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have ht : 0 < t := lt_of_lt_of_le h0 h1
  have hp1 := E.phi3_lo
  have hp2 := E.phi3_hi
  have hp0 : 0 < phi3 t := lt_of_lt_of_le hpL0 hp1
  have hX1 := xe_hi ht h2 hp0 hp2 hxH
  have hX2 := xe_lo h0 h1 hpL0 hp1 hxL
  have hX0 : 0 ≤ Xe (t * phi3 t) := le_trans hxL0 hX2
  have hk : kt t ≤ kt t2 := kt_mono ht.le h2 (by linarith)
  rw [kt_eq t2] at hk
  have he1 : e1 t ≤ (3 * lmH + 3 / 4 * l34H) / 7 * xH := by
    unfold e1; exact mul_le_mul hp2 hX1 hX0 (by linarith)
  have he2 : (3 * lmL + 3 / 4 * l34L) / 7 * xL ≤ e1 t := by
    unfold e1; exact mul_le_mul hp1 hX2 hxL0 hp0.le
  have hu0 : 0 < 1 - e1 t := by linarith
  refine ⟨hu0, ?_⟩
  have hdiv : (1 - 2 / ((1 - t2) * (3 + 2 * t2))) / (1 - (3 * lmL + 3 / 4 * l34L) / 7 * xL)
      ≤ (1 - kt t) / (1 - e1 t) :=
    div_le_div₀ (by linarith) (by linarith) hu0 (by linarith)
  have het := E.et_lo
  have hD := E.D2t_hi
  have hq0 : 0 ≤ (1 - 2 / ((1 - t2) * (3 + 2 * t2))) / (1 - (3 * lmL + 3 / 4 * l34L) / 7 * xL) :=
    div_nonneg c3 (by linarith)
  have hm := mul_le_mul het (by linarith : 3 / 2 + (1 - 2 / ((1 - t2) * (3 + 2 * t2))) /
    (1 - (3 * lmL + 3 / 4 * l34L) / 7 * xL) ≤ 3 / 2 + (1 - kt t) / (1 - e1 t)) (by linarith) (le_trans c1 het)
  linarith

/-! ### C1: (S2), scaled: `phi3 >= q3 * Lg (t q3)` -/

lemma xq_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) : s * q3 s ≤ t * q3 t :=
  mul_le_mul hst (q3_mono hs hst ht) (by unfold q3; apply div_nonneg (by norm_num); nlinarith) (by linarith)

lemma xq_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < t * q3 t := by
  apply mul_pos h0; unfold q3; apply div_pos (by norm_num); nlinarith

theorem S2_box {t t1 t2 lmL lmH l34L l34H l23L l23H LqH : ℝ}
    (h0 : 0 ≤ t1) (h1 : t1 ≤ t) (h2 : t ≤ t2) (h3 : t2 < 1) (ht : 0 < t)
    (E : Enc t lmL lmH l34L l34H l23L l23H)
    (hLq : Lg (t * q3 t) ≤ LqH)
    (fin : 0 < (3 * lmL + 3 / 4 * l34L) / 7 - 2 / ((1 - t2) * (4 + 3 * t2)) * LqH) :
    q3 t * Lg (t * q3 t) < phi3 t := by
  have hp := E.phi3_lo
  have hq : q3 t ≤ q3 t2 := q3_mono ht.le h2 h3
  rw [q3_eq t2] at hq
  have hL0 : 0 < Lg (t * q3 t) := Lg_pos (xq_pos ht (by linarith))
  have hq0 : 0 < q3 t := by unfold q3; apply div_pos (by norm_num); nlinarith
  have := mul_le_mul hq hLq hL0.le (by linarith)
  linarith

/-- the bound on `Lg (t q3)` on a box with `0 < t1` -/
lemma Lq_box {t t1 LqH : ℝ} (h0 : 0 < t1) (h1 : t1 ≤ t) (ht : t < 1) (h : Lg (t1 * q3 t1) ≤ LqH) :
    Lg (t * q3 t) ≤ LqH :=
  le_trans (Lg_anti (xq_pos h0 (by linarith)) (xq_mono h0.le h1 ht)) h

lemma Lq_box0 {t LqH : ℝ} (ht : 0 < t) (ht1 : t < 1) (h : 1 ≤ LqH) : Lg (t * q3 t) ≤ LqH :=
  le_trans (Lg_le_one (xq_pos ht ht1)) h

/-! ### C3: (S4) -/

lemma rhohat_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 31 / 50) : 0 ≤ rhohat t := by
  unfold rhohat; nlinarith [sq_nonneg t, mul_nonneg h0 (sq_nonneg t)]

lemma gS_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gS r := by
  rw [gS_eq hr]; positivity

theorem S4_box {t t1 t2 R : ℝ} (h0 : 0 ≤ t1) (h1 : t1 ≤ t) (h2 : t ≤ t2) (h3 : t2 ≤ 31 / 50) (ht : 0 < t)
    (hR0 : 0 < R) (hR : 1 ≤ R ^ 2 * (1 - t2))
    (fin : 0 < (1 + t1) ^ 2 - 1291 / 1000 * gS (rhohat t1) * t2 * (1 + R)) :
    1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have hr0 : 0 ≤ rhohat t := rhohat_nonneg ht.le (by linarith)
  have hg : gS (rhohat t) ≤ gS (rhohat t1) := gS_mono hr0 (rhohat_anti h0 h1 (by linarith))
  have hg0 : 0 ≤ gS (rhohat t) := gS_nonneg hr0
  have hs0 : 0 < 1 - t := by linarith
  have hsq : 1 / Real.sqrt (1 - t) ≤ R := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hs0)]
    have h4 : Real.sqrt (1 - t2) ≤ Real.sqrt (1 - t) := Real.sqrt_le_sqrt (by linarith)
    have h5 : 1 ≤ R * Real.sqrt (1 - t2) := by
      have hs2 : 0 ≤ 1 - t2 := by linarith
      have e : (R * Real.sqrt (1 - t2)) ^ 2 = R ^ 2 * (1 - t2) := by
        rw [mul_pow, Real.sq_sqrt hs2]
      by_contra hc
      push Not at hc
      have hn := mul_nonneg hR0.le (Real.sqrt_nonneg (1 - t2))
      nlinarith
    nlinarith
  have hsq0 : 0 ≤ 1 / Real.sqrt (1 - t) := by positivity
  have hA : gS (rhohat t) * t ≤ gS (rhohat t1) * t2 := mul_le_mul hg h2 ht.le (le_trans hg0 hg)
  have hB : gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) ≤ gS (rhohat t1) * t2 * (1 + R) :=
    mul_le_mul hA (by linarith) (by positivity) (le_trans (mul_nonneg hg0 ht.le) hA)
  have hC : (1 + t1) ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
  linarith

/-! ### C8: (S6) for `lam >= 2`, scaled -/

lemma r8_mono {s t : ℝ} (hs : 1 / 2 ≤ s) (hst : s ≤ t) (ht : t < 1) : r8 s ≤ r8 t := by
  unfold r8
  have e : (1 - s) * (3 + 2 * s) ^ 2 - (1 - t) * (3 + 2 * t) ^ 2
      = (t - s) * (-3 + 8 * (s + t) + 4 * (s ^ 2 + s * t + t ^ 2)) := by ring
  have hb : 0 ≤ (t - s) * (-3 + 8 * (s + t) + 4 * (s ^ 2 + s * t + t ^ 2)) :=
    mul_nonneg (by linarith) (by nlinarith)
  apply div_le_div₀ (by nlinarith) (by nlinarith) (mul_pos (by linarith) (pow_pos (by linarith) 2)) (by linarith)

theorem S6hi_box {t t1 t2 lmL lmH l34L l34H l23L l23H : ℝ}
    (h0 : 1 / 2 ≤ t1) (h1 : t1 ≤ t) (h2 : t ≤ t2) (h3 : t2 < 1)
    (E : Enc t lmL lmH l34L l34H l23L l23H)
    (fin : 0 < lmL / 2 - 2 / 3 * l23H - (2 * t2 - 1) * (1 + t2) / ((1 - t2) * (3 + 2 * t2) ^ 2)) :
    r8 t < Lm t / 2 - 2 / 3 * Lg (2 * t / 3) := by
  have hr : r8 t ≤ r8 t2 := r8_mono (by linarith) h2 h3
  unfold r8 at hr
  unfold r8
  have := E.hlmL; have := E.hl23H
  linarith

/-! ### C10: the `W2` conditions (T1)-(T8), scaled -/

/-- the base enclosures of the `W2` conditions on a box -/
structure W2Enc (t pL pH etL etH hL hH kL kH yL yH eL eH xH : ℝ) : Prop where
  p1 : pL ≤ phi3 t
  p2 : phi3 t ≤ pH
  et1 : etL ≤ et t
  et2 : et t ≤ etH
  h1 : hL ≤ h2t t
  h2 : h2t t ≤ hH
  k1 : kL ≤ kt t
  k2 : kt t ≤ kH
  y1 : yL ≤ y4 t
  y2 : y4 t ≤ yH
  e1' : eL ≤ e1 t
  e2' : e1 t ≤ eH
  x2 : Xe (t * phi3 t) ≤ xH
  tpos : 0 < t
  hL0 : 0 < hL
  pL0 : 0 < pL

theorem w2enc {t t1 t2 lmL lmH l34L l34H l23L l23H xL xH gL gH : ℝ}
    (h0 : 0 ≤ t1) (h1 : t1 ≤ t) (h2 : t ≤ t2) (h3 : t2 ≤ 1 / 10) (ht : 0 < t)
    (E : Enc t lmL lmH l34L l34H l23L l23H)
    (hpL0 : 0 < (3 * lmL + 3 / 4 * l34L) / 7) (hxL0 : 0 ≤ xL)
    (hxH : Xe (t2 * ((3 * lmH + 3 / 4 * l34H) / 7)) ≤ xH)
    (hxL : xL ≤ Xe (t * phi3 t))
    (hgL : gL ≤ G2t t) (hgH : G2t t ≤ gH) (hgL0 : 0 < gL) :
    W2Enc t ((3 * lmL + 3 / 4 * l34L) / 7) ((3 * lmH + 3 / 4 * l34H) / 7) ((3 / 2 * l34L - lmH) / 7)
      ((3 / 2 * l34H - lmL) / 7) (4 / 5 * gL / 7) (4 / 5 * gH / 7) (2 / ((1 - t1) * (3 + 2 * t1)))
      (2 / ((1 - t2) * (3 + 2 * t2))) (1 / (5 + 4 * t2)) (1 / (5 + 4 * t1))
      ((3 * lmL + 3 / 4 * l34L) / 7 * xL) ((3 * lmH + 3 / 4 * l34H) / 7 * xH) xH := by
  have hp1 := E.phi3_lo
  have hp2 := E.phi3_hi
  have hp0 : 0 < phi3 t := lt_of_lt_of_le hpL0 hp1
  have hX1 := xe_hi ht h2 hp0 hp2 hxH
  have hX0 : 0 ≤ Xe (t * phi3 t) := le_trans hxL0 hxL
  have k1 := kt_mono h0 h1 (by linarith)
  have k2 := kt_mono ht.le h2 (by linarith)
  have y1 := y4_anti ht.le h2
  have y2 := y4_anti h0 h1
  rw [kt_eq] at k1 k2
  rw [y4_eq] at y1 y2
  exact
    { p1 := hp1, p2 := hp2, et1 := E.et_lo, et2 := E.et_hi
      h1 := by unfold h2t; linarith
      h2 := by unfold h2t; linarith
      k1 := k1, k2 := k2, y1 := y1, y2 := y2
      e1' := by unfold e1; exact mul_le_mul hp1 hxL hxL0 hp0.le
      e2' := by unfold e1; exact mul_le_mul hp2 hX1 hX0 (by linarith)
      x2 := hX1, tpos := ht
      hL0 := by positivity
      pL0 := hpL0 }

namespace W2Enc

variable {t pL pH etL etH hL hH kL kH yL yH eL eH xH : ℝ}
  (W : W2Enc t pL pH etL etH hL hH kL kH yL yH eL eH xH)
include W

lemma T1 (fin : 0 < kL - eH) : 0 < kt t - e1 t := by
  have := W.k1; have := W.e2'; linarith

lemma T3a (fin : 0 < etL - hH) : 0 < et t - h2t t := by
  have := W.et1; have := W.h2; linarith

lemma T2 (c1 : 0 < kL - eH) (c2 : 0 < etL - hH) (c3 : kH < 1)
    (fin : 0 ≤ (etL - hH) / (1 - kL) - hH / (kL - eH)) :
    h2t t / (kt t - e1 t) ≤ (et t - h2t t) / (1 - kt t) := by
  have hk := W.T1 c1
  have hh0 : 0 < h2t t := lt_of_lt_of_le W.hL0 W.h1
  have hn := W.T3a c2
  have a1 : h2t t / (kt t - e1 t) ≤ hH / (kL - eH) :=
    div_le_div₀ (by linarith [W.h2]) W.h2 c1 (by linarith [W.k1, W.e2'])
  have a2 : (etL - hH) / (1 - kL) ≤ (et t - h2t t) / (1 - kt t) :=
    div_le_div₀ hn.le (by linarith [W.et1, W.h2]) (by linarith [W.k2]) (by linarith [W.k1])
  linarith

lemma T4 (t2 : ℝ) (ht2 : t ≤ t2) (c0 : 0 < kL) (c1 : 0 < kL - eH) (c2 : 0 < etL - hH) (c3 : kH < 1) (c4 : 0 ≤ yL)
    (c5 : 0 ≤ 1 - t2 * kH * yH)
    (fin : 0 ≤ yL * (1 - t2 * kH * yH) - (etH - hL) / (1 - kH)) :
    (et t - h2t t) / (1 - kt t) ≤ y4 t * (1 - t * kt t * y4 t) := by
  have hn := W.T3a c2
  have hk0 : 0 < kt t := lt_of_lt_of_le c0 W.k1
  have a1 : (et t - h2t t) / (1 - kt t) ≤ (etH - hL) / (1 - kH) :=
    div_le_div₀ (by linarith [W.et2, W.h1]) (by linarith [W.et2, W.h1]) (by linarith) (by linarith [W.k2])
  have a2 : t * kt t * y4 t ≤ t2 * kH * yH := by
    have := mul_le_mul ht2 W.k2 hk0.le (by linarith [W.tpos])
    exact mul_le_mul this W.y2 (by linarith [W.y1]) (by nlinarith [W.tpos])
  have a3 : yL * (1 - t2 * kH * yH) ≤ y4 t * (1 - t * kt t * y4 t) :=
    mul_le_mul W.y1 (by linarith) c5 (by linarith [W.y1])
  linarith

lemma T5 (t1 : ℝ) (h1 : t1 ≤ t) (h0 : 0 ≤ t1) (c0 : 0 ≤ eL) (c1 : 0 < kL - eH)
    (fin : 0 ≤ 1 + 14 * (1 + t1 * eL) - (kH - eL) / hL) :
    (kt t - e1 t) / h2t t ≤ 1 + 14 * (1 + t * e1 t) := by
  have hh0 : 0 < h2t t := lt_of_lt_of_le W.hL0 W.h1
  have a1 : (kt t - e1 t) / h2t t ≤ (kH - eL) / hL :=
    div_le_div₀ (by linarith [W.k2, W.e1', W.k1, W.e2']) (by linarith [W.k2, W.e1']) W.hL0 W.h1
  have a2 : t1 * eL ≤ t * e1 t := mul_le_mul h1 W.e1' c0 (by linarith [W.tpos])
  linarith

lemma T6 (fin : 0 ≤ 14 / 13 - xH) : Xe (t * phi3 t) ≤ 14 / 13 := by
  have := W.x2; linarith

lemma T7 (sq : ℝ) (hsq0 : 0 ≤ sq) (hsq : sq ^ 2 ≤ kL * hL) (c0 : 0 ≤ kL)
    (fin : 0 ≤ pL - kH - hH + 2 * sq) :
    0 ≤ phi3 t - kt t - h2t t + 2 * Real.sqrt (kt t * h2t t) := by
  have a1 : sq ≤ Real.sqrt (kt t * h2t t) := by
    apply Real.le_sqrt_of_sq_le
    have := mul_le_mul W.k1 W.h1 W.hL0.le (le_trans c0 W.k1)
    linarith
  have := W.p1; have := W.k2; have := W.h2
  linarith

lemma T8 (fin : 0 ≤ pL + 5 * etL - 5 / 6) : 0 ≤ phi3 t + 5 * et t - 5 / 6 := by
  have := W.p1; have := W.et1; linarith

lemma T8b (fin : 0 ≤ etL - 1 / 36) : 1 / 36 ≤ et t := by
  have := W.et1; linarith

end W2Enc

end

end PBC
end LeanCherry
