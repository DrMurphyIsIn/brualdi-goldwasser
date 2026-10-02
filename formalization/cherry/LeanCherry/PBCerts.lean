/-
LeanCherry.PBCerts -- the low-degree part (B) certificates as real inequalities over their whole intervals.

Variable: t = lam/(2+lam) in (0, 1/phi), 1/phi < 6181/10000.  Unscaled quantities (with F = f3 where used):
  ell = -log(1-t) = log c,  f3 = (3 ell + log(1+3t/4))/7,  eps3 = 2 f3 - ell,  E3 = exp f3,
  kap = 2t/((1-t)(3+2t)) = lam y2,  D2 = log(1+2t/3) - ell/2 = D(2),  h2 = (4/5) G2/7 = (4/5) g(A2),
  y4 = 1/(5+4t),  lam y3 = t q3(t).
Certificates:
  C1  (S2)  log(1 + lam y3) < f3                             on (0, 6181/10000]   (10 rows)
  C2  (S3)  P2(t) > 0 by 7 positive Bernstein coefficients, hence (5+4t)/6 < (11/12) sqrt c (1 - kap y4)
                                                              on [0, 6181/10000]
  C3  (S4)  1.291 g(rhohat t) t (1 + 1/sqrt(1-t)) < (1+t)^2   on (0, 6181/10000]   (13 rows)
  C4-C6     8+6lam+3lam^2 > 0, -5lam^3-14lam^2+128lam+160 > 0 (lam in [0, 3.2361]), 2-t-2t^2-t^3 > 0
  C7  (S6)  u3 = 1+t-E3 > 0 and eps3 (3/2 + (t-kap)/u3) - D2 > 0   on [3/43, 3229/10000]  (17 rows)
  C8  (S6)  kap (y2 - yC) < -D2                              on [1/2, 6181/10000]  (1 row)
  C9        G3(3/43) < 0   (auxiliary: not used by part_B_full; F = f3 on (0, 3/20] is PBGap.fstar_eq_f3)
  C10 (W2)  (T1)-(T8) at F = f3                               on (0, 3/43]   (9 conditions x 2 rows)
  e^{6 Dmax} = 32768/19683 < 1.291^2.
-/
import LeanCherry.PBRowsC1
import LeanCherry.PBRowsC3
import LeanCherry.PBRowsC7
import LeanCherry.PBRowsC8
import LeanCherry.PBRowsC10

open Real

namespace LeanCherry
namespace PBC

noncomputable section

/-! ### unscaled quantities -/

def ell (t : ℝ) : ℝ := -Real.log (1 - t)
def f3 (t : ℝ) : ℝ := (3 * ell t + Real.log (1 + 3 * t / 4)) / 7
def eps3 (t : ℝ) : ℝ := 2 * f3 t - ell t
def E3 (t : ℝ) : ℝ := Real.exp (f3 t)
def kap (t : ℝ) : ℝ := 2 * t / ((1 - t) * (3 + 2 * t))
def D2 (t : ℝ) : ℝ := Real.log (1 + 2 * t / 3) - ell t / 2
def h2 (t : ℝ) : ℝ := 4 / 5 * G2 t / 7

lemma t_Lm {t : ℝ} (ht : t ≠ 0) : t * Lm t = ell t := by unfold Lm ell; field_simp
lemma t_Lg {a t : ℝ} (ha : a ≠ 0) (ht : t ≠ 0) : a * t * Lg (a * t) = Real.log (1 + a * t) := by
  unfold Lg; have : a * t ≠ 0 := mul_ne_zero ha ht
  field_simp
lemma t_phi3 {t : ℝ} (ht : t ≠ 0) : t * phi3 t = f3 t := by
  unfold phi3 f3
  have h1 := t_Lm ht
  have h2 := t_Lg (a := 3 / 4) (by norm_num) ht
  have e : 3 * t / 4 = 3 / 4 * t := by ring
  rw [e]
  linear_combination 3 / 7 * h1 + 1 / 7 * h2
lemma t_et {t : ℝ} (ht : t ≠ 0) : t * et t = eps3 t := by
  unfold et eps3 f3
  have h1 := t_Lm ht
  have h2 := t_Lg (a := 3 / 4) (by norm_num) ht
  have e : 3 * t / 4 = 3 / 4 * t := by ring
  rw [e]
  linear_combination (-1 / 7) * h1 + 2 / 7 * h2
lemma t_D2t {t : ℝ} (ht : t ≠ 0) : t * D2t t = D2 t := by
  unfold D2t D2
  have h1 := t_Lm ht
  have h2 := t_Lg (a := 2 / 3) (by norm_num) ht
  have e : 2 * t / 3 = 2 / 3 * t := by ring
  rw [e]
  linear_combination -(1 / 2) * h1 + h2
lemma t_kt (t : ℝ) : t * kt t = kap t := by unfold kt kap; ring
lemma t_h2t {t : ℝ} (ht : t ≠ 0) : t * h2t t = h2 t := by unfold h2t h2 G2t; field_simp
lemma f3_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < f3 t := by
  have : 0 < phi3 t := by
    unfold phi3; have := one_le_Lm h0 h1; have := Lg_pos (by linarith : (0:ℝ) < 3 * t / 4); linarith
  rw [← t_phi3 h0.ne']; positivity
lemma t_e1 {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : t * e1 t = E3 t - 1 := by
  have hf := f3_pos h0 h1
  unfold e1 Xe E3
  rw [← mul_assoc, t_phi3 h0.ne']
  field_simp

/-! ### C1 -/

/-- **C1 (S2)**: `log(1 + lam y3) < f3` on `(0, 6181/10000]`, with `lam y3 = t q3(t)`. -/
theorem cert_C1 (t : ℝ) (ht : 0 < t) (h2 : t ≤ 6181 / 10000) : Real.log (1 + t * q3 t) < f3 t := by
  have h := cert_C1_scaled t ht h2
  have hq : 0 < t * q3 t := xq_pos ht (by linarith)
  have hq3 : q3 t ≠ 0 := by
    have := hq; intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  have e : Real.log (1 + t * q3 t) = q3 t * Lg (t * q3 t) * t := by
    unfold Lg; field_simp
  rw [e, ← t_phi3 ht.ne']
  nlinarith

/-! ### C2 -/

/-- the degree-6 polynomial of (S3) -/
def P2 (t : ℝ) : ℝ := 11 * (1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3) * ((1 - t) * (3 + 2 * t) * (5 + 4 * t) - 2 * t)
  - 2 * (5 + 4 * t) ^ 2 * (1 - t) * (3 + 2 * t)

lemma P2_bern (u : ℝ) : P2 (6181 / 10000 * u) = 4 / 5 + ((71/5:ℝ) * u ^ 0 * (1 - u) ^ 6 + (210999/4000:ℝ) * u ^ 1 * (1 - u) ^ 5 + (9304147591/160000000:ℝ) * u ^ 2 * (1 - u) ^ 4 + (200458973624967/16000000000000:ℝ) * u ^ 3 * (1 - u) ^ 3 + (28274024699927191/160000000000000000:ℝ) * u ^ 4 * (1 - u) ^ 2 + (7602690775427121099251/800000000000000000000:ℝ) * u ^ 5 * (1 - u) ^ 1 + (288263746938437739731609/400000000000000000000000:ℝ) * u ^ 6 * (1 - u) ^ 0) := by
  unfold P2; ring

/-- **C2**: `P2 > 0` on `[0, 6181/10000]` (all seven Bernstein coefficients exceed `4/5`). -/
theorem cert_C2_poly (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 6181 / 10000) : 0 < P2 t := by
  set u := t / (6181 / 10000) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : 0 ≤ 1 - u := by
    rw [hu, sub_nonneg, div_le_one (by norm_num)]; exact h1
  have et : t = 6181 / 10000 * u := by rw [hu]; field_simp
  rw [et, P2_bern]
  set v := 1 - u with hv
  have : 0 ≤ ((71/5:ℝ) * u ^ 0 * v ^ 6 + (210999/4000:ℝ) * u ^ 1 * v ^ 5 + (9304147591/160000000:ℝ) * u ^ 2 * v ^ 4 + (200458973624967/16000000000000:ℝ) * u ^ 3 * v ^ 3 + (28274024699927191/160000000000000000:ℝ) * u ^ 4 * v ^ 2 + (7602690775427121099251/800000000000000000000:ℝ) * u ^ 5 * v ^ 1 + (288263746938437739731609/400000000000000000000000:ℝ) * u ^ 6 * v ^ 0) := by positivity
  linarith

/-- the truncated binomial series: `1 + t/2 + 3t^2/8 + 5t^3/16 <= (1-t)^{-1/2}` -/
lemma binom_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3 ≤ 1 / Real.sqrt (1 - t) := by
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  rw [le_div_iff₀ hs]
  have hB : 0 ≤ 1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3 := by positivity
  have key : (1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3) ^ 2 * (1 - t) ≤ 1 := by
    have e : 1 - (1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3) ^ 2 * (1 - t)
        = 35 / 64 * t ^ 4 + 7 / 32 * t ^ 5 + 35 / 256 * t ^ 6 + 25 / 256 * t ^ 7 := by ring
    have : 0 ≤ 35 / 64 * t ^ 4 + 7 / 32 * t ^ 5 + 35 / 256 * t ^ 6 + 25 / 256 * t ^ 7 := by positivity
    linarith
  have hsq : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have hp : 0 ≤ (1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3) * Real.sqrt (1 - t) := mul_nonneg hB hs.le
  nlinarith [sq_nonneg ((1 + t / 2 + 3 / 8 * t ^ 2 + 5 / 16 * t ^ 3) * Real.sqrt (1 - t) - 1)]

/-- **C2 (S3)**: `(5+4t)/6 < (11/12) (1-t)^{-1/2} (1 - kap y4)` on `[0, 6181/10000]`. -/
theorem cert_C2 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 6181 / 10000) :
    (5 + 4 * t) / 6 < 11 / 12 * (1 / Real.sqrt (1 - t)) * (1 - kap t * y4 t) := by
  have hP := cert_C2_poly t h0 h1
  have hB := binom_le h0 (by linarith)
  have h1t : 0 < 1 - t := by linarith
  have hA : 0 < (1 - t) * (3 + 2 * t) * (5 + 4 * t) := by positivity
  have hQ : 0 < (1 - t) * (3 + 2 * t) * (5 + 4 * t) - 2 * t := by nlinarith
  have e : 1 - kap t * y4 t = ((1 - t) * (3 + 2 * t) * (5 + 4 * t) - 2 * t) / ((1 - t) * (3 + 2 * t) * (5 + 4 * t)) := by
    unfold kap y4
    have : (1 - t) ≠ 0 := h1t.ne'
    field_simp
  rw [e]
  set S := 1 / Real.sqrt (1 - t) with hS
  set Qv := (1 - t) * (3 + 2 * t) * (5 + 4 * t) - 2 * t with hQv
  set A := (1 - t) * (3 + 2 * t) * (5 + 4 * t) with hAv
  have hm := mul_le_mul_of_nonneg_right hB hQ.le
  unfold P2 at hP
  have key : 2 * (5 + 4 * t) * A < 11 * S * Qv := by
    have : 2 * (5 + 4 * t) * A = 2 * (5 + 4 * t) ^ 2 * (1 - t) * (3 + 2 * t) := by rw [hAv]; ring
    rw [this]; nlinarith
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 6)]
  have : 11 / 12 * S * (Qv / A) * 6 = 11 * S * Qv / (2 * A) := by field_simp; ring
  rw [this, lt_div_iff₀ (by positivity)]
  nlinarith

/-! ### C4-C6 -/

/-- **C4** -/
theorem cert_C4 (l : ℝ) : 0 < 8 + 6 * l + 3 * l ^ 2 := by nlinarith [sq_nonneg (3 * l + 1)]

/-- **C5** -/
theorem cert_C5 (l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 32361 / 10000) : 0 < -5 * l ^ 3 - 14 * l ^ 2 + 128 * l + 160 := by
  nlinarith [mul_nonneg h0 (mul_nonneg h0 (by linarith : (0:ℝ) ≤ 32361 / 10000 - l)),
    mul_nonneg h0 (by linarith : (0:ℝ) ≤ 32361 / 10000 - l)]

/-- **C6** -/
theorem cert_C6 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 6181 / 10000) : 0 < 2 - t - 2 * t ^ 2 - t ^ 3 := by
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-! ### C7 -/

/-- **C7 (S6) for `W*` at `F = f3`**: `u3 = 1 + t - E3 > 0` and `eps3 (3/2 + (t - kap)/u3) - D2 > 0`
    on `[3/43, 3229/10000]`, i.e. `lam in [3/20, 0.9538...]`. -/
theorem cert_C7 (t : ℝ) (h1 : 3 / 43 ≤ t) (h2 : t ≤ 3229 / 10000) :
    0 < 1 + t - E3 t ∧ 0 < eps3 t * (3 / 2 + (t - kap t) / (1 + t - E3 t)) - D2 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  obtain ⟨hu, hP⟩ := c7_cov_0 t h1 h2
  have e1' := t_e1 ht (by linarith)
  have hu' : 1 + t - E3 t = t * (1 - e1 t) := by linarith
  refine ⟨by rw [hu']; positivity, ?_⟩
  have e2 : (t - kap t) / (1 + t - E3 t) = (1 - kt t) / (1 - e1 t) := by
    rw [hu', ← t_kt]; field_simp
  rw [e2, ← t_et ht.ne', ← t_D2t ht.ne']
  have : t * et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - t * D2t t
      = t * (et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t) := by ring
  rw [this]; positivity

/-! ### C8 -/

/-- **C8 (S6), `lam >= 2`**: `kap (y2 - yC) < -D(2)` on `[1/2, 6181/10000]`. -/
theorem cert_C8 (t : ℝ) (h1 : 1 / 2 ≤ t) (h2 : t ≤ 6181 / 10000) :
    kap t * (1 / (3 + 2 * t) - (1 - t) / 2) < -D2 t := by
  have ht : 0 < t := by linarith
  have h := cert_C8_scaled t h1 h2
  have e1 : kap t * (1 / (3 + 2 * t) - (1 - t) / 2) = t * r8 t := by
    unfold kap r8
    have : (1 - t) ≠ 0 := by intro h; linarith
    have : (3 + 2 * t) ≠ 0 := by intro h; linarith
    field_simp; ring
  have e2 : -D2 t = t * (Lm t / 2 - 2 / 3 * Lg (2 * t / 3)) := by
    rw [← t_D2t ht.ne']; unfold D2t; ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left h ht

/-! ### C9 (auxiliary: not used by part_B_full, see PBGap.fstar_eq_f3) -/

/-- `G3 = 7 log(1+4t/5) - 9 log(1+3t/4) - log(1-t)` -/
def G3 (t : ℝ) : ℝ := 7 * Real.log (1 + 4 * t / 5) - 9 * Real.log (1 + 3 * t / 4) - Real.log (1 - t)

/-- **C9**: `G3(3/43) < 0`. -/
theorem cert_C9 : G3 (3 / 43) < 0 := by
  have l1 := log_le_of (y := 1 + 4 * (3 / 43 : ℝ) / 5) (b := 13577997341 / 250000000000) 7 (by norm_num) (by norm_num)
    (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])
  have l2 := log_ge_of (y := 1 + 3 * (3 / 43 : ℝ) / 4) (a := 25501277221 / 500000000000) 6 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])
  have l3 := nlog1m_le (p := (3 / 43 : ℝ)) (b := 7232066159 / 100000000000) 7 (by norm_num) (by norm_num)
    (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])
  unfold G3
  linarith

/-! ### the identity e^{6 Dmax} -/

def Dmax : ℝ := Real.log (4 / 3) + 1 / 2 * Real.log (2 / 3)

/-- `e^{6 Dmax} = 32768/19683 < 1.291^2` -/
theorem cert_Dmax : Real.exp (6 * Dmax) = 32768 / 19683 ∧ (32768 / 19683 : ℝ) < (1291 / 1000) ^ 2 := by
  refine ⟨?_, by norm_num⟩
  have e : 6 * Dmax = Real.log ((4 / 3) ^ 6 * (2 / 3) ^ 3) := by
    unfold Dmax
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e, Real.exp_log (by norm_num)]
  norm_num

/-! ### C10 -/

/-- **C10: the `W2` conditions at `F = f3` on `(0, 3/43]`** (`lam in (0, 3/20]`):
  (T1) `E3 - 1 < kap`; (T3) `h2 < eps3`, `kap < t`, `0 < f3`, `0 < G2`;
  (T2) `h2 (t - kap) <= (eps3 - h2)(kap - E3 + 1)`; (T4) `eps3 - h2 <= (t - kap) y4 (1 - kap y4)`;
  (T5) `kap - E3 + 1 <= h2 (1 + 14 E3)`; (T6) `13 (E3 - 1) <= 14 f3`;
  (T7) `0 <= f3 - kap - h2 + 2 sqrt(kap h2)`; (T8) `0 <= f3 + 5 eps3 - 5t/6` and `t/36 <= eps3`. -/
theorem cert_C10 (t : ℝ) (ht : 0 < t) (hb : t ≤ 3 / 43) :
    E3 t - 1 < kap t ∧ h2 t < eps3 t ∧ kap t < t ∧ 0 < f3 t ∧ 0 < G2 t ∧
    h2 t * (t - kap t) ≤ (eps3 t - h2 t) * (kap t - E3 t + 1) ∧
    eps3 t - h2 t ≤ (t - kap t) * y4 t * (1 - kap t * y4 t) ∧
    kap t - E3 t + 1 ≤ h2 t * (1 + 14 * E3 t) ∧
    13 * (E3 t - 1) ≤ 14 * f3 t ∧
    0 ≤ f3 t - kap t - h2 t + 2 * Real.sqrt (kap t * h2 t) ∧
    0 ≤ f3 t + 5 * eps3 t - 5 * t / 6 ∧ t / 36 ≤ eps3 t := by
  obtain ⟨T1, T3a, T2, T4, T5, T6, T7, T8, T8b⟩ := cert_C10_scaled t ht hb
  have ht1 : t < 1 := by linarith
  have hne := ht.ne'
  have ee1 := t_e1 ht ht1
  have ek := t_kt t
  have eet := t_et hne
  have eh := t_h2t hne
  have ep := t_phi3 hne
  have hkt1 : kt t < 1 := by
    have := kt_mono ht.le hb (by norm_num)
    have : kt (3 / 43) < 1 := by norm_num [kt]
    linarith
  have hG : 1 / 12 ≤ G2t t := G2t_ge ht (by linarith)
  have hh0 : 0 < h2t t := by unfold h2t; linarith
  have hf3 : 0 < f3 t := f3_pos ht ht1
  have h1k : 0 < 1 - kt t := by linarith
  refine ⟨?_, ?_, ?_, hf3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ee1, ← ek]; exact mul_lt_mul_of_pos_left (by linarith) ht
  · rw [← eh, ← eet]; exact mul_lt_mul_of_pos_left (by linarith) ht
  · rw [← ek]; nlinarith
  · have : G2 t = t * G2t t := by unfold G2t; field_simp
    rw [this]; positivity
  · -- (T2)
    rw [div_le_div_iff₀ T1 h1k] at T2
    have a : h2 t * (t - kap t) = t ^ 2 * (h2t t * (1 - kt t)) := by rw [← eh, ← ek]; ring
    have b : (eps3 t - h2 t) * (kap t - E3 t + 1) = t ^ 2 * ((et t - h2t t) * (kt t - e1 t)) := by
      have : kap t - E3 t + 1 = t * (kt t - e1 t) := by rw [← ek]; linarith
      rw [this, ← eet, ← eh]; ring
    rw [a, b]
    exact mul_le_mul_of_nonneg_left T2 (sq_nonneg t)
  · -- (T4)
    rw [div_le_iff₀ h1k] at T4
    have e : (t - kap t) * y4 t * (1 - kap t * y4 t) = t * (y4 t * (1 - t * kt t * y4 t) * (1 - kt t)) := by
      rw [← ek]; ring
    rw [e, ← eet, ← eh]
    have : t * et t - t * h2t t = t * (et t - h2t t) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left T4 ht.le
  · -- (T5)
    rw [div_le_iff₀ hh0] at T5
    have e : kap t - E3 t + 1 = t * (kt t - e1 t) := by rw [← ek]; linarith
    have e' : h2 t * (1 + 14 * E3 t) = t * ((1 + 14 * (1 + t * e1 t)) * h2t t) := by
      rw [← eh, ee1]; ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left T5 ht.le
  · -- (T6)
    have hx : Xe (t * phi3 t) = (E3 t - 1) / f3 t := by unfold Xe E3; rw [ep]
    rw [hx, div_le_iff₀ hf3] at T6
    linarith
  · -- (T7)
    have e : Real.sqrt (kap t * h2 t) = t * Real.sqrt (kt t * h2t t) := by
      rw [← ek, ← eh]
      have : t * kt t * (t * h2t t) = t ^ 2 * (kt t * h2t t) := by ring
      rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
    rw [e, ← ep, ← ek, ← eh]
    have : t * phi3 t - t * kt t - t * h2t t + 2 * (t * Real.sqrt (kt t * h2t t))
        = t * (phi3 t - kt t - h2t t + 2 * Real.sqrt (kt t * h2t t)) := by ring
    rw [this]; exact mul_nonneg ht.le T7
  · rw [← ep, ← eet]
    have : t * phi3 t + 5 * (t * et t) - 5 * t / 6 = t * (phi3 t + 5 * et t - 5 / 6) := by ring
    rw [this]; exact mul_nonneg ht.le T8
  · rw [← eet]
    have := mul_le_mul_of_nonneg_left T8b ht.le
    linarith

end

end PBC
end LeanCherry
