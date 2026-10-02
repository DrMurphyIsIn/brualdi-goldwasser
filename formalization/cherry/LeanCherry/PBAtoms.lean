/-
LeanCherry.PBAtoms -- the monotone atoms of the low-degree part (B) certificates.

Atoms (all in the variable t = lam/(2+lam)):
  Lm t  = -log(1-t)/t        increasing on (0,1), at least 1;
  Lg x  = log(1+x)/x         decreasing on (0,oo), at most 1   (L_a(t) = Lg(a t));
  Xe s  = (e^s-1)/s          increasing on (0,oo), at least 1;
  G2t t = G2(t)/t            increasing on (0,1/10], at least 1/12,
          G2 = 5 log(1+3t/4) - 7 log(1+2t/3) - log(1-t);
  kt, q3 increasing, y4 decreasing (rational functions);
  rhohat decreasing on [0,1], gS increasing on [0,oo) (the map g of the (S4) reduction).
Each monotonicity is proved once; on a box each atom is enclosed by its two endpoint values.
The numerical point bounds come from Taylor sums of exp (`expUp`, `expLo`).
-/
import Mathlib

open Real

namespace LeanCherry
namespace PBC

noncomputable section

/-! ### definitions -/

/-- `-log(1-t)/t` -/
def Lm (t : ℝ) : ℝ := -Real.log (1 - t) / t
/-- `log(1+x)/x` -/
def Lg (x : ℝ) : ℝ := Real.log (1 + x) / x
/-- `(e^s-1)/s` -/
def Xe (s : ℝ) : ℝ := (Real.exp s - 1) / s
/-- `G_2 = 5 log(1+3t/4) - 7 log(1+2t/3) - log(1-t)` -/
def G2 (t : ℝ) : ℝ := 5 * Real.log (1 + 3 * t / 4) - 7 * Real.log (1 + 2 * t / 3) - Real.log (1 - t)
/-- `G_2(t)/t` -/
def G2t (t : ℝ) : ℝ := G2 t / t
/-- `kappa/t` -/
def kt (t : ℝ) : ℝ := 2 / ((1 - t) * (3 + 2 * t))
/-- `lam y_3 / t` -/
def q3 (t : ℝ) : ℝ := 2 / ((1 - t) * (4 + 3 * t))
/-- `y_4` -/
def y4 (t : ℝ) : ℝ := 1 / (5 + 4 * t)
/-- the polynomial bound `rhohat` on `rho = D/sigma` -/
def rhohat (t : ℝ) : ℝ := 1 / 2 - t / 4 - 7 * t ^ 2 / 12 + t ^ 3 / 6
/-- the map `g(r) = r (1 - r/(8+6r))^3 (4+3r)` of the (S4) reduction -/
def gS (r : ℝ) : ℝ := r * (1 - r / (8 + 6 * r)) ^ 3 * (4 + 3 * r)

/-- upper Taylor bound of `exp` on `[0,1]` -/
def expUp (n : ℕ) (x : ℝ) : ℝ :=
  (∑ m ∈ Finset.range n, x ^ m / m.factorial) + x ^ n * (n + 1) / (n.factorial * n)
/-- lower Taylor bound of `exp` on `[0,oo)` -/
def expLo (n : ℕ) (x : ℝ) : ℝ := ∑ m ∈ Finset.range n, x ^ m / m.factorial

lemma exp_le_expUp {x : ℝ} (n : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (hn : 0 < n) : Real.exp x ≤ expUp n x :=
  Real.exp_bound' h0 h1 hn

lemma expLo_le_exp {x : ℝ} (n : ℕ) (h0 : 0 ≤ x) : expLo n x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg h0 n

/-! ### secant lemmas from convexity -/

lemma log_secant {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : x / y * Real.log (1 + y) ≤ Real.log (1 + x) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hb0 : 0 ≤ x / y := div_nonneg hx.le hy.le
  have hb1 : x / y ≤ 1 := (div_le_one hy).mpr hxy
  have key := strictConcaveOn_log_Ioi.concaveOn.2 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 + y ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith) (show 0 ≤ 1 - x / y by linarith) hb0
    (show 1 - x / y + x / y = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at key
  have e : (1 - x / y) * 1 + x / y * (1 + y) = 1 + x := by field_simp; ring
  rw [e] at key
  exact key

lemma log1m_secant {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    s / t * Real.log (1 - t) ≤ Real.log (1 - s) := by
  have htp : 0 < t := lt_of_lt_of_le hs hst
  have hb0 : 0 ≤ s / t := div_nonneg hs.le htp.le
  have hb1 : s / t ≤ 1 := (div_le_one htp).mpr hst
  have key := strictConcaveOn_log_Ioi.concaveOn.2 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 - t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith) (show 0 ≤ 1 - s / t by linarith) hb0
    (show 1 - s / t + s / t = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at key
  have e : (1 - s / t) * 1 + s / t * (1 - t) = 1 - s := by field_simp; ring
  rw [e] at key
  exact key

/-! ### Lg -/

lemma Lg_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Lg y ≤ Lg x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have k := log_secant hx hxy
  unfold Lg
  rw [div_le_div_iff₀ hy hx]
  have : x / y * Real.log (1 + y) * y = x * Real.log (1 + y) := by field_simp
  nlinarith

lemma Lg_le_one {x : ℝ} (hx : 0 < x) : Lg x ≤ 1 := by
  unfold Lg
  rw [div_le_one hx]
  have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + x)
  linarith

lemma Lg_pos {x : ℝ} (hx : 0 < x) : 0 < Lg x := by
  unfold Lg
  exact div_pos (Real.log_pos (by linarith)) hx

/-! ### Lm -/

lemma Lm_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) : Lm s ≤ Lm t := by
  have htp : 0 < t := lt_of_lt_of_le hs hst
  have k := log1m_secant hs hst ht
  unfold Lm
  rw [div_le_div_iff₀ hs htp]
  have : s / t * Real.log (1 - t) * t = s * Real.log (1 - t) := by field_simp
  nlinarith

lemma one_le_Lm {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 1 ≤ Lm t := by
  unfold Lm
  rw [le_div_iff₀ h0]
  have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 - t)
  linarith

/-! ### Xe -/

lemma Xe_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : Xe s ≤ Xe t := by
  have htp : 0 < t := lt_of_lt_of_le hs hst
  have hb0 : 0 ≤ s / t := div_nonneg hs.le htp.le
  have hb1 : s / t ≤ 1 := (div_le_one htp).mpr hst
  have key := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ t) (show 0 ≤ 1 - s / t by linarith) hb0
    (show 1 - s / t + s / t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at key
  have e : s / t * t = s := by field_simp
  rw [e] at key
  unfold Xe
  rw [div_le_div_iff₀ hs htp]
  have : s / t * Real.exp t * t = s * Real.exp t := by field_simp
  have : s / t * t = s := e
  nlinarith

lemma one_le_Xe {s : ℝ} (hs : 0 < s) : 1 ≤ Xe s := by
  unfold Xe
  rw [le_div_iff₀ hs]
  have := Real.add_one_le_exp s
  linarith

/-! ### G2 -/

/-- the derivative of `G2` -/
def G2d (x : ℝ) : ℝ := 5 * (3 / 4) / (1 + 3 * x / 4) - 7 * (2 / 3) / (1 + 2 * x / 3) + 1 / (1 - x)

lemma G2_hasDeriv {x : ℝ} (h0 : -1 < x) (h1 : x < 1) : HasDerivAt G2 (G2d x) x := by
  have a1 : HasDerivAt (fun y : ℝ => 1 + 3 * y / 4) (3 / 4) x := by
    have := ((hasDerivAt_id x).const_mul (3 : ℝ)).div_const 4
    simpa using this.const_add 1
  have a2 : HasDerivAt (fun y : ℝ => 1 + 2 * y / 3) (2 / 3) x := by
    have := ((hasDerivAt_id x).const_mul (2 : ℝ)).div_const 3
    simpa using this.const_add 1
  have a3 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have l1 := (a1.log (by linarith)).const_mul 5
  have l2 := (a2.log (by linarith)).const_mul 7
  have l3 := a3.log (by linarith)
  have := (l1.sub l2).sub l3
  have hf : G2 = fun y => 5 * Real.log (1 + 3 * y / 4) - 7 * Real.log (1 + 2 * y / 3) - Real.log (1 - y) := rfl
  have e : G2d x = 5 * (3 / 4 / (1 + 3 * x / 4)) - 7 * (2 / 3 / (1 + 2 * x / 3)) - -1 / (1 - x) := by
    unfold G2d; ring
  rw [hf, e]
  exact this

lemma G2d_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 10) : G2d x ≤ G2d y := by
  unfold G2d
  have n1 : (1:ℝ) + 3 * x / 4 ≠ 0 := by positivity
  have n2 : (1:ℝ) + 3 * y / 4 ≠ 0 := by have : 0 ≤ y := by linarith
                                        positivity
  have n3 : (1:ℝ) + 2 * x / 3 ≠ 0 := by positivity
  have n4 : (1:ℝ) + 2 * y / 3 ≠ 0 := by have : 0 ≤ y := by linarith
                                        positivity
  have n5 : (1:ℝ) - x ≠ 0 := by intro h; linarith
  have n6 : (1:ℝ) - y ≠ 0 := by intro h; linarith
  have n7 : (4:ℝ) + 3 * x ≠ 0 := by positivity
  have n8 : (4:ℝ) + 3 * y ≠ 0 := by have : 0 ≤ y := by linarith
                                    positivity
  have n9 : (3:ℝ) + 2 * x ≠ 0 := by positivity
  have n10 : (3:ℝ) + 2 * y ≠ 0 := by have : 0 ≤ y := by linarith
                                     positivity
  have e1 : 5 * (3 / 4) / (1 + 3 * x / 4) - 5 * (3 / 4) / (1 + 3 * y / 4)
      = 45 * (y - x) / ((4 + 3 * x) * (4 + 3 * y)) := by field_simp; ring
  have e2 : 7 * (2 / 3) / (1 + 2 * x / 3) - 7 * (2 / 3) / (1 + 2 * y / 3)
      = 28 * (y - x) / ((3 + 2 * x) * (3 + 2 * y)) := by field_simp; ring
  have e3 : 1 / (1 - y) - 1 / (1 - x) = (y - x) / ((1 - x) * (1 - y)) := by
    field_simp; ring
  have hd : 0 ≤ y - x := by linarith
  have b1 : 45 * (y - x) / ((4 + 3 * x) * (4 + 3 * y)) ≤ 45 * (y - x) / 16 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
  have b2 : 28 * (y - x) / (32 / 10 * (32 / 10)) ≤ 28 * (y - x) / ((3 + 2 * x) * (3 + 2 * y)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by nlinarith); nlinarith
  have b3 : (y - x) ≤ (y - x) / ((1 - x) * (1 - y)) := by
    rw [le_div_iff₀ (by nlinarith)]
    have : (1 - x) * (1 - y) ≤ 1 := by nlinarith
    nlinarith
  have : 28 * (y - x) / (32 / 10 * (32 / 10)) = (y - x) * (28 / (1024 / 100)) := by ring
  have : 45 * (y - x) / 16 = (y - x) * (45 / 16) := by ring
  nlinarith

lemma G2_zero : G2 0 = 0 := by simp [G2]

lemma G2_convex : ConvexOn ℝ (Set.Icc 0 (1 / 10)) G2 := by
  have hd : ∀ x ∈ Set.Icc (0:ℝ) (1 / 10), HasDerivAt G2 (G2d x) x := fun x hx =>
    G2_hasDeriv (by linarith [hx.1]) (by linarith [hx.2])
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 (1 / 10))
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hd x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(hd x (Set.Ioo_subset_Icc_self hx)).deriv, (hd y (Set.Ioo_subset_Icc_self hy)).deriv]
    exact G2d_mono hx.1.le hxy hy.2.le

lemma G2t_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1 / 10) : G2t s ≤ G2t t := by
  have htp : 0 < t := lt_of_lt_of_le hs hst
  have hb0 : 0 ≤ s / t := div_nonneg hs.le htp.le
  have hb1 : s / t ≤ 1 := (div_le_one htp).mpr hst
  have key := G2_convex.2 (show (0:ℝ) ∈ Set.Icc 0 (1 / 10) by constructor <;> norm_num)
    (show t ∈ Set.Icc 0 (1 / 10) from ⟨htp.le, ht⟩) (show 0 ≤ 1 - s / t by linarith) hb0
    (show 1 - s / t + s / t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, G2_zero] at key
  have e : s / t * t = s := by field_simp
  rw [e] at key
  unfold G2t
  rw [div_le_div_iff₀ hs htp]
  have : s / t * G2 t * t = s * G2 t := by field_simp
  nlinarith

lemma G2t_ge {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 10) : 1 / 12 ≤ G2t t := by
  have hd : ∀ x ∈ Set.Icc (0:ℝ) (1 / 10), HasDerivAt (fun y => G2 y - y / 12) (G2d x - 1 / 12) x := fun x hx =>
    (G2_hasDeriv (by linarith [hx.1]) (by linarith [hx.2])).sub ((hasDerivAt_id x).div_const 12)
  have hmono : MonotoneOn (fun y => G2 y - y / 12) (Set.Icc 0 (1 / 10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 10))
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x (Set.Ioo_subset_Icc_self hx)).deriv]
      have h := G2d_mono (le_refl 0) hx.1.le hx.2.le
      have h0' : G2d 0 = 1 / 12 := by norm_num [G2d]
      linarith
  have := hmono (a := 0) (b := t) (by constructor <;> norm_num) ⟨h0.le, h1⟩ h0.le
  simp only [G2_zero, zero_div, sub_zero] at this
  unfold G2t
  rw [le_div_iff₀ h0]
  linarith

/-! ### rational atoms -/

lemma kt_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) : kt s ≤ kt t := by
  unfold kt
  apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)

lemma q3_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) : q3 s ≤ q3 t := by
  unfold q3
  apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)

lemma y4_anti {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : y4 t ≤ y4 s := by
  unfold y4
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma rhohat_anti {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) : rhohat t ≤ rhohat s := by
  unfold rhohat
  have e : rhohat s - rhohat t = (t - s) * (1 / 4 + 7 * (s + t) / 12 - (s ^ 2 + s * t + t ^ 2) / 6) := by
    unfold rhohat; ring
  have h1 : 0 ≤ t - s := by linarith
  have h2 : 0 ≤ 1 / 4 + 7 * (s + t) / 12 - (s ^ 2 + s * t + t ^ 2) / 6 := by nlinarith
  have := mul_nonneg h1 h2
  unfold rhohat at e
  linarith

lemma gS_eq {r : ℝ} (hr : 0 ≤ r) : gS r = r * (8 + 5 * r) ^ 3 / (8 * (4 + 3 * r) ^ 2) := by
  unfold gS
  have h : (8:ℝ) + 6 * r ≠ 0 := by positivity
  have h' : (4:ℝ) + 3 * r ≠ 0 := by positivity
  field_simp
  ring

lemma gS_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : gS r ≤ gS s := by
  have hs : 0 ≤ s := le_trans hr hrs
  rw [gS_eq hr, gS_eq hs, div_le_div_iff₀ (by positivity) (by positivity)]
  set d := s - r with hd
  have hd0 : 0 ≤ d := by linarith
  have hsd : s = r + d := by rw [hd]; ring
  rw [hsd]
  have key : (r + d) * (8 + 5 * (r + d)) ^ 3 * (4 + 3 * r) ^ 2 - r * (8 + 5 * r) ^ 3 * (4 + 3 * (r + d)) ^ 2 =
      d * (1125*d^3*r^2 + 3000*d^3*r + 2000*d^3 + 4500*d^2*r^3 + 17400*d^2*r^2 + 22400*d^2*r + 9600*d^2
        + 5625*d*r^4 + 28800*d*r^3 + 55200*d*r^2 + 47232*d*r + 15360*d + 2250*r^5 + 14400*r^4 + 36800*r^3
        + 47232*r^2 + 30720*r + 8192) := by ring
  have : 0 ≤ d * (1125*d^3*r^2 + 3000*d^3*r + 2000*d^3 + 4500*d^2*r^3 + 17400*d^2*r^2 + 22400*d^2*r + 9600*d^2
        + 5625*d*r^4 + 28800*d*r^3 + 55200*d*r^2 + 47232*d*r + 15360*d + 2250*r^5 + 14400*r^4 + 36800*r^3
        + 47232*r^2 + 30720*r + 8192) := by positivity
  nlinarith

/-! ### numerical point bounds -/

lemma log_ge_of {y a : ℝ} (n : ℕ) (hy : 0 < y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hn : 0 < n)
    (h : expUp n a ≤ y) : a ≤ Real.log y :=
  (Real.le_log_iff_exp_le hy).mpr (le_trans (exp_le_expUp n ha0 ha1 hn) h)

lemma log_le_of {y b : ℝ} (n : ℕ) (hy : 0 < y) (hb0 : 0 ≤ b) (h : y ≤ expLo n b) : Real.log y ≤ b :=
  (Real.log_le_iff_le_exp hy).mpr (le_trans h (expLo_le_exp n hb0))

/-- `-log(1-p) >= a` from `expUp n a * (1-p) <= 1` -/
lemma nlog1m_ge {p a : ℝ} (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hn : 0 < n)
    (h : expUp n a * (1 - p) ≤ 1) : a ≤ -Real.log (1 - p) := by
  have hq : 0 < 1 - p := by linarith
  have h' : expUp n a ≤ 1 / (1 - p) := by rw [le_div_iff₀ hq]; exact h
  have := log_ge_of n (by positivity) ha0 ha1 hn h'
  rw [one_div, Real.log_inv] at this
  exact this

/-- `-log(1-p) <= b` from `1 <= expLo n b * (1-p)` -/
lemma nlog1m_le {p b : ℝ} (n : ℕ) (hp1 : p < 1) (hb0 : 0 ≤ b) (h : 1 ≤ expLo n b * (1 - p)) :
    -Real.log (1 - p) ≤ b := by
  have hq : 0 < 1 - p := by linarith
  have h' : 1 / (1 - p) ≤ expLo n b := by rw [div_le_iff₀ hq]; exact h
  have := log_le_of n (by positivity) hb0 h'
  rw [one_div, Real.log_inv] at this
  exact this

lemma Lm_ge_pt {p a : ℝ} (n : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hn : 0 < n)
    (h : expUp n a * (1 - p) ≤ 1) : a / p ≤ Lm p := by
  unfold Lm
  exact div_le_div_of_nonneg_right (nlog1m_ge n hp0.le hp1 ha0 ha1 hn h) hp0.le

lemma Lm_le_pt {p b : ℝ} (n : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hb0 : 0 ≤ b)
    (h : 1 ≤ expLo n b * (1 - p)) : Lm p ≤ b / p := by
  unfold Lm
  exact div_le_div_of_nonneg_right (nlog1m_le n hp1 hb0 h) hp0.le

lemma Lg_ge_pt {x a : ℝ} (n : ℕ) (hx : 0 < x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hn : 0 < n)
    (h : expUp n a ≤ 1 + x) : a / x ≤ Lg x := by
  unfold Lg
  exact div_le_div_of_nonneg_right (log_ge_of n (by linarith) ha0 ha1 hn h) hx.le

lemma Lg_le_pt {x b : ℝ} (n : ℕ) (hx : 0 < x) (hb0 : 0 ≤ b) (h : 1 + x ≤ expLo n b) : Lg x ≤ b / x := by
  unfold Lg
  exact div_le_div_of_nonneg_right (log_le_of n (by linarith) hb0 h) hx.le

lemma Xe_le_pt {s : ℝ} (n : ℕ) (hs : 0 < s) (hs1 : s ≤ 1) (hn : 0 < n) : Xe s ≤ (expUp n s - 1) / s := by
  unfold Xe
  exact div_le_div_of_nonneg_right (by linarith [exp_le_expUp n hs.le hs1 hn]) hs.le

lemma Xe_ge_pt {s : ℝ} (n : ℕ) (hs : 0 < s) : (expLo n s - 1) / s ≤ Xe s := by
  unfold Xe
  exact div_le_div_of_nonneg_right (by linarith [expLo_le_exp n hs.le]) hs.le

/-- `G2(p) >= 5 a1 - 7 b2 + a3` from bounds on the three logarithms -/
lemma G2t_ge_pt {p a1 b2 a3 : ℝ} (n1 n2 n3 : ℕ) (hp0 : 0 < p) (hp1 : p < 1)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1) (hn1 : 0 < n1) (h1 : expUp n1 a1 ≤ 1 + 3 * p / 4)
    (hb2 : 0 ≤ b2) (h2 : 1 + 2 * p / 3 ≤ expLo n2 b2)
    (ha3 : 0 ≤ a3) (ha3' : a3 ≤ 1) (hn3 : 0 < n3) (h3 : expUp n3 a3 * (1 - p) ≤ 1) :
    (5 * a1 - 7 * b2 + a3) / p ≤ G2t p := by
  have l1 := log_ge_of n1 (by linarith) ha1 ha1' hn1 h1
  have l2 := log_le_of n2 (by linarith) hb2 h2
  have l3 := nlog1m_ge n3 hp0.le hp1 ha3 ha3' hn3 h3
  unfold G2t G2
  apply div_le_div_of_nonneg_right _ hp0.le
  linarith

lemma G2t_le_pt {p b1 a2 b3 : ℝ} (n1 n2 n3 : ℕ) (hp0 : 0 < p) (hp1 : p < 1)
    (hb1 : 0 ≤ b1) (h1 : 1 + 3 * p / 4 ≤ expLo n1 b1)
    (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1) (hn2 : 0 < n2) (h2 : expUp n2 a2 ≤ 1 + 2 * p / 3)
    (hb3 : 0 ≤ b3) (h3 : 1 ≤ expLo n3 b3 * (1 - p)) :
    G2t p ≤ (5 * b1 - 7 * a2 + b3) / p := by
  have l1 := log_le_of n1 (by linarith) hb1 h1
  have l2 := log_ge_of n2 (by linarith) ha2 ha2' hn2 h2
  have l3 := nlog1m_le n3 hp1 hb3 h3
  unfold G2t G2
  apply div_le_div_of_nonneg_right _ hp0.le
  linarith

end

end PBC
end LeanCherry
