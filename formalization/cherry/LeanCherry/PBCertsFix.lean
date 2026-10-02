/-
LeanCherry.PBCertsFix -- audit 10 fixes for the low-degree part (B) certificates.

* The hand step of (S6) on [lam_D2, 2], i.e. t in [t_D2, 1/2] with t_D2 = (sqrt 7 - 2)/2:
  there D(2) <= 0 (iff 4t^2 + 8t - 3 >= 0) and delta = t - kappa >= 0, so for every eps > 0 and u > 0,
  Psi = eps (3/2 + delta/u) - D(2) >= (3/2) eps > 0.
* `cert_S6_full`: on t in [3/43, 6181/10000] (lam in [3/20, 3.237]) one of C7, the hand step, C8 applies;
  the three ranges [3/43, 3229/10000], [t_D2, 1/2], [1/2, 6181/10000] overlap (t_D2 < 3229/10000).
* the monotonicity facts used by the reductions, named as in the note: `mono_g`, `mono_r`, `mono_Lq`.
-/
import LeanCherry.PBCerts

open Real

namespace LeanCherry
namespace PBC

noncomputable section

/-- `t_D2 = (sqrt 7 - 2)/2`, i.e. `lam_D2 = 0.95367...` -/
def tD2 : ℝ := (Real.sqrt 7 - 2) / 2

lemma tD2_sq : 4 * tD2 ^ 2 + 8 * tD2 - 3 = 0 := by
  unfold tD2
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)
  nlinarith [h]

lemma tD2_pos : 0 < tD2 := by
  unfold tD2
  have : (2:ℝ) < Real.sqrt 7 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- the hand-step range starts inside the C7 range: `t_D2 < 3229/10000` -/
lemma tD2_lt : tD2 < 3229 / 10000 := by
  unfold tD2
  have : Real.sqrt 7 < 26458 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- `D(2) <= 0` exactly when `4t^2 + 8t - 3 >= 0` (for `0 < t < 1`) -/
lemma D2_nonpos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (h : 0 ≤ 4 * t ^ 2 + 8 * t - 3) : D2 t ≤ 0 := by
  unfold D2 ell
  have hp : 0 < (1 + 2 * t / 3) ^ 2 * (1 - t) := by
    have : 0 < 1 - t := by linarith
    positivity
  have key : (1 + 2 * t / 3) ^ 2 * (1 - t) ≤ 1 := by
    have e : 1 - (1 + 2 * t / 3) ^ 2 * (1 - t) = t * (4 * t ^ 2 + 8 * t - 3) / 9 := by ring
    have : 0 ≤ t * (4 * t ^ 2 + 8 * t - 3) / 9 := by positivity
    linarith
  have hl := Real.log_nonpos hp.le key
  rw [Real.log_mul (by positivity) (by linarith), Real.log_pow] at hl
  push_cast at hl
  linarith

lemma D2_nonpos_of_ge {t : ℝ} (h0 : tD2 ≤ t) (h1 : t < 1) : D2 t ≤ 0 := by
  have hp := tD2_pos
  apply D2_nonpos (by linarith) h1
  have := tD2_sq
  nlinarith

/-- `delta = t - kappa >= 0` for `0 <= t <= 1/2` -/
lemma delta_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 0 ≤ t - kap t := by
  unfold kap
  have hd : 0 < (1 - t) * (3 + 2 * t) := by
    have : 0 < 1 - t := by linarith
    positivity
  have e : t - 2 * t / ((1 - t) * (3 + 2 * t)) = t * (1 - 2 * t) * (1 + t) / ((1 - t) * (3 + 2 * t)) := by
    have h1t : (1 - t) ≠ 0 := by intro h; linarith
    have h3 : (3 + 2 * t) ≠ 0 := by intro h; linarith
    field_simp
    ring
  rw [e]
  apply div_nonneg _ hd.le
  have : 0 ≤ 1 - 2 * t := by linarith
  positivity

/-- **(S6) hand step on `[lam_D2, 2]`**: for every `eps > 0` and `u = 1 + t - E > 0`,
    `Psi = eps (3/2 + (t - kappa)/u) - D(2) > 0` (indeed `>= (3/2) eps`). -/
theorem cert_S6_mid (t : ℝ) (h1 : tD2 ≤ t) (h2 : t ≤ 1 / 2) (eps E : ℝ) (heps : 0 < eps)
    (hu : 0 < 1 + t - E) : 0 < eps * (3 / 2 + (t - kap t) / (1 + t - E)) - D2 t := by
  have ht : 0 < t := lt_of_lt_of_le tD2_pos h1
  have hD := D2_nonpos_of_ge h1 (by linarith)
  have hd := delta_nonneg ht.le h2
  have hq : 0 ≤ (t - kap t) / (1 + t - E) := div_nonneg hd hu.le
  nlinarith

/-- **(S6) on all of `t in [3/43, 6181/10000]`** (`lam in [3/20, 3.237] ⊇ [3/20, lam_c)`): every `t` lies in
    the C7 range, the hand-step range, or the C8 range, and the corresponding inequality holds. -/
theorem cert_S6_full (t : ℝ) (h1 : 3 / 43 ≤ t) (h2 : t ≤ 6181 / 10000) :
    (t ≤ 3229 / 10000 ∧ 0 < 1 + t - E3 t ∧ 0 < eps3 t * (3 / 2 + (t - kap t) / (1 + t - E3 t)) - D2 t) ∨
    (tD2 ≤ t ∧ t ≤ 1 / 2 ∧ ∀ eps E : ℝ, 0 < eps → 0 < 1 + t - E →
      0 < eps * (3 / 2 + (t - kap t) / (1 + t - E)) - D2 t) ∨
    (1 / 2 ≤ t ∧ kap t * (1 / (3 + 2 * t) - (1 - t) / 2) < -D2 t) := by
  rcases le_or_gt t (3229 / 10000) with ha | ha
  · exact Or.inl ⟨ha, cert_C7 t h1 ha⟩
  · rcases le_or_gt t (1 / 2) with hb | hb
    · exact Or.inr (Or.inl ⟨le_of_lt (lt_trans tD2_lt ha), hb,
        fun eps E he hu => cert_S6_mid t (le_of_lt (lt_trans tD2_lt ha)) hb eps E he hu⟩)
    · exact Or.inr (Or.inr ⟨hb.le, cert_C8 t hb.le h2⟩)

/-! ### named monotonicity facts -/

/-- **mono_g**: `g(r) = r (1 - r/(8+6r))^3 (4+3r)` is increasing on `[0, 1/2]` (on `[0, oo)` in fact). -/
theorem mono_g : MonotoneOn gS (Set.Icc 0 (1 / 2)) :=
  fun _ hr _ _ hrs => gS_mono hr.1 hrs

/-- **mono_r**: `r(t) = kappa (y2 - yC)/t = (2t-1)(1+t)/((1-t)(3+2t)^2)` is increasing on
    `[1/2, 6181/10000] ⊇ [1/2, 1/phi]`. -/
theorem mono_r : MonotoneOn r8 (Set.Icc (1 / 2) (6181 / 10000)) :=
  fun _ hs _ ht hst => r8_mono hs.1 hst (by linarith [ht.2])

/-- **mono_Lq**: `L_q(t) = log(1+x)/x` at `x = t q3(t) = lam y3` is decreasing in `t` on `(0, 6181/10000]`. -/
theorem mono_Lq : AntitoneOn (fun t => Lg (t * q3 t)) (Set.Ioc 0 (6181 / 10000)) :=
  fun _ hs _ ht hst => Lg_anti (xq_pos hs.1 (by linarith [hs.2])) (xq_mono hs.1.le hst (by linarith [ht.2]))

end

end PBC
end LeanCherry
