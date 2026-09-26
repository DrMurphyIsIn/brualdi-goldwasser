/-
  The `m ≥ 1` slice, part 2: the CONVEX-INTERPOLATION TOOLKIT.

  `StarBound`'s left side is `linear(Sg) + (11/50)·(1/(K+Sg) − T0)₊` — convex in `Sg` — while the
  right side is linear on each fold piece (`[0, m·T0]` and `[m·T0, m/2]`).  So the bound on a piece
  follows from its two ENDPOINTS by convex interpolation.  This file provides the toolkit:

  * `posPart_smul`, `posPart_combo` — the positive part respects convex combinations;
  * `inv_combo` — the inverse `1/(K+·)` lies below its chords (certificate `θ(1−θ)(p−q)² ≥ 0`);
  * `Pval_le_fold` — on `y < 1` (all `m ≥ 1` cavities), `Pval y ≤ (11/50)·(y − T0)₊`, so the
    fold form genuinely dominates (the only special point reachable is `y = 1/3`, where
    `−ω ≤ (11/50)(4/3 − rhoB)`).

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal
import R3Cert.PotentialClassify
import R3Cert.PotentialM0Region

namespace R3Cert

open Real

/-- `(t·u)₊ = t·u₊` for `t ≥ 0`. -/
theorem posPart_smul {t u : ℝ} (ht : 0 ≤ t) : max 0 (t * u) = t * max 0 u := by
  rcases le_total u 0 with h | h
  · have hn : (0 : ℝ) ≤ t * (-u) := mul_nonneg ht (by linarith)
    rw [max_eq_left (by nlinarith : t * u ≤ 0), max_eq_left h, mul_zero]
  · rw [max_eq_right (mul_nonneg ht h), max_eq_right h]

/-- The positive part of a convex combination is at most the combination of positive parts. -/
theorem posPart_combo {θ u v : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    max 0 (θ * u + (1 - θ) * v) ≤ θ * max 0 u + (1 - θ) * max 0 v := by
  calc max 0 (θ * u + (1 - θ) * v)
      ≤ max 0 (θ * u) + max 0 ((1 - θ) * v) := posPart_add_le _ _
    _ = θ * max 0 u + (1 - θ) * max 0 v := by
        rw [posPart_smul hθ0, posPart_smul (by linarith : (0 : ℝ) ≤ 1 - θ)]

/-- The convex-combination denominator is positive. -/
theorem combo_denom_pos {K p q θ : ℝ} (hKp : 0 < K + p) (hKq : 0 < K + q)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 < K + (θ * p + (1 - θ) * q) := by
  nlinarith [mul_nonneg hθ0 hKp.le, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) hKq.le,
    mul_nonneg hθ0 (sq_nonneg (K + p)), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) (sq_nonneg (K + q)),
    mul_pos hKp hKq]

/-- **The inverse lies below its chords:** for `θ ∈ [0,1]`,
    `1/(K + θp + (1−θ)q) ≤ θ/(K+p) + (1−θ)/(K+q)`  (certificate `θ(1−θ)(p−q)² ≥ 0`). -/
theorem inv_combo {K p q θ : ℝ} (hKp : 0 < K + p) (hKq : 0 < K + q)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 / (K + (θ * p + (1 - θ) * q)) ≤ θ / (K + p) + (1 - θ) / (K + q) := by
  have hD : 0 < K + (θ * p + (1 - θ) * q) := combo_denom_pos hKp hKq hθ0 hθ1
  rw [div_add_div _ _ (ne_of_gt hKp) (ne_of_gt hKq), div_le_div_iff₀ hD (mul_pos hKp hKq)]
  nlinarith [mul_nonneg (mul_nonneg hθ0 (by linarith : (0 : ℝ) ≤ 1 - θ)) (sq_nonneg (p - q))]

/-- `−ω ≤ (11/50)(4/3 − rhoB)`: the arm's special `Pval` value is below the linear fold. -/
theorem neg_omega_le_fold_third : -omegaVal ≤ (11 / 50) * (4 / 3 - rhoB) := by
  have hr2 : (0 : ℝ) < rhoB ^ 2 := pow_pos rhoB_pos 2
  have hpos : (0 : ℝ) < 2 * rhoB ^ 2 / 3 := by linarith
  have hup : -omegaVal ≤ 2 * rhoB ^ 2 / 3 - 1 := by
    rw [neg_omega_eq]
    exact Real.log_le_sub_one_of_pos hpos
  have hlt : rhoB < 123 / 100 := rhoB_lt_123
  have hsq : (0 : ℝ) < (123 / 100 - rhoB) * (123 / 100 + rhoB) :=
    mul_pos (sub_pos.2 hlt) (by linarith [rhoB_pos] : (0 : ℝ) < 123 / 100 + rhoB)
  nlinarith [hup, hsq, hlt]

/-- **`Pval` is dominated by the linear fold on `y < 1`** (all cavities in the `m ≥ 1` slice). -/
theorem Pval_le_fold {y : ℝ} (hy : y < 1) : Pval y ≤ (11 / 50) * max 0 (y - T0) := by
  by_cases h3 : y = 1 / 3
  · subst h3
    rw [Pval_third]
    have hge : (0 : ℝ) ≤ 1 / 3 - T0 := by
      unfold T0; linarith [rhoB_lt_four_thirds]
    rw [max_eq_right hge]
    have := neg_omega_le_fold_third
    unfold T0
    linarith [this]
  · exact le_of_eq (Pval_struct y h3 (ne_of_lt hy))

end R3Cert
