/-
  R3Cert.BGEnvCert.Tangent -- the tangent of `φ(x) = log x + μ/x` (2026-09-25).

  For `0 ≤ μ`, `2μ ≤ u` and `2μ ≤ x`:
      `log x + μ/x ≤ log u + μ/u + ν (x - u)`,   `ν = φ'(u) = (u - μ)/u²`
  (`φ` is concave on `[2μ, ∞)`).  With `r = x/u` this is `log r ≤ (r-1) - (μ/u)(r-1)²/r`, from
  `log r ≤ sinh(log r) = (r - 1/r)/2` (`r ≥ 1`) and `log r ≤ (r-1) - (r-1)²/2` (`r ≤ 1`).
  `TanB` is the per-vertex Bellman step in the form the envelope induction consumes.
  No `sorry`; standard axioms only.
-/
import Mathlib

namespace R3Cert
namespace EnvCert

open Real

theorem log_le_sinh_form {r : ℝ} (hr : 1 ≤ r) : Real.log r ≤ (r - r⁻¹) / 2 := by
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hr)
  rwa [Real.sinh_log (by linarith)] at h

theorem log_le_quad {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : Real.log r ≤ (r - 1) - (r - 1) ^ 2 / 2 := by
  set y := 1 - r with hy
  have hy0 : 0 ≤ y := by linarith
  have hy1 : |y| < 1 := by rw [abs_of_nonneg hy0]; linarith
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hy1
  have hle : ∑ i ∈ Finset.range 2, y ^ (i + 1) / (i + 1) ≤ -Real.log (1 - y) :=
    sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
  simp [Finset.sum_range_succ] at hle
  rw [show 1 - y = r by rw [hy]; ring] at hle
  nlinarith

theorem tan_ineq {μ u x : ℝ} (hμ : 0 ≤ μ) (hu : 2 * μ ≤ u) (hx : 2 * μ ≤ x) (hu0 : 0 < u) (hx0 : 0 < x) :
    Real.log x + μ / x ≤ Real.log u + μ / u + (u - μ) / u ^ 2 * (x - u) := by
  set r := x / u with hr
  have hr0 : 0 < r := div_pos hx0 hu0
  have hxr : x = r * u := by rw [hr]; field_simp
  have hlog : Real.log x = Real.log u + Real.log r := by
    rw [hxr, Real.log_mul hr0.ne' hu0.ne']; ring
  have key : μ / u - μ / x + (u - μ) / u ^ 2 * (x - u) = (r - 1) - (μ / u) * (r - 1) ^ 2 / r := by
    rw [hxr]; field_simp; ring
  suffices h : Real.log r ≤ (r - 1) - (μ / u) * (r - 1) ^ 2 / r by linarith
  have hk0 : 0 ≤ μ / u := div_nonneg hμ hu0.le
  have hk1 : μ / u ≤ 1 / 2 := by rw [div_le_iff₀ hu0]; linarith
  rcases le_or_gt 1 r with h1 | h1
  · have hs := log_le_sinh_form h1
    have hq : (r - r⁻¹) / 2 ≤ (r - 1) - (μ / u) * (r - 1) ^ 2 / r := by
      have : (r - 1) - (μ / u) * (r - 1) ^ 2 / r - (r - r⁻¹) / 2 = (r - 1) ^ 2 * (1 - 2 * (μ / u)) / (2 * r) := by
        field_simp; ring
      have : 0 ≤ (r - 1) ^ 2 * (1 - 2 * (μ / u)) / (2 * r) := by
        apply div_nonneg _ (by linarith); apply mul_nonneg (sq_nonneg _); linarith
      linarith
    linarith
  · have hq := log_le_quad hr0 h1.le
    -- `μ/(u r) = μ/x ≤ 1/2`
    have hkr : (μ / u) / r ≤ 1 / 2 := by
      rw [div_div, show u * r = x by rw [hxr]; ring, div_le_iff₀ hx0]; linarith
    have : (μ / u) * (r - 1) ^ 2 / r ≤ (r - 1) ^ 2 / 2 := by
      rw [show (μ / u) * (r - 1) ^ 2 / r = ((μ / u) / r) * (r - 1) ^ 2 by field_simp]
      nlinarith [sq_nonneg (r - 1)]
    linarith

/-- **The per-vertex Bellman step** at a vertex with `c` children, parent price `μ`, child price
    `ν` and constant `T`: for every children field-sum `S ≥ 0`,
    `log(1 + S/(c+1)) + μ/((c+1) + S) - f ≤ T + ν S`. -/
def TanB (f μ ν : ℝ) (c : ℕ) (T : ℝ) : Prop :=
  ∀ S : ℝ, 0 ≤ S → Real.log (1 + S / ((c : ℝ) + 1)) + μ / (((c : ℝ) + 1) + S) - f ≤ T + ν * S

/-- `TanB` from a tangent point `u` and rational bounds of its constants. -/
theorem tanB_of {f μ ν u A N Ld : ℝ} (c : ℕ) (hμ0 : 0 ≤ μ) (hμ1 : 2 * μ ≤ (c : ℝ) + 1) (hu0 : 0 < u)
    (hu : 2 * μ ≤ u) (hν : (u - μ) / u ^ 2 ≤ ν) (hN : (u - μ) / u ^ 2 ≤ N)
    (hA : Real.log u + 2 * μ / u - 1 - f ≤ A) (hLd : Ld ≤ Real.log ((c : ℝ) + 1)) :
    TanB f μ ν c (A + N * ((c : ℝ) + 1) - Ld) := by
  intro S hS
  have hd : (1 : ℝ) ≤ (c : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) c; linarith
  set x := ((c : ℝ) + 1) + S with hx
  have hx0 : 0 < x := by linarith
  have hx2 : 2 * μ ≤ x := by rw [hx]; linarith
  have hl : Real.log (1 + S / ((c : ℝ) + 1)) = Real.log x - Real.log ((c : ℝ) + 1) := by
    rw [show 1 + S / ((c : ℝ) + 1) = x / ((c : ℝ) + 1) by rw [hx]; field_simp,
      Real.log_div hx0.ne' (by linarith)]
  have ht := tan_ineq hμ0 hu hx2 hu0 hx0
  set ν0 := (u - μ) / u ^ 2 with hν0
  have hνu : ν0 * u = 1 - μ / u := by rw [hν0]; field_simp
  have hν00 : 0 ≤ ν0 ∨ ν0 < 0 := le_or_gt 0 ν0
  have e1 : ν0 * (x - u) = ν0 * ((c : ℝ) + 1) + ν0 * S - ν0 * u := by rw [hx]; ring
  have e2 : ν0 * ((c : ℝ) + 1) ≤ N * ((c : ℝ) + 1) := mul_le_mul_of_nonneg_right hN (by linarith)
  have e3 : ν0 * S ≤ ν * S := mul_le_mul_of_nonneg_right hν hS
  rw [hl]
  have : Real.log u + μ / u - ν0 * u ≤ A + f := by
    rw [hνu]; linarith [show 2 * μ / u = μ / u + μ / u by ring]
  linarith

end EnvCert
end R3Cert
