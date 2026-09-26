/-
  The `m ≥ 1` slice, part 1: TANGENT-AT-THE-TIE reduction and the slice assembler.

  The tangent bound `log(1+x) ≤ L + (x − T0)/rhoB` (concavity of `log`, tangent at the tie point
  `x = T0` where `log(1+T0) = L` exactly) removes the transcendental from the `m ≥ 1` deficit: the
  strengthened statement `StarBound` is a rational inequality in `(a, nl, m, Sg, rhoB)`.  It holds
  for all `m ≥ 1` (numerically verified; margin `→ 0` as `m → ∞` — the accumulating tie is absorbed
  exactly by the tangent slack `T0/(rhoB(m+1))`), though NOT for `m = 0` — which is why the `m = 0`
  slice is proven separately (`deficit_m0`).

  `deficitNonneg_of_slices` assembles: `DeficitNonneg ⟸ deficit_m0 (proven) + StarBound (open)`.
  After this file the remaining mathematical content of the conjecture is `StarBound` alone.

  Genuine proofs (no `sorry`).  `StarBound` is NOT proven here (next: convex-in-`Sg` endpoint
  interpolation reducing it to three endpoint families `Sg ∈ {0, m·T0, m/2}`).
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialAssembly
import R3Cert.PotentialM0Region

namespace R3Cert

open Real

/-- **Tangent to `log(1+·)` at the tie `x = T0`:** `log(1+x) ≤ L + (x − T0)/rhoB`
    (`log y ≤ log ρ + (y−ρ)/ρ`, i.e. `log(y/ρ) ≤ y/ρ − 1`). -/
theorem log_tangent_tie {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ Lval + (x - T0) / rhoB := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hq : (0 : ℝ) < (1 + x) / rhoB := div_pos h1x rhoB_pos
  have heq : Real.log ((1 + x) / rhoB) = Real.log (1 + x) - Lval := by
    rw [Real.log_div (ne_of_gt h1x) (ne_of_gt rhoB_pos), logRhoB_local]
  have hle := Real.log_le_sub_one_of_pos hq
  rw [heq] at hle
  have hexp : (1 + x) / rhoB - 1 = (x - T0) / rhoB := by
    rw [show (x - T0) = (1 + x) - rhoB from by unfold T0; ring, ← div_sub_div_same,
        div_self (ne_of_gt rhoB_pos)]
  linarith [hle, hexp.le, hexp.ge]

/-- **The tangent-strengthened `m ≥ 1` crux** — a rational inequality, no logs. -/
def StarBound : Prop :=
  ∀ (a nl m : ℕ) (Sg : ℝ), 1 ≤ m → 0 ≤ Sg → Sg ≤ (m : ℝ) / 2 →
    (((a : ℝ) / 3 + nl + Sg) / ((a : ℝ) + nl + m + 1) - T0) / rhoB
        + Pval (1 / ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + Sg)))
      ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval
        + (11 / 50) * max 0 (Sg - (m : ℝ) * T0)

/-- **`DeficitNonneg ⟸ deficit_m0 + StarBound`.**  After this, the whole conjecture rests on
    `StarBound`. -/
theorem deficitNonneg_of_star (hS : StarBound) : DeficitNonneg := by
  intro a nl m Sg hSg0 hSgh
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- m = 0: Sg = 0, convert to the proven deficit_m0
    subst hm0
    have hSg : Sg = 0 := le_antisymm (by simpa using hSgh) hSg0
    subst hSg
    have h := deficit_m0 a nl
    have hp1 : ((a : ℝ) + ↑nl + 1) ≠ 0 := by positivity
    have hp2 : (4 * (a : ℝ) + 6 * ↑nl + 3) ≠ 0 := by positivity
    have e1 : 1 + ((a : ℝ) / 3 + ↑nl + 0) / ((a : ℝ) + ↑nl + ↑(0 : ℕ) + 1)
        = (4 * (a : ℝ) + 6 * (nl : ℝ) + 3) / (3 * ((a : ℝ) + (nl : ℝ) + 1)) := by
      push_cast
      simp only [add_zero]
      rw [one_add_div hp1, div_eq_div_iff hp1 (by positivity)]
      ring
    have e2 : 1 / ((a : ℝ) + ↑nl + ↑(0 : ℕ) + 1 + ((a : ℝ) / 3 + ↑nl + 0))
        = 3 / (4 * (a : ℝ) + 6 * (nl : ℝ) + 3) := by
      push_cast
      simp only [add_zero]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [e1, e2]
    have e3 : (11 / 50 : ℝ) * max 0 (0 - ↑(0 : ℕ) * T0) = 0 := by
      norm_num
    rw [e3]
    linarith [h]
  · -- m ≥ 1: tangent + StarBound
    have hN : (0 : ℝ) < (a : ℝ) + ↑nl + ↑m + 1 := by positivity
    have hSnn : (0 : ℝ) ≤ ((a : ℝ) / 3 + ↑nl + Sg) / ((a : ℝ) + ↑nl + ↑m + 1) := by
      apply div_nonneg _ hN.le
      have ha3 : (0 : ℝ) ≤ (a : ℝ) / 3 := by positivity
      have hnl0 : (0 : ℝ) ≤ (nl : ℝ) := Nat.cast_nonneg nl
      linarith [hSg0]
    have htan := log_tangent_tie hSnn
    have hstar := hS a nl m Sg hm1 hSg0 hSgh
    linarith [htan, hstar]

/-- **The whole conjecture, conditional on `StarBound` alone:** `Φ ≤ 1` for every branch. -/
theorem phi_le_one_of_star (hS : StarBound) (b : Branch) : logPhi b ≤ 0 :=
  phi_le_one_of_deficitNonneg (deficitNonneg_of_star hS) b

end R3Cert
