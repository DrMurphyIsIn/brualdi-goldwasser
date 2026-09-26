/-
  R47 R6 arm-balancing reduced-identity certificate -- connecting the R47ArmBalance
  Polya positivity core to the actual (reduced) transfer surplus.

  SOURCE: proof/verification/distribution.py, `certify_arm_balancing_symbolic` (exact).

  CONTEXT.  `R47ArmBalance` (on main) certifies the POSITIVITY of the Polya numerator/
  denominator `num, den` of the arm-balancing transfer surplus.  This brick supplies the
  missing ALGEBRAIC IDENTITY that ties `num/den` to the transfer's actual objective change.

  The single-cherry balancing transfer `(a,b) -> (a+1,b-1)` (spreading arm cherries toward
  balance, `b >= a+2`) changes the star objective, at the worst-case corner `P = 1`,
  `z0 = 1/6` (the 2-arm hub-3 star), by `D = (3/2)^{a+b} * Dred`.  Because the transfer
  CONSERVES `a + b`, the `(3/2)^{a+b}` factors CANCEL, so the reduced surplus
      Dred = [rr(a+1) rr(b-1) - rr(a) rr(b)]
             + (1/6) [rr(a+1) rr(b-1) (hh(a+1)+hh(b-1)) - rr(a) rr(b) (hh(a)+hh(b))],
  with `rr(c) = (4c+3)/(3c+3) = F(1,c)/(3/2)^c` and `hh(c) = 3/(4c+3) = z(1,c)`, is a PURE
  RATIONAL function (no symbolic exponents).  After the corner shift `a = 3+s`, `b = 5+s+t`
  (`s,t >= 0`) it equals exactly `num/den`, the `R47ArmBalance` Polya certificate:
      Dred = (2 t^2 + 4 s t + 22 t + 4 s + 20) / den(s,t).
  Verified in exact `sympy`.  With `R47ArmBalance` (`num >= 0`, `den > 0`) this gives
  `Dred >= 0`, hence `D >= 0`: the balancing transfer never decreases the objective.

  HONEST SCOPE.  The reduced worst-case identity only -- one composition step for the Hdom
  single-hub arm-balancing.  It does NOT include the `P`/`z0` affine-monotonicity lift to
  general stars, the transfer induction to the canonical form, nor the conjecture.
  Self-contained (`import Mathlib`); genuine proofs (no `sorry`, no `axiom`, no vacuous
  hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- Arm rate factor `rr(c) = (4c+3)/(3c+3) = F(1,c)/(3/2)^c`. -/
noncomputable def abR (c : ℝ) : ℝ := (4 * c + 3) / (3 * c + 3)

/-- Arm slot activity `hh(c) = 3/(4c+3) = z(1,c)`. -/
noncomputable def abH (c : ℝ) : ℝ := 3 / (4 * c + 3)

/-- **Arm-balancing reduced-surplus identity.**  At the worst-case corner (`P=1`, `z0=1/6`),
    the `(3/2)^{a+b}`-reduced transfer surplus `Dred` equals the `R47ArmBalance` Polya
    ratio `num/den` (`a = 3+s`, `b = 5+s+t`).  A pure rational identity. -/
theorem armBalance_Dred_eq (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (abR (4 + s) * abR (4 + s + t) - abR (3 + s) * abR (5 + s + t))
      + (1 / 6) * (abR (4 + s) * abR (4 + s + t) * (abH (4 + s) + abH (4 + s + t))
                   - abR (3 + s) * abR (5 + s + t) * (abH (3 + s) + abH (5 + s + t)))
      = (2 * t ^ 2 + 4 * s * t + 22 * t + 4 * s + 20)
        / (9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
           + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
           + 1980 * t + 5400) := by
  unfold abR abH
  have d1 : (3 * (4 + s) + 3 : ℝ) ≠ 0 := by positivity
  have d2 : (3 * (4 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have d3 : (3 * (3 + s) + 3 : ℝ) ≠ 0 := by positivity
  have d4 : (3 * (5 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have h1 : (4 * (4 + s) + 3 : ℝ) ≠ 0 := by positivity
  have h2 : (4 * (4 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have h3 : (4 * (3 + s) + 3 : ℝ) ≠ 0 := by positivity
  have h4 : (4 * (5 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have hden : (9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
      + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
      + 1980 * t + 5400 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Step3
end R3Cert
