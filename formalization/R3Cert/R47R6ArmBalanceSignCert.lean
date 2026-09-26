/-
  R47 R6 arm-balancing coefficient-sign lemmas -- discharging the two hypotheses of
  `R47R6ArmBalanceLiftCert.armBalance_lift`.

  SOURCE: proof/verification/distribution.py (arm-balancing part (A): g log-concavity +
  the coupling-term sign).

  CONTEXT.  The P/z0 affine lift (`armBalance_lift`) is conditional on two coefficient-sign
  facts about the single-cherry balancing transfer `(a,b) -> (a+1,b-1)` at `a = 3+s`,
  `b = 5+s+t` (`s,t >= 0`), where `abR(c) = (4c+3)/(3c+3) = F(1,c)/(3/2)^c` and
  `abH(c) = 3/(4c+3) = z(1,c)` (from `R47R6ArmBalanceIdCert`):

    * `Go <= Gn`         -- balancing RAISES the arm rate product (`g` log-concavity), and
    * `Gn Sn <= Go So`   -- balancing LOWERS the coupling term.

  Both reduce (clearing the positive `(3c+3)`/`(4c+3)` denominators) to Polya
  nonnegative-coefficient numerators over positive denominators:
      Gn - Go       = (8 s t + 8 s + 4 t^2 + 43 t + 39) / den1,
      Go So - Gn Sn = (8 s t/3 + 8 s/3 + 4 t^2/3 + 14 t + 38/3) / den2,
  with `den1, den2 > 0`.  Verified in exact `sympy`.  These discharge the two hypotheses of
  `armBalance_lift`, so with `R47R6ArmBalanceIdCert` (corner surplus `= num/den >= 0`) the
  arm-balancing transfer objective change is `>= 0` on EVERY star -- unconditionally.

  HONEST SCOPE.  The two coefficient-sign facts at the certificate corner shift.  Together
  with the lift + reduced identity they close the arm-balancing MONOTONICITY (one arm
  transfer); they do NOT include the transfer induction to canonical form nor the
  conjecture.  Self-contained (`import Mathlib` + `R47R6ArmBalanceIdCert` for `abR`/`abH`);
  genuine proofs (no `sorry`, no `axiom`, no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6ArmBalanceIdCert

namespace R3Cert
namespace Step3

/-- **g-log-concavity (the P-coefficient sign).**  The balancing transfer raises the arm
    rate product: `abR(3+s)·abR(5+s+t) ≤ abR(4+s)·abR(4+s+t)`. -/
theorem armBalance_Gmono (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    abR (3 + s) * abR (5 + s + t) ≤ abR (4 + s) * abR (4 + s + t) := by
  rw [← sub_nonneg]
  have d1 : (3 * (4 + s) + 3 : ℝ) ≠ 0 := by positivity
  have d2 : (3 * (4 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have d3 : (3 * (3 + s) + 3 : ℝ) ≠ 0 := by positivity
  have d4 : (3 * (5 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have hden : (9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
      + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
      + 1980 * t + 5400 : ℝ) ≠ 0 := by positivity
  have key : abR (4 + s) * abR (4 + s + t) - abR (3 + s) * abR (5 + s + t)
      = (8 * s * t + 8 * s + 4 * t ^ 2 + 43 * t + 39)
        / (9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
           + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
           + 1980 * t + 5400) := by
    unfold abR; field_simp; ring
  rw [key]; positivity

/-- **Coupling sign (the z0-coefficient sign).**  The balancing transfer lowers the coupling
    term: `abR(4+s)·abR(4+s+t)·(abH(4+s)+abH(4+s+t)) ≤ abR(3+s)·abR(5+s+t)·(abH(3+s)+abH(5+s+t))`. -/
theorem armBalance_Smono (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    abR (4 + s) * abR (4 + s + t) * (abH (4 + s) + abH (4 + s + t))
      ≤ abR (3 + s) * abR (5 + s + t) * (abH (3 + s) + abH (5 + s + t)) := by
  rw [← sub_nonneg]
  have d1 : (3 * (4 + s) + 3 : ℝ) ≠ 0 := by positivity
  have d2 : (3 * (4 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have d3 : (3 * (3 + s) + 3 : ℝ) ≠ 0 := by positivity
  have d4 : (3 * (5 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have h1 : (4 * (4 + s) + 3 : ℝ) ≠ 0 := by positivity
  have h2 : (4 * (4 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have h3 : (4 * (3 + s) + 3 : ℝ) ≠ 0 := by positivity
  have h4 : (4 * (5 + s + t) + 3 : ℝ) ≠ 0 := by positivity
  have hden : (s ^ 4 + 2 * s ^ 3 * t + 20 * s ^ 3 + s ^ 2 * t ^ 2 + 29 * s ^ 2 * t
      + 149 * s ^ 2 + 9 * s * t ^ 2 + 139 * s * t + 490 * s + 20 * t ^ 2
      + 220 * t + 600 : ℝ) ≠ 0 := by positivity
  have key : abR (3 + s) * abR (5 + s + t) * (abH (3 + s) + abH (5 + s + t))
        - abR (4 + s) * abR (4 + s + t) * (abH (4 + s) + abH (4 + s + t))
      = (8 * s * t / 3 + 8 * s / 3 + 4 * t ^ 2 / 3 + 14 * t + 38 / 3)
        / (s ^ 4 + 2 * s ^ 3 * t + 20 * s ^ 3 + s ^ 2 * t ^ 2 + 29 * s ^ 2 * t
           + 149 * s ^ 2 + 9 * s * t ^ 2 + 139 * s * t + 490 * s + 20 * t ^ 2
           + 220 * t + 600) := by
    unfold abR abH; field_simp; ring
  rw [key]; positivity

end Step3
end R3Cert
