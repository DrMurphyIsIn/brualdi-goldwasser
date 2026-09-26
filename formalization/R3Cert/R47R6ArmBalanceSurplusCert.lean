/-
  R47 R6 arm-balancing surplus nonnegativity -- the consolidated, usable form.

  Combines the four arm-balancing bricks into a single statement: for ANY real-hub
  environment parameters `P >= 1` (the other-arm activity factor) and `z0 <= 1/6` (the hub
  coupling coefficient, `= 1/d` in the single-hub objective, so `z0 <= 1/6 <=> d >= 6`), the
  balancing-transfer surplus in the `(P, z0)` form is nonnegative:

      0 <= P * (Gn - Go) + z0 * (Gn Sn - Go So),

  with `Gn = abR(4+s) abR(4+s+t)`, `Go = abR(3+s) abR(5+s+t)`,
  `Sn = abH(4+s)+abH(4+s+t)`, `So = abH(3+s)+abH(5+s+t)` (the corner shift `a = 3+s`,
  `b = 5+s+t`).  This is EXACTLY the bracket of the general single-hub balancing-transfer
  Aobj change (verified: `dAobj = armProd(rest)*(3/2)^{c}*(3/2)^{a+b} * [that bracket]`),
  so it is the direct input to the Aobj-level connective identity.

  PROOF.  `armBalance_lift` (#110) bounds it below by the worst-case corner surplus
  `D = (Gn - Go) + (1/6)(Gn Sn - Go So)`, using the two sign facts `armBalance_Gmono` /
  `armBalance_Smono` (#111); `armBalance_Dred_eq` (#109) rewrites `D = num/den` with `num, den`
  the `R47ArmBalance` Polya certificate, and `positivity` gives `num/den >= 0`.

  HONEST SCOPE.  The consolidated arm-balancing surplus in `(P, z0)` form -- the usable input
  to the connective identity.  It does NOT include the connective identity itself (Aobj
  list-surgery), the transfer induction, nor the conjecture.  Self-contained (`import
  Mathlib` + the four arm-balancing bricks); genuine proof (no `sorry`, no `axiom`, no
  vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6ArmBalanceIdCert
import R3Cert.R47R6ArmBalanceLiftCert
import R3Cert.R47R6ArmBalanceSignCert

namespace R3Cert
namespace Step3

/-- **Consolidated arm-balancing surplus nonnegativity.**  For any `P ≥ 1`, `z0 ≤ 1/6`, the
    balancing-transfer surplus (in the environment `(P, z0)` form) is nonnegative. -/
theorem armBalance_surplus_nonneg (s t P z0 : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hP : 1 ≤ P) (hz0 : z0 ≤ 1 / 6) :
    0 ≤ P * (abR (4 + s) * abR (4 + s + t) - abR (3 + s) * abR (5 + s + t))
        + z0 * (abR (4 + s) * abR (4 + s + t) * (abH (4 + s) + abH (4 + s + t))
                - abR (3 + s) * abR (5 + s + t) * (abH (3 + s) + abH (5 + s + t))) := by
  have hlift := armBalance_lift P z0 (abR (4 + s) * abR (4 + s + t))
      (abR (3 + s) * abR (5 + s + t)) (abH (4 + s) + abH (4 + s + t))
      (abH (3 + s) + abH (5 + s + t)) hP hz0
      (armBalance_Gmono s t hs ht) (armBalance_Smono s t hs ht)
  have hD := armBalance_Dred_eq s t hs ht
  have hDnn : (0 : ℝ) ≤ (2 * t ^ 2 + 4 * s * t + 22 * t + 4 * s + 20)
      / (9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
         + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
         + 1980 * t + 5400) := by positivity
  rw [hD] at hlift
  linarith [hlift, hDnn]

end Step3
end R3Cert
