/-
  R47 R6 arm-balancing coupled comparison -- the Aobj-relevant form.

  The single-hub balancing-transfer Aobj change is (verified)
      dAobj = armProd(rest) * (3/2)^c * (3/2)^{a+b} * [Gn * Cnew - Go * Cold],
  where `Go = abR(3+s) abR(5+s+t)`, `Gn = abR(4+s) abR(4+s+t)` are the (rate-normalised)
  arm products, and the couplings are `Cold = P + z0 * So`, `Cnew = P + z0 * Sn` with the
  environment factor `P = 1 + Hrest/d + c/(3d) >= 1`, the hub coupling coefficient
  `z0 = 1/d <= 1/6` (for `d = |arms|+c >= 6`), and `So = abH(3+s)+abH(5+s+t)`,
  `Sn = abH(4+s)+abH(4+s+t)`.

  This brick proves the sign of that bracket directly: `Go * Cold <= Gn * Cnew`.  Because
  `Gn Cnew - Go Cold = P (Gn - Go) + z0 (Gn Sn - Go So)` (a `ring` identity), it is exactly
  `armBalance_surplus_nonneg` (#114).  All prefactors being positive, this gives the
  single-hub balancing transfer `dAobj >= 0` once the Aobj split identity is supplied.

  HONEST SCOPE.  The coupled arm-product comparison -- the algebraic heart of the connective
  identity, in the Aobj-relevant `G * C` form.  It does NOT include the Aobj list-split
  identity, the transfer induction, nor the conjecture.  Self-contained (`import Mathlib` +
  `R47R6ArmBalanceSurplusCert`); genuine proof (no `sorry`, no `axiom`, no vacuous
  hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6ArmBalanceSurplusCert

namespace R3Cert
namespace Step3

/-- **Coupled arm-product comparison.**  With environment factor `P ≥ 1` and hub coupling
    `z0 ≤ 1/6`, the balanced arm product times its coupling dominates the unbalanced one:
    `Go * (P + z0 * So) ≤ Gn * (P + z0 * Sn)`.  This is the sign of the single-hub balancing
    transfer's `Aobj` change (bracket), equal to `armBalance_surplus_nonneg` by `ring`. -/
theorem armBalance_coupled_le (s t P z0 : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hP : 1 ≤ P) (hz0 : z0 ≤ 1 / 6) :
    (abR (3 + s) * abR (5 + s + t)) * (P + z0 * (abH (3 + s) + abH (5 + s + t)))
      ≤ (abR (4 + s) * abR (4 + s + t)) * (P + z0 * (abH (4 + s) + abH (4 + s + t))) := by
  have h := armBalance_surplus_nonneg s t P z0 hs ht hP hz0
  have hid : (abR (4 + s) * abR (4 + s + t)) * (P + z0 * (abH (4 + s) + abH (4 + s + t)))
        - (abR (3 + s) * abR (5 + s + t)) * (P + z0 * (abH (3 + s) + abH (5 + s + t)))
      = P * (abR (4 + s) * abR (4 + s + t) - abR (3 + s) * abR (5 + s + t))
        + z0 * (abR (4 + s) * abR (4 + s + t) * (abH (4 + s) + abH (4 + s + t))
                - abR (3 + s) * abR (5 + s + t) * (abH (3 + s) + abH (5 + s + t))) := by ring
  linarith [h, hid]

end Step3
end R3Cert
