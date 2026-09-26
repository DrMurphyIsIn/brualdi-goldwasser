/-
  R47 R6 arm-balancing P/z0 affine lift -- the general-star surplus is bounded below by
  the worst-case corner surplus.

  SOURCE: proof/verification/distribution.py, arm-balancing part (A): "Delta is AFFINE and
  increasing in P (>= 1) and affine in z0 (in (0, 1/6]); its joint minimum is the 2-arm
  hub-3 star (P = 1, z0 = 1/6)."

  CONTEXT.  For a general star the single-cherry balancing transfer `(a,b) -> (a+1,b-1)`
  changes the objective by
      Delta = P * (Gn - Go) + z0 * (Gn * Sn - Go * So),
  where `Go = g(a) g(b)`, `Gn = g(a+1) g(b-1)`, `So = h(a)+h(b)`, `Sn = h(a+1)+h(b-1)`,
  `P = 1 + z0 * (other-arm activities) >= 1`, and `z0 in (0, 1/6]`.  The worst-case corner
  surplus is `D = Delta` at `P = 1`, `z0 = 1/6` -- exactly the quantity `R47ArmBalance` /
  `R47R6ArmBalanceIdCert` certify as `num/den >= 0`.

  This brick supplies the LIFT: given the two coefficient-sign facts
      Go <= Gn                (g is log-concave: balancing raises the arm product), and
      Gn * Sn <= Go * So      (the coupling term decreases under balancing),
  the general-star surplus dominates the corner surplus, `D <= Delta`, for every admissible
  `P >= 1`, `0 < z0 <= 1/6`.  The mechanism is the exact affine identity
      Delta - D = (P - 1) (Gn - Go) + (1/6 - z0) (Go * So - Gn * Sn),
  a sum of two nonnegative products.  Hence with `D >= 0` (the certified corner) the FULL
  transfer surplus is `>= 0`: balancing never decreases the objective on any star.

  HONEST SCOPE.  The affine-lift mechanism, conditional on the two coefficient-sign facts
  (which are the substantive `g`-log-concavity / coupling lemmas, dischargeable separately
  -- NOT vacuous).  It does NOT discharge those signs, the transfer induction, nor the
  conjecture.  Self-contained (`import Mathlib`); genuine proof (no `sorry`, no `axiom`, no
  vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **The arm-balancing P/z0 affine lift.**  If the balancing transfer raises the arm
    product (`Go ≤ Gn`) and lowers the coupling (`Gn·Sn ≤ Go·So`), then the general-star
    surplus `Delta` dominates the worst-case corner surplus `D` for every `P ≥ 1`,
    `0 < z0 ≤ 1/6`. -/
theorem armBalance_lift
    (P z0 Gn Go Sn So : ℝ)
    (hP : 1 ≤ P) (hz0hi : z0 ≤ 1 / 6)
    (hGmono : Go ≤ Gn) (hSmono : Gn * Sn ≤ Go * So) :
    (Gn - Go) + (1 / 6) * (Gn * Sn - Go * So)
      ≤ P * (Gn - Go) + z0 * (Gn * Sn - Go * So) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hGmono),
             mul_nonneg (sub_nonneg.mpr hz0hi) (sub_nonneg.mpr hSmono)]

end Step3
end R3Cert
