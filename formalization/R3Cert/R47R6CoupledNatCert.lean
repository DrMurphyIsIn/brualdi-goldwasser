/-
  R47 R6 arm-balancing coupled comparison, Nat-indexed form.

  Bridges `R47R6ArmBalanceCoupledCert.armBalance_coupled_le` (stated at the Polya corner
  shift `a = 3+s`, `b = 5+s+t`, `s,t >= 0`) to concrete integer arm cherry-counts `a, b`
  with `3 <= a` and `a + 2 <= b`, by instantiating `s = a-3`, `t = b-a-2` and rewriting the
  four shifted arguments back to `a, a+1, b, b-1` (exact `ring` identities on the reals).

  This is the arm-index form of the single-hub balancing-transfer surplus sign: with the
  environment factor `P >= 1` and hub coupling `z0 <= 1/6`, the balanced arm pair `(a+1,b-1)`
  dominates the unbalanced `(a,b)` in the Aobj-relevant `G * C` form.  It is the direct input
  to the Aobj list-split comparison (arm value `Ztot_dtSub_armU(a) = (3/2)^a * abR(a)`).

  HONEST SCOPE.  The Nat-indexed coupled comparison -- one step of the connective identity.
  It does NOT include the Aobj list-split, the induction, nor the conjecture.  Self-contained
  (`import Mathlib` + `R47R6ArmBalanceCoupledCert`); genuine proof (no `sorry`, no `axiom`,
  no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6ArmBalanceCoupledCert

namespace R3Cert
namespace Step3

/-- **Coupled comparison, Nat-indexed.**  For integer arm counts `3 ≤ a`, `a+2 ≤ b`, and
    environment `P ≥ 1`, `z0 ≤ 1/6`, the balanced pair dominates:
    `abR a · abR b · (P + z0(abH a + abH b)) ≤ abR (a+1) · abR (b-1) · (P + z0(abH (a+1) + abH (b-1)))`. -/
theorem armBalance_coupled_le_nat (a b : ℕ) (ha : 3 ≤ a) (hb : a + 2 ≤ b) (P z0 : ℝ)
    (hP : 1 ≤ P) (hz0 : z0 ≤ 1 / 6) :
    abR (a : ℝ) * abR (b : ℝ) * (P + z0 * (abH (a : ℝ) + abH (b : ℝ)))
      ≤ abR ((a : ℝ) + 1) * abR ((b : ℝ) - 1)
        * (P + z0 * (abH ((a : ℝ) + 1) + abH ((b : ℝ) - 1))) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (a : ℝ) + 2 ≤ (b : ℝ) := by exact_mod_cast hb
  have hs : (0 : ℝ) ≤ (a : ℝ) - 3 := by linarith
  have ht : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) - 2 := by linarith
  have key := armBalance_coupled_le ((a : ℝ) - 3) ((b : ℝ) - (a : ℝ) - 2) P z0 hs ht hP hz0
  have e1 : (3 : ℝ) + ((a : ℝ) - 3) = (a : ℝ) := by ring
  have e2 : (5 : ℝ) + ((a : ℝ) - 3) + ((b : ℝ) - (a : ℝ) - 2) = (b : ℝ) := by ring
  have e3 : (4 : ℝ) + ((a : ℝ) - 3) = (a : ℝ) + 1 := by ring
  have e4 : (4 : ℝ) + ((a : ℝ) - 3) + ((b : ℝ) - (a : ℝ) - 2) = (b : ℝ) - 1 := by ring
  rw [e2, e4, e1, e3] at key
  exact key

end Step3
end R3Cert
