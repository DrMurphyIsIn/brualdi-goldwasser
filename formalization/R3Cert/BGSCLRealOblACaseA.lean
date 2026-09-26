/-
  RealObligationA — Case A (leaf-path-extension) Aobj-monotonicity certificate.

  The straightening move for Hnorm (`R3Cert.Step3.RealObligationA`, `BGSCLObligationA.lean`) requires a
  size-preserving SPR move that strictly drops `strDefect` and does NOT decrease `Aobj`.  The taxonomy sweep
  (`telperion/scratch/a7_taxonomy.py`, exact n ≤ 12) shows **92% (17567/19099)** of defective trees are
  straightened by a LEAF move (Type L) — a leaf-onto-leaf PATH-EXTENSION inside the deepest defect's subtree.

  For that move the `Aobj` increment has the exact closed form (derived + verified vs the exact cavity engine
  in `telperion/scratch/a3_F2_closed.py`):

      ΔAobj  =  P · (n² + n·Q + 4·Q) / (2·(n+1)·(n+2)),

  where `P = ∏ Ztot(child) > 0`, `Q` a `qSum` term ≥ 0, and `n` a child count ≥ 0.  Since every factor is
  nonnegative and the denominator is positive, **ΔAobj ≥ 0** — the Case-A `Aobj t ≤ Aobj (f t)` clause.

  This file kernel-certifies that sign fact (the numerator and the packaged increment).  It is the `Aobj`
  clause of the Case-A leaf-path-extension move; the remaining structural obligation is to prove, in the
  cavity model, that the move's actual `Aobj` increment EQUALS this closed form (then this certificate
  discharges non-negativity).  The Type-W residual (8%, whole-hub move) is tracked separately.

  Kernel-checked, no `sorry`, axiom-clean `[propext, Classical.choice, Quot.sound]`.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace BGSCL

/-- F2 numerator sign: the leaf-path-extension `Aobj`-increment numerator `n² + n·Q + 4·Q` is ≥ 0 for
    `n, Q ≥ 0` (`n` a child count, `Q` a `qSum` term) — the nontrivial sign content of the increment. -/
theorem f2_numerator_nonneg (n Q : ℝ) (hn : 0 ≤ n) (hQ : 0 ≤ Q) :
    0 ≤ n ^ 2 + n * Q + 4 * Q := by positivity

/-- F2 leaf-path-extension `Aobj`-monotonicity certificate: the full increment
    `P · (n² + n·Q + 4·Q) / (2·(n+1)·(n+2))` is ≥ 0 for `P, Q, n ≥ 0` — the Case-A `Aobj t ≤ Aobj (f t)`
    clause of `RealObligationA` (92% of defective trees, per the taxonomy sweep). -/
theorem f2_aobj_increment_nonneg (P Q n : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hn : 0 ≤ n) :
    0 ≤ P * (n ^ 2 + n * Q + 4 * Q) / (2 * (n + 1) * (n + 2)) := by positivity

end BGSCL
end R3Cert
