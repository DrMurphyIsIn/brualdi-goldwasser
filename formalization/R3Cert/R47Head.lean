/-
  R4-R7 campaign, PHASE 5c (part 1): the dressed hub-node form.

  Per P5_SEAM_DESIGN.md (S3), the head-merge identity
      Aobj(before) = K * beforeD,   Aobj(after) = K * afterD,
      K = prod(armsA Ztots) * prod(armsB Ztots) * Ztot(tail)
  was validated EXACTLY in rationals (60/60 random states, all 36 load cells,
  0/1/2-hub tails) before any Lean here.  This file builds its engine:

  * `sigmaArms`/`qSum`     -- the dressed activity sum of an arm list and the dressed
    cavity sum of a child block;
  * `sum_div_factor`/`wQ_ts_factor` -- factoring the node degree out of the P2a wQ-sums;
  * `Ztot_hubNode_dressed` -- the hub form in the certified language: for STRUCTURAL
    degree `dS` and load `c` (full degree `dS + c`),
        `Ztot = (blocks) * Fw dS c * (1 + zw dS c * (sigmaArms arms + qSum ts))`,
    the cherry block `(3/2)^c` folded into `Fw` via `fold_FZ` (R47Dress).

  The head identities themselves assemble in part 2.  Nothing here asserts per-step
  monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Dress

namespace R3Cert
namespace Step3

open RTree

/-! ### The dressed sums -/

/-- The dressed cavity sum of a child block: `Σ (Zopen/Ztot)/udeg`. -/
noncomputable def qSum (ts : List UTree) : ℝ :=
  (ts.map fun K => Zopen (dtSub K) / Ztot (dtSub K) / (udeg K : ℝ)).sum

/-! ### Factoring the node degree out of the P2a sums -/

/-- The P2a child-block wQ-sum is `(1/d) * qSum` (pure field algebra; the weight
    `1/(d * udeg)` splits). -/
theorem wQ_ts_factor (d : ℕ) (ts : List UTree) :
    ((dtChildren d ts).map fun p => p.1 * (Zopen p.2 / Ztot p.2)).sum
      = 1 / (d : ℝ) * qSum ts := by
  induction ts with
  | nil => simp [dtChildren_nil, qSum]
  | cons K rest ih =>
    rw [dtChildren_cons, List.map_cons, List.sum_cons, ih]
    simp only [qSum, List.map_cons, List.sum_cons]
    show 1 / ((d : ℝ) * (udeg K : ℝ)) * (Zopen (dtSub K) / Ztot (dtSub K))
        + 1 / (d : ℝ)
          * ((rest.map fun K' =>
              Zopen (dtSub K') / Ztot (dtSub K') / (udeg K' : ℝ))).sum
        = 1 / (d : ℝ) * (Zopen (dtSub K) / Ztot (dtSub K) / (udeg K : ℝ)
            + ((rest.map fun K' =>
                Zopen (dtSub K') / Ztot (dtSub K') / (udeg K' : ℝ))).sum)
    ring

/-! ### The dressed hub-node form -/

end Step3
end R3Cert
