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
import R3Cert.R47Capped

namespace R3Cert
namespace Step3

open RTree

/-! ### The dressed sums -/

/-- The dressed activity sum of an arm-load list: `Σ zw 1 j = Σ 3/(4j+3)`. -/
noncomputable def sigmaArms (arms : List ℕ) : ℝ := (arms.map fun j : ℕ => zw 1 j).sum

/-- The dressed cavity sum of a child block: `Σ (Zopen/Ztot)/udeg`. -/
noncomputable def qSum (ts : List UTree) : ℝ :=
  (ts.map fun K => Zopen (dtSub K) / Ztot (dtSub K) / (udeg K : ℝ)).sum

theorem sigmaArms_append (l1 l2 : List ℕ) :
    sigmaArms (l1 ++ l2) = sigmaArms l1 + sigmaArms l2 := by
  simp [sigmaArms]

theorem sigmaArms_replicate (n j : ℕ) :
    sigmaArms (List.replicate n j) = (n : ℝ) * zw 1 j := by
  simp [sigmaArms, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- Permutation invariance (the donor's arm order is immaterial). -/
theorem sigmaArms_perm {l1 l2 : List ℕ} (h : l1.Perm l2) :
    sigmaArms l1 = sigmaArms l2 := (h.map _).sum_eq

/-! ### Factoring the node degree out of the P2a sums -/

/-- The P2a arm wQ-sum is `(1/d) * sigmaArms`: each term `3/(d(4j+3))` factors. -/
theorem sum_div_factor (d : ℝ) (hd : d ≠ 0) (arms : List ℕ) :
    (arms.map fun j : ℕ => 3 / (d * (4 * (j : ℝ) + 3))).sum
      = 1 / d * sigmaArms arms := by
  induction arms with
  | nil => simp [sigmaArms]
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [sigmaArms, List.map_cons, List.sum_cons]
    have h43 : (4 * (a : ℝ) + 3) ≠ 0 := by positivity
    have h34 : (3 * 1 + 4 * (a : ℝ)) ≠ 0 := by positivity
    rw [zw]
    push_cast
    field_simp
    ring

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

/-- **The dressed hub-node partition function**: for a node of STRUCTURAL degree `dS`
    carrying load `c` (full realization degree `dS + c`), `arms`, and a further child
    block `ts`, the P2a form speaks the certified language:
    `Ztot = (blocks) * Fw dS c * (1 + zw dS c * (sigmaArms arms + qSum ts))`. -/
theorem Ztot_hubNode_dressed (dS c : ℕ) (arms : List ℕ) (ts : List UTree)
    (hd : 0 < dS) (hpos : ∀ K ∈ ts, 0 < Ztot (dtSub K)) :
    Ztot (RTree.node (dtChildren (dS + c)
        (arms.map armU ++ List.replicate c cherryU ++ ts)))
      = (((arms.map armU).map fun K => Ztot (dtSub K)).prod
          * (ts.map fun K => Ztot (dtSub K)).prod)
        * (Fw (dS : ℝ) c * (1 + zw (dS : ℝ) c * (sigmaArms arms + qSum ts))) := by
  have hD : 0 < dS + c := by omega
  have hDR : ((dS + c : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  rw [Ztot_hubNode (dS + c) hD arms c ts hpos,
    sum_div_factor (((dS + c : ℕ) : ℝ)) hDR arms, wQ_ts_factor (dS + c) ts]
  have hfold := fold_FZ dS c (sigmaArms arms + qSum ts) hd
  push_cast at hfold ⊢
  linear_combination
    (((arms.map armU).map fun K => Ztot (dtSub K)).prod
      * (ts.map fun K => Ztot (dtSub K)).prod) * hfold

end Step3
end R3Cert
