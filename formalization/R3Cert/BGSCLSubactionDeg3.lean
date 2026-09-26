/-
  The first genuine MULTI-CHILD SUBACTION cell with high-degree children (2026-09-03).

  Companion to `BGSCLSubaction`.  It discharges the first degree-3 SUBACTION cell whose BOTH children carry a
  free (non-pinned) message: a degree-3 hub (`node [c1, c2]`) whose two children are each degree ≥ 3
  (`bcc cᵢ ≥ 2`, so `bY cᵢ ∈ [0, 1/3]`).  Unlike the broom (`subaction_broom_d3`, both children leaves, messages
  pinned to 1) this cell requires the concave-log DECOUPLE across a free two-variable message box, collapsed to
  the aggregate endpoint `S = bY c1 + bY c2 = 2/3` by `log_tangent`, plus a per-child ρ-lower-bound that turns
  the linearized slope term `(3/11)(S − 2/3)` into `Σ_c ρwit c`.

  * `log119_sub_fstar` — the enclosure atom `log(11/9) − F* ≤ −1/200` (Telperion-generated).
  * `rhowit_ge_perchild` — per-child ρ lower bound: `(3/11)(bY c − 1/3) + 13/4800 ≤ ρwit c` for `bcc c ≥ 2`.
  * `subaction_deg3_highchildren` — the cell: `(log(1 + S/3) − F*) + ρwit(node [c1,c2]) ≤ Σ ρwit cᵢ`.

  Kernel-checked, no `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction

namespace R3Cert
namespace BGSCL

open Real

/-- **The enclosure atom** `log(11/9) − F* ≤ −1/200`, via `log x ≤ x − 1` at
    `x = (11/9)¹¹·(64/621) ≈ 0.945`, F*-folded (Telperion-generated). -/
theorem log119_sub_fstar : Real.log (11/9 : ℝ) - (FSTAR : ℝ) ≤ (-1/200 : ℝ) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (11/9 : ℝ) ^ (11 : ℕ) * (64/621) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((11/9 : ℝ) ^ (11 : ℕ) * (64/621))
      = 11 * Real.log (11/9 : ℝ) - Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621 : ℝ) = (621/64 : ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (11/9 : ℝ) ^ (11 : ℕ) * (64/621) - 1 ≤ -11/200 := by norm_num
  linarith

/-- **Per-child ρ-lower-bound.**  For any child `c` of degree ≥ 3 (`bcc c ≥ 2`, so `bY c ≤ 1/3`), the witness
    `ρwit c` dominates the affine slope line `(3/11)(bY c − 1/3) + 13/4800`.  This is what turns the decoupled
    slope term into `Σ_c ρwit c` in the cell.  Case split on degree 3 / 4 / ≥5:
    * deg-3 (`ρwit = bY/32`): worst at `bY = 1/3`, margin `+0.0077`.
    * deg-4 (`ρwit = bY/384 ≥ 0`): RHS `< 0` since `bY ≤ 1/4`.
    * deg≥5 (`ρwit = 0`): RHS `< 0` since `bY ≤ 1/5`. -/
theorem rhowit_ge_perchild (c : Branch) (hc : 2 ≤ bcc c) :
    (3/11) * (bY c - 1/3) + 13/4800 ≤ ρwit c := by
  have hy := bY_le_inv_deg c
  have hy0 := bY_nonneg c
  rcases (show bcc c = 2 ∨ bcc c = 3 ∨ 4 ≤ bcc c by omega) with h | h | h
  · -- deg-3: ρwit = (1/32) * bY c, bY c ≤ 1/3
    have hyle : bY c ≤ 1/3 := by rw [h] at hy; norm_num at hy; linarith
    simp only [ρwit, h]
    linarith
  · -- deg-4: ρwit = (1/384) * bY c ≥ 0, RHS < 0 (bY c ≤ 1/4)
    have hyle : bY c ≤ 1/4 := by rw [h] at hy; norm_num at hy; linarith
    simp only [ρwit, h]
    nlinarith [hy0]
  · -- deg≥5: ρwit = 0, RHS < 0 (bY c ≤ 1/5)
    have hyle : bY c ≤ 1/5 := by
      have hcast : (4:ℝ) ≤ (bcc c : ℝ) := by exact_mod_cast h
      have h2 : (1:ℝ) / ((bcc c : ℝ) + 1) ≤ 1/5 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hrc : ρwit c = 0 := by
      rw [ρwit]
      rcases hbc : bcc c with _ | _ | _ | _ | n
      · exact absurd hbc (by omega)
      · exact absurd hbc (by omega)
      · exact absurd hbc (by omega)
      · exact absurd hbc (by omega)
      · rfl
    rw [hrc]; linarith

/-- **The first genuine multi-child high-degree SUBACTION cell** (degree-3 hub, two degree-≥3 children).  The
    subaction inequality `(SUB)` at a degree-3 vertex (`node [c1, c2]`, `ρwit(node) = bY(node)/32`) whose two
    children each carry a free message `bY cᵢ ∈ [0, 1/3]`:  `(log(1 + S/3) − F*) + ρwit(node) ≤ ρwit c1 + ρwit c2`,
    `S = bY c1 + bY c2`.  Discharged by: (1) the concave-log DECOUPLE (`log_tangent`) collapsing the free
    two-variable message box to the aggregate endpoint `S = 2/3`, giving the slope line `log(11/9) + (3/11)(S−2/3)`;
    (2) the node-ρ bound `ρwit(node) = 1/(32(3+S)) ≤ 1/96`; (3) the enclosure `log(11/9) − F* ≤ −1/200`;
    (4) the two per-child ρ-lower-bounds `rhowit_ge_perchild`.  Tightest margin `+0.0077` at the all-deg-3
    corner `bY = 1/3`.  Kernel-checked, no `sorry`. -/
theorem subaction_deg3_highchildren (c1 c2 : Branch) (h1 : 2 ≤ bcc c1) (h2 : 2 ≤ bcc c2) :
    (Real.log (1 + (([c1, c2]).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2]).map ρwit).sum := by
  -- child message bounds
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy1 : bY c1 ≤ 1/3 := by
    have hy := bY_le_inv_deg c1
    have hcast : (2:ℝ) ≤ (bcc c1 : ℝ) := by exact_mod_cast h1
    have hle : (1:ℝ) / ((bcc c1 : ℝ) + 1) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy2 : bY c2 ≤ 1/3 := by
    have hy := bY_le_inv_deg c2
    have hcast : (2:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have hle : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSle : S ≤ 2/3 := by rw [hS]; linarith
  have hden : (0:ℝ) < 3 + S := by linarith
  -- (1) decouple: log(1 + S/3) ≤ log(11/9) + (S − 2/3)/(11/3) = log(11/9) + (3/11)(S − 2/3)
  have htan := log_tangent (d := (3:ℝ)) (s := S) (s0 := (2:ℝ)/3)
    (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (2/3)/3 = 11/9 by norm_num, show (3:ℝ) + 2/3 = 11/3 by norm_num] at htan
  -- (2) node-ρ bound: ρwit(node [c1,c2]) = (1/32) * bY(node) = 1/(32(3+S)) ≤ 1/96
  have hbYnode : bY (Branch.node [c1, c2]) = 1 / (3 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring_nf
  have hbcc_node : bcc (Branch.node [c1, c2]) = 2 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2]) = (1/32) * (1 / (3 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]
    norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2]) ≤ 1/96 := by
    rw [hrnode]
    have hinv : 1 / (3 + S) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hinv_nn : (0:ℝ) ≤ 1 / (3 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- (3) enclosure
  have henc := log119_sub_fstar
  -- (4) per-child lower bounds
  have hpc1 := rhowit_ge_perchild c1 h1
  have hpc2 := rhowit_ge_perchild c2 h2
  -- assemble: simplify the goal's log-arg and RHS
  have hlogarg : (1:ℝ) + (([c1, c2]).map bY).sum
      / ((([c1, c2] : List Branch).length : ℝ) + 1) = 1 + S / 3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; norm_num
  have hrhs : (([c1, c2]).map ρwit).sum = ρwit c1 + ρwit c2 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hlogarg, hrhs]
  -- htan : log(1 + S/3) ≤ log(11/9) + (S − 2/3)/(11/3)
  -- Combine: LHS ≤ [log(11/9) − F* + (3/11)(S−2/3)] + 1/96
  --        ≤ [−1/200 + (3/11)(S−2/3)] + 1/96
  --        = (3/11)((bY c1 − 1/3) + (bY c2 − 1/3)) + (1/96 − 1/200)
  -- with 1/96 − 1/200 = 13/2400 = 2·(13/4800), split equally between the two per-child bounds.
  have hslope : (S - 2/3)/(11/3) = (3/11) * (bY c1 - 1/3) + (3/11) * (bY c2 - 1/3) := by
    rw [hS]; ring
  linarith [htan, hrnode_le, henc, hpc1, hpc2, hslope]

end BGSCL
end R3Cert

-- #print axioms R3Cert.BGSCL.subaction_deg3_highchildren
