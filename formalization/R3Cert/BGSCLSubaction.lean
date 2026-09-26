/-
  The additive SUBACTION bridge + first compact-core cell (2026-09-02).

  Companion to `BGSCLGStepBridge`.  It replaces the (REFUTED) multiplicative capped-product step by the
  ADDITIVE ergodic-optimization SUBACTION.  Since `bell b = Σ_v e_v` telescopes (`bell_node`), a subaction
  `ρ ≥ 0` satisfying the per-vertex inequality  `e_v + ρ(v) ≤ Σ_{child c} ρ(c)`  gives, by strong induction,
  `bell b ≤ −ρ(root) ≤ 0` — the branch ceiling.  Being a SUM (not a product), it structurally CANNOT incur the
  multiplicative overshoot that makes the capped-product step `Le1Step` FALSE
  (see `proof/docs/BG_LE1STEP_REFUTED_20260902.md`, `proof/docs/BG_CEILING_SUBACTION_20260902.md`).

  * `ceiling_of_subaction` — the bridge, sorry-free: `(ρ≥0 ∧ IsSubaction ρ) → ∀ b, bell b ≤ 0`.
  * `subaction_cell_broom_d4` — the FIRST compact-core cell of the empirically-verified affine-per-degree
    witness (`ρ(leaf)=F*`, `ρ(deg≥4)=0`) against the kernel: the degree-4 all-leaf (broom) corner, whose
    `(SUB)` content is `log(7/4) ≤ 4·F*`, discharged by log-monotonicity + `norm_num` on the rational
    `(7/4)^11 ≤ (621/64)^4`.  This is the message-endpoint corner (all children at the maximal message `y=1`).

  This is a WITNESS + a reduction, NOT a closed ceiling: the full per-cell certificate family over the
  compact deg-≤6 core (each an affine-in-μ endpoint check + a `log(1+S/d)` enclosure) and the high-degree tail
  lemma remain to be discharged.  No `sorry` here.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubactionEnc

namespace R3Cert
namespace BGSCL

open Real

/-- **The additive subaction inequality (SUB).**  A function `ρ : Branch → ℝ` is a *subaction* when, at every
    hub `node cs`, the local excess `e = log(1 + (Σ_c y_c)/d) − F*` (`d = |cs|+1`, `y_c = bY c`) plus the hub's
    own `ρ` is dominated by the children's `ρ`-sum.  For `cs = []` this specializes to `−F* + ρ(leaf) ≤ 0`,
    i.e. `ρ(leaf) ≤ F*`.  The `log(...) − FSTAR` term is exactly `bell_node`'s local excess, so summing `(SUB)`
    over a branch telescopes to `bell b ≤ −ρ(root)`. -/
def IsSubaction (ρ : Branch → ℝ) : Prop :=
  ∀ cs : List Branch,
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρ (Branch.node cs)
      ≤ (cs.map ρ).sum

/-- **The additive SUBACTION bridge.**  If `ρ ≥ 0` is a subaction, the whole branch ceiling `∀ b, bell b ≤ 0`
    holds.  Additive analog of `ceiling_of_gstep`: the per-vertex inequality is a SUM, so `Σ_v e_v = bell b`
    telescopes against `−ρ(root) ≤ 0` with no multiplicative overshoot.  Proof: `scl_of_child_step` strong
    induction with the invariant `bell b + ρ b ≤ 0`; the hub step is exactly `(SUB)` plus the child IH sum. -/
theorem ceiling_of_subaction (ρ : Branch → ℝ)
    (hSUB : IsSubaction ρ) (hρ : ∀ b, 0 ≤ ρ b) :
    ∀ b, bell b ≤ 0 := by
  -- `Σ_c (bell c + ρ c) = Σ_c bell c + Σ_c ρ c`
  have hsplit : ∀ l : List Branch,
      (l.map (fun c => bell c + ρ c)).sum = (l.map bell).sum + (l.map ρ).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  -- strengthened invariant `bell b + ρ b ≤ 0`
  have key : ∀ b, bell b + ρ b ≤ 0 := by
    refine scl_of_child_step bsize bchildren (fun b => bell b + ρ b ≤ 0) bchildren_bsize_lt ?_
    intro a hIH
    cases a with
    | node cs =>
        have hsum : (cs.map (fun c => bell c + ρ c)).sum ≤ 0 := by
          refine list_sum_nonpos ?_
          intro x hx; rw [List.mem_map] at hx; obtain ⟨c, hc, rfl⟩ := hx
          exact hIH c (by simpa [bchildren] using hc)
        rw [hsplit] at hsum
        have hsub := hSUB cs
        rw [bell_node]
        linarith
  intro b
  have h1 := key b
  have h2 := hρ b
  linarith

/-! ### First compact-core cell of the verified witness against the kernel. -/

/-- `bY(leaf) = 1` for the leaf `node []` (the maximal message). -/
theorem bY_leaf : bY (Branch.node []) = 1 := by
  simp [bY, bh, bcc, cav, cavAgg]

/-- The 3-leaf child list of the degree-4 broom vertex has message-sum `3` and length `3` — grounding the
    cell's `(SUB)` numerics (`log(1 + 3/4) = log(7/4)`, RHS `= 3·F*`). -/
theorem broom_d4_children_eval :
    (([Branch.node [], Branch.node [], Branch.node []] : List Branch).map bY).sum = 3
    ∧ ([Branch.node [], Branch.node [], Branch.node []] : List Branch).length = 3 := by
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bY_leaf]; norm_num
  · simp

/-- `log(7/4) ≤ 4·F*` — the analytic content of the degree-4 broom cell, via log-monotonicity reduced to the
    rational `(7/4)^11 ≤ (621/64)^4` (`norm_num`).  `F* = log(621/64)/11`. -/
theorem log74_le_4fstar : Real.log (7/4 : ℝ) ≤ 4 * FSTAR := by
  rw [FSTAR]
  have key : 11 * Real.log (7/4 : ℝ) ≤ 4 * Real.log (621/64 : ℝ) := by
    have e1 : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) = 11 * Real.log (7/4 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have e2 : Real.log ((621/64 : ℝ) ^ (4 : ℕ)) = 4 * Real.log (621/64 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have hle : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) ≤ Real.log ((621/64 : ℝ) ^ (4 : ℕ)) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [e1, e2] at hle; exact hle
  linarith

/-- **POC — the first compact-core cell of the witness against the kernel.**  The subaction inequality `(SUB)`
    at the degree-4 broom vertex (children = three leaves, all at the maximal message `y=1`), with the verified
    affine-per-degree witness `ρ(broom)=0`, `ρ(leaf)=F*`:  `(log(1 + 3/4) − F*) + 0 ≤ 3·F*`.  This is the
    all-children-maximal endpoint corner; the `log` is discharged exactly by `log74_le_4fstar`.  Kernel-checked,
    no `sorry`. -/
theorem subaction_cell_broom_d4 :
    (Real.log (1 + 3 / ((3 : ℝ) + 1)) - FSTAR) + (0 : ℝ) ≤ 3 * FSTAR := by
  have h74 : (1 + 3 / ((3 : ℝ) + 1)) = 7 / 4 := by norm_num
  rw [h74]
  have := log74_le_4fstar
  linarith

/-! ### The first TIGHT compact-core cell (deg-4 hub, deg-3 children) — tangent-endpoint + log-enclosure. -/

/-- The (rational, tie-free) degree-3 line of the verified witness, `ρ₃(μ) = (1/8)(μ − 1/5)`.  With
    `ρ(leaf)=F*`, `ρ(2,μ)=2F*−log(3/2)+(1/4)(μ−1/3)`, `ρ(3,·)=ρ₃`, `ρ(deg≥4)=0`, the subaction holds globally
    (checked on all branches `n≤14`); `ρ₃` is the piece the deg-4 tight cell exercises. -/
noncomputable def ρ3 (μ : ℝ) : ℝ := (1 / 8) * (μ - 1 / 5)

/-- **Log-enclosure** `log(5/4) − F* ≤ 1/20`, via `log x ≤ x − 1` at `x = (5/4)^11·(64/621) ≈ 1.20`
    (so `log x ≤ x−1 ≈ 0.20 ≤ 11/20`, all rational after clearing the `11·F* = log(621/64)`).  This is the
    analytic content the deg-4/deg-3 tight cell rests on (kin to the parallel session's
    `TranscendentalEnclosureEmitter`). -/
theorem log54_sub_fstar_le : Real.log (5 / 4 : ℝ) - FSTAR ≤ 1 / 20 := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (5 / 4 : ℝ) ^ (11 : ℕ) * (64 / 621) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((5 / 4 : ℝ) ^ (11 : ℕ) * (64 / 621))
      = 11 * Real.log (5 / 4) - Real.log (621 / 64) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64 / 621 : ℝ) = (621 / 64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5 / 4 : ℝ) ^ (11 : ℕ) * (64 / 621) - 1 ≤ 11 / 20 := by norm_num
  linarith

/-- **POC — the first TIGHT compact-core cell (degree-4 hub with three degree-3 children).**  The subaction
    inequality `(SUB)` at a degree-4 vertex (`ρ = 0`) whose three children are degree-3 with messages
    `y_i ∈ [1/5, 1/3]` (`ρ(3,·) = ρ₃`):  `(log(1 + (Σy)/4) − F*) + 0 ≤ Σ ρ₃(y_i)`.  This is the binding cell
    class (margin ≈ 0.033), far tighter than the broom corner.  The proof is the two tools the whole
    certificate family needs: the CONCAVE-LOG TANGENT at the aggregate endpoint `S = 1` (`log_tangent`, which
    collapses the 3-variable child-message box to the message endpoint — the analytic form of ①'s
    affine-endpoint / the `CurvatureBoundaryEmitter`), plus the LOG-ENCLOSURE `log(5/4) − F* ≤ 1/20`.
    Kernel-checked, no `sorry`. -/
theorem subaction_cell_d4_d3 (y1 y2 y3 : ℝ)
    (h1 : 1 / 5 ≤ y1) (h1' : y1 ≤ 1 / 3) (h2 : 1 / 5 ≤ y2) (h2' : y2 ≤ 1 / 3)
    (h3 : 1 / 5 ≤ y3) (h3' : y3 ≤ 1 / 3) :
    (Real.log (1 + (y1 + y2 + y3) / 4) - FSTAR) + 0 ≤ ρ3 y1 + ρ3 y2 + ρ3 y3 := by
  have hS0 : (0 : ℝ) ≤ y1 + y2 + y3 := by linarith
  have hS1 : y1 + y2 + y3 ≤ 1 := by linarith
  -- tangent of the concave `log(1 + S/4)` at the aggregate endpoint S = 1
  have htan := log_tangent (d := (4 : ℝ)) (s := y1 + y2 + y3) (s0 := (1 : ℝ))
    (by norm_num) hS0 (by norm_num)
  rw [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num, show (4 : ℝ) + 1 = 5 by norm_num] at htan
  have henc := log54_sub_fstar_le
  simp only [ρ3]
  linarith

/-! ### The validated explicit witness `ρwit`, and the single conditional theorem.

  NOTE: the exploratory `ρ3(μ)=(1/8)(μ−1/5)` above was found (2026-09-03) to belong to a witness that
  FAILS the high-degree-parent tail (a deg-D hub with deg-4 children at message → 1/4 has `e_node>0`,
  `RHS=0`); `subaction_cell_broom_d4`/`subaction_cell_d4_d3`/`log54_sub_fstar_le`/`log74_le_4fstar` remain
  TRUE isolated inequalities (and the log-enclosure tools), but are not cells of a globally-valid witness.
  The corrected, thoroughly-validated witness (enumerated n≤15 + tail to deg-140 + spider family + 120k
  mixed high-degree trees, margin 0 tight only at the `27·23` tie, `ρ≥0`) is `ρwit` below — clean rationals
  except the two tie anchors `F*`, `log(3/2)`; `e_tail = log(1+1/d)−F* > 0` only for `d=2,3,4`, so `ρ`
  vanishes for `d≥5`. -/

/-- Every message is `≤ 1` (`bY(node cs) = 1/((|cs|+1)+Σ bY) ≤ 1`). -/
theorem bY_le_one (b : Branch) : bY b ≤ 1 := by
  cases b with
  | node cs =>
    rw [bY_node]
    have hSnn : (0:ℝ) ≤ (cs.map bY).sum :=
      List.sum_nonneg (fun x hx => by
        rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
    have hcl : (0:ℝ) ≤ (cs.length : ℝ) := Nat.cast_nonneg _
    have hpos : (0:ℝ) < ((cs.length : ℝ) + 1) + (cs.map bY).sum := by linarith
    rw [div_le_one hpos]
    linarith

/-- A degree-2 branch (`node [c]`) has message `≥ 1/3` (since the single child's message is `≤ 1`). -/
theorem bY_deg2_ge_third (c : Branch) : (1:ℝ)/3 ≤ bY (Branch.node [c]) := by
  rw [bY_node]
  have hc := bY_le_one c
  have h0 := bY_nonneg c
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_one, add_zero, zero_add]
  apply one_div_le_one_div_of_le (by linarith)
  linarith

/-- `0 ≤ F*`. -/
theorem fstar_nonneg : 0 ≤ FSTAR :=
  by rw [FSTAR]; exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)

/-- The cherry/tie anchor is nonnegative: `2F* − log(3/2) ≥ 0` (via `(621/64)² ≥ (3/2)¹¹`, F*-folded). -/
theorem cherry_anchor_nonneg : 0 ≤ 2 * FSTAR - Real.log (3/2 : ℝ) := by
  rw [FSTAR]
  have h : 11 * Real.log (3/2 : ℝ) ≤ 2 * Real.log (621/64 : ℝ) := by
    have e1 : Real.log ((3/2 : ℝ) ^ (11:ℕ)) = 11 * Real.log (3/2) := by rw [Real.log_pow]; norm_num
    have e2 : Real.log ((621/64 : ℝ) ^ (2:ℕ)) = 2 * Real.log (621/64) := by rw [Real.log_pow]; norm_num
    have hle : Real.log ((3/2 : ℝ) ^ (11:ℕ)) ≤ Real.log ((621/64 : ℝ) ^ (2:ℕ)) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [e1, e2] at hle; exact hle
  linarith

/-- **The validated explicit witness** `ρwit : Branch → ℝ`, keyed by degree `= bcc + 1` and message `bY`:
    `ρ(leaf)=F*`, `ρ(2,μ)=2F*−log(3/2)+(1/4)(μ−1/3)`, `ρ(3,μ)=μ/32`, `ρ(4,μ)=μ/384`, `ρ(deg≥5)=0`. -/
noncomputable def ρwit (b : Branch) : ℝ :=
  match bcc b with
  | 0 => FSTAR
  | 1 => (2 * FSTAR - Real.log (3/2)) + (1/4) * (bY b - 1/3)
  | 2 => (1/32) * bY b
  | 3 => (1/384) * bY b
  | _ => 0

/-- `ρwit ≥ 0` everywhere (the nonnegativity the bridge requires). -/
theorem ρwit_nonneg (b : Branch) : 0 ≤ ρwit b := by
  cases b with
  | node cs =>
    rcases cs with _ | ⟨c, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
    · simp only [ρwit, bcc, List.length_nil]; exact fstar_nonneg
    · simp only [ρwit, bcc, List.length_cons, List.length_nil]
      have hb3 := bY_deg2_ge_third c
      have hch := cherry_anchor_nonneg
      nlinarith [hb3, hch]
    · simp only [ρwit, bcc, List.length_cons, List.length_nil]
      exact mul_nonneg (by norm_num) (bY_nonneg _)
    · simp only [ρwit, bcc, List.length_cons, List.length_nil]
      exact mul_nonneg (by norm_num) (bY_nonneg _)
    · simp [ρwit, bcc, List.length_cons]

/-- **The ceiling, reduced to a single explicit hypothesis.**  If the validated rational witness `ρwit`
    satisfies the per-vertex subaction inequality (`IsSubaction ρwit` — the finite per-cell family over the
    compact deg-≤4 core plus the `deg≥5 ⇒ ρ=0` tail), then the whole branch ceiling `∀ b, bell b ≤ 0` holds.
    The nonnegativity leg is discharged (`ρwit_nonneg`); `IsSubaction ρwit` is the one remaining obligation,
    now against a concrete, thoroughly-validated witness.  `conjecture1_proved = False`. -/
theorem ceiling_of_witness (hSUB : IsSubaction ρwit) : ∀ b, bell b ≤ 0 :=
  ceiling_of_subaction ρwit hSUB ρwit_nonneg

/-! ### First cells of `IsSubaction ρwit` (the remaining obligation).

  `IsSubaction ρwit` is `∀ cs, e_node + ρwit(node cs) ≤ Σ_c ρwit(c)`; discharging it is a finite per-node
  family: node degree `d = |cs|+1 ∈ {1,2,3,4}` (each with arbitrary child-degree mixes) plus the
  `d ≥ 5 ⇒ ρwit(node)=0` tail cells, every cell a tangent-endpoint reduction + an F*-folded log-enclosure
  (`curvature_boundary` + `log_combination`).  These two anchor cells are the base and the tie leg. -/

/-- `ρwit(leaf) = F*`. -/
theorem ρwit_leaf : ρwit (Branch.node []) = FSTAR := by simp [ρwit, bcc]

/-- **Cell: the leaf node** (`cs = []`, degree 1).  `(log 1 − F*) + F* = 0 ≤ 0` — the trivial base. -/
theorem subaction_nil :
    (Real.log (1 + (([] : List Branch).map bY).sum / (((([] : List Branch)).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node []) ≤ (([] : List Branch).map ρwit).sum := by
  simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_add, zero_div,
    add_zero, Real.log_one, ρwit_leaf]
  linarith

/-- **Cell: the cherry** (`cs = [leaf]`, degree 2 with one leaf child).  Here `bY(leaf)=1`, `bY(node)=1/3`,
    so `ρwit(node)=2F*−log(3/2)` and the inequality is `(log(3/2)−F*)+(2F*−log(3/2)) ≤ F*`, i.e. `F* ≤ F*`
    — the EXACT tie leg (equality), the `27·23` identity's degree-2 face. -/
theorem subaction_cherry :
    (Real.log (1 + (([Branch.node []]).map bY).sum
        / ((([Branch.node []] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [Branch.node []]) ≤ (([Branch.node []]).map ρwit).sum := by
  have hbYnode : bY (Branch.node [Branch.node []]) = 1/3 := by
    rw [bY_node]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, bY_leaf, Nat.cast_one, add_zero, zero_add]
    norm_num
  have hrnode : ρwit (Branch.node [Branch.node []]) = 2 * FSTAR - Real.log (3/2) := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil, hbYnode]; ring
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, bY_leaf, ρwit_leaf, hrnode, add_zero, Nat.cast_one, zero_add]
  rw [show (1:ℝ) + 1 / (1 + 1) = 3/2 by norm_num]
  linarith

/-- Message bound by degree: `bY b ≤ 1/(bcc b + 1) = 1/deg`. -/
theorem bY_le_inv_deg (b : Branch) : bY b ≤ 1 / ((bcc b : ℝ) + 1) := by
  cases b with
  | node cs =>
    rw [bY_node]
    simp only [bcc]
    have hSnn : (0:ℝ) ≤ (cs.map bY).sum := List.sum_nonneg (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
    have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
    exact one_div_le_one_div_of_le hd (by linarith)

/-- Log-enclosure for the deg-2 node with a deg≥5 child: `log(11/15) + F* + 1/24 ≤ 0`
    (via `log x ≤ x−1` at `x = (11/15)¹¹·(621/64) ≈ 0.32`, F*-folded). -/
theorem d2_deg5_enc : Real.log (11/15 : ℝ) + FSTAR + 1/24 ≤ 0 := by
  rw [FSTAR]
  have hr := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < (11/15 : ℝ) ^ (11:ℕ) * (621/64) by positivity)
  have hsplit : Real.log ((11/15 : ℝ) ^ (11:ℕ) * (621/64))
      = 11 * Real.log (11/15) + Real.log (621/64) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
  rw [hsplit] at hr
  have hnum : (11/15 : ℝ) ^ (11:ℕ) * (621/64) - 1 ≤ -11/24 := by norm_num
  linarith

/-- **Cell: degree-2 node with any deg≥5 child.**  Here the child's `ρwit = 0` and its message `≤ 1/5`, so
    the local excess is already `< 0`: `(log(1+bY c/2) − F*) + ρwit(node) ≤ log(11/10) − F* + [2F*−log(3/2)+1/24]
    = log(11/15) + F* + 1/24 ≤ 0`.  Covers infinitely many child degrees uniformly. -/
theorem subaction_deg2_deg5child (c : Branch) (hc : 4 ≤ bcc c) :
    (Real.log (1 + (([c]).map bY).sum / ((([c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c]) ≤ (([c]).map ρwit).sum := by
  have hy0 := bY_nonneg c
  have hy5 : bY c ≤ 1/5 := by
    have h1 := bY_le_inv_deg c
    have hcast : (4:ℝ) ≤ (bcc c : ℝ) := by exact_mod_cast hc
    have h2 : (1:ℝ) / ((bcc c : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hrc : ρwit c = 0 := by
    rw [ρwit]
    rcases hbc : bcc c with _ | _ | _ | _ | n
    · exact absurd hbc (by omega)
    · exact absurd hbc (by omega)
    · exact absurd hbc (by omega)
    · exact absurd hbc (by omega)
    · rfl
  have hrnode : ρwit (Branch.node [c]) ≤ 2 * FSTAR - Real.log (3/2) + 1/24 := by
    have hbn : bY (Branch.node [c]) ≤ 1/2 := by
      have h := bY_le_inv_deg (Branch.node [c])
      simp only [bcc, List.length_cons, List.length_nil] at h
      norm_num at h ⊢; linarith
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil]
    linarith
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, hrc, add_zero, zero_add, Nat.cast_one]
  have hlog : Real.log (1 + bY c / (1 + 1)) ≤ Real.log (11/10) := by
    apply Real.log_le_log (by positivity)
    have : bY c / (1 + 1) ≤ 1/10 := by linarith
    linarith
  have hld : Real.log (11/10 : ℝ) - Real.log (3/2) = Real.log (11/15) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have henc := d2_deg5_enc
  linarith [hlog, hrnode, henc, hld]

/-- Tighter enclosure `log(5/4) − F* ≤ 1/55` (via `log x ≤ x−1` at `x=(5/4)¹¹·(64/621) ≈ 1.1998`,
    so `x−1 ≈ 0.1998 ≤ 11/55`, F*-folded). -/
theorem log54_sub_fstar_le' : Real.log (5/4 : ℝ) - FSTAR ≤ 1/55 := by
  rw [FSTAR]
  have hr := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < (5/4 : ℝ) ^ (11:ℕ) * (64/621) by positivity)
  have hsplit : Real.log ((5/4 : ℝ) ^ (11:ℕ) * (64/621))
      = 11 * Real.log (5/4) - Real.log (621/64) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621 : ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5/4 : ℝ) ^ (11:ℕ) * (64/621) - 1 ≤ 11/55 := by norm_num
  linarith

/-- A degree-2 branch (`bcc = 1`) has message `≥ 1/3`. -/
theorem bY_ge_third_of_bcc1 (c : Branch) (hc : bcc c = 1) : (1:ℝ)/3 ≤ bY c := by
  cases c with
  | node cs =>
    simp only [bcc] at hc
    rcases cs with _ | ⟨c', _ | ⟨c2, t⟩⟩
    · simp at hc
    · exact bY_deg2_ge_third c'
    · simp only [List.length_cons, List.length_nil] at hc; omega

/-- **Cell: degree-2 node with a deg-2 child** (`bcc c = 1`, `bY c ∈ [1/3,1/2]`).  The delicate mid case:
    after cancelling the shared `2F*−log(3/2)−(1/4)(1/3)`, reduces to
    `log(1+y/2) − F* + (1/4)/(2+y) ≤ (1/4)y`, closed by the concave-log tangent at `y=1/2`, the convex
    secant bound `1/(2+y) ≤ 3/7 − (6/35)(y−1/3)`, and the tight enclosure `log(5/4)−F* ≤ 1/55`. -/
theorem subaction_deg2_deg2child (c : Branch) (hc : bcc c = 1) :
    (Real.log (1 + (([c]).map bY).sum / ((([c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c]) ≤ (([c]).map ρwit).sum := by
  have hy0 := bY_nonneg c
  have hy_lo : (1:ℝ)/3 ≤ bY c := bY_ge_third_of_bcc1 c hc
  have hy_hi : bY c ≤ 1/2 := by
    have h := bY_le_inv_deg c; rw [hc] at h; norm_num at h; linarith
  have hden : (0:ℝ) < 2 + bY c := by linarith
  have hrc : ρwit c = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c - 1/3) := by
    simp only [ρwit, hc]
  have hbYn : bY (Branch.node [c]) = 1 / (2 + bY c) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      Nat.cast_one, add_zero, zero_add]
    norm_num
  have hrn : ρwit (Branch.node [c])
      = 2 * FSTAR - Real.log (3/2) + (1/4) * (1 / (2 + bY c) - 1/3) := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil]; rw [hbYn]
  have htan : Real.log (1 + bY c / (1 + 1)) ≤ Real.log (5/4) + (2/5) * (bY c - 1/2) := by
    have h := log_tangent (d := (2:ℝ)) (s := bY c) (s0 := (1:ℝ)/2)
      (by norm_num) (by linarith) (by norm_num)
    rw [show (1:ℝ) + (1/2)/2 = 5/4 by norm_num, show (2:ℝ) + 1/2 = 5/2 by norm_num] at h
    rw [show (1:ℝ) + bY c / (1 + 1) = 1 + bY c / 2 by norm_num]
    calc Real.log (1 + bY c / 2) ≤ Real.log (5/4) + (bY c - 1/2) / (5/2) := h
      _ = Real.log (5/4) + (2/5) * (bY c - 1/2) := by ring
  have hsec : 1 / (2 + bY c) ≤ 3/7 - (6/35) * (bY c - 1/3) := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ bY c - 1/3 by linarith)
      (show (0:ℝ) ≤ 1/2 - bY c by linarith)]
  have henc := log54_sub_fstar_le'
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, hrc, hrn, add_zero]
  linarith [htan, hsec, henc, hy_lo, hy_hi]

/-- **Cell: degree-2 node with ANY deg≥3 child** — closes the whole degree-2 node.  For any child with
    `bcc c ≥ 2` (degree ≥ 3), the message `≤ 1/3`, so `log(1+bY c/2) ≤ log(7/6)` and
    `ρwit(node) ≤ 2F*−log(3/2)+1/24`, giving LHS `≤ log(7/6)−F*+[2F*−log(3/2)+1/24] = log(7/9)+F*+1/24 ≤ 0`
    (the tight-route enclosure `log79_add_fstar`, Telperion `emit_log_combination route='tight'`), which is
    `≤ 0 ≤ ρwit c`.  Subsumes `subaction_deg2_deg5child` and handles the deg-3/deg-4 children the degree-1
    tangent could not. -/
theorem subaction_deg2_highchild (c : Branch) (hc : 2 ≤ bcc c) :
    (Real.log (1 + (([c]).map bY).sum / ((([c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c]) ≤ (([c]).map ρwit).sum := by
  have hy0 := bY_nonneg c
  have hy3 : bY c ≤ 1/3 := by
    have h1 := bY_le_inv_deg c
    have hcast : (2:ℝ) ≤ (bcc c : ℝ) := by exact_mod_cast hc
    have h2 : (1:ℝ) / ((bcc c : ℝ) + 1) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hrnode : ρwit (Branch.node [c]) ≤ 2 * FSTAR - Real.log (3/2) + 1/24 := by
    have hbn : bY (Branch.node [c]) ≤ 1/2 := by
      have h := bY_le_inv_deg (Branch.node [c])
      simp only [bcc, List.length_cons, List.length_nil] at h
      norm_num at h ⊢; linarith
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil]
    linarith
  have hrc_nn : 0 ≤ ρwit c := ρwit_nonneg c
  have henc : Real.log (7/9 : ℝ) + FSTAR + 1/24 ≤ 0 := by have h := log79_add_fstar; linarith
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, add_zero, zero_add, Nat.cast_one]
  have hlog : Real.log (1 + bY c / (1 + 1)) ≤ Real.log (7/6) := by
    apply Real.log_le_log (by positivity)
    have : bY c / (1 + 1) ≤ 1/6 := by linarith
    linarith
  have hld : Real.log (7/6 : ℝ) - Real.log (3/2) = Real.log (7/9) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  linarith [hlog, hrnode, hrc_nn, hld, henc]

/-! ### First MULTI-child cell (node degree 3): the two-leaf broom. -/

/-- Log-enclosure for the degree-3 broom: `log(5/3) + 1/160 ≤ 3F*` (monotone/tangent route, comfortable
    margin: fold `(5/3)¹¹·(64/621)³ ≈ 0.555`, `x−1 ≈ −0.445 ≤ −11/160`). -/
theorem log53_enc : Real.log (5/3 : ℝ) + 1/160 ≤ 3 * FSTAR := by
  rw [FSTAR]
  have hr := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < (5/3 : ℝ) ^ (11:ℕ) * (64/621 : ℝ) ^ (3:ℕ) by positivity)
  have hsplit : Real.log ((5/3 : ℝ) ^ (11:ℕ) * (64/621 : ℝ) ^ (3:ℕ))
      = 11 * Real.log (5/3) - 3 * Real.log (621/64) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (64/621 : ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5/3 : ℝ) ^ (11:ℕ) * (64/621 : ℝ) ^ (3:ℕ) - 1 ≤ -11/160 := by norm_num
  linarith

/-- **Cell: the degree-3 broom** (`cs = [leaf, leaf]`).  Both children are leaves (`bY=1`, `ρwit=F*`), the
    node has `bY=1/5`, `ρwit(node)=1/160`; the inequality is `(log(5/3)−F*)+1/160 ≤ 2F*`, a fixed-point
    2-child enclosure (no decouple — messages are pinned).  Pins the two-child list mechanics. -/
theorem subaction_broom_d3 :
    (Real.log (1 + (([Branch.node [], Branch.node []]).map bY).sum
        / ((([Branch.node [], Branch.node []] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [Branch.node [], Branch.node []])
      ≤ (([Branch.node [], Branch.node []]).map ρwit).sum := by
  have hbY : bY (Branch.node [Branch.node [], Branch.node []]) = 1/5 := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, bY_leaf]
    norm_num
  have hrnode : ρwit (Branch.node [Branch.node [], Branch.node []]) = 1/160 := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil, hbY]; norm_num
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, bY_leaf, ρwit_leaf, hrnode]
  rw [show ((0 + 1 + 1 : ℕ) : ℝ) = 2 by norm_num,
      show (1:ℝ) + (1 + (1 + 0)) / (2 + 1) = 5/3 by norm_num]
  have := log53_enc
  linarith

end BGSCL
end R3Cert
