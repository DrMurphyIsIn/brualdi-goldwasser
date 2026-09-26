/-
  BG asymptotic upper bound — the SCL price-flow layer (2026-09-02).

  Builds on `R3Cert.BGSCLInduction` (the concrete cavity `total`/`ell`/`V_μ`, the ell recursion `bell_node`,
  the concave tangent `bell_node_tangent`, the hub `y`-formula `bY_node`, and the reduction `scl_of_step`).
  The remaining obligation `SCLStep` is the per-hub decouple, which flows the price `μ ↦ μ'' =
  3(4d−1−3μ)/(4d−1)²` (telperion's `ExtremalityPriceMap`, gated leg #1) and needs the induction to carry the
  SCL for ALL prices in the invariant interval `I = [456/3703, 3/7]`.

  What is PROVED here (verified by local `lake build`, no `sorry`):
    * `inI`, `muPP` — the invariant price interval and the concavity-tangent price map.
    * `muPP_mem_I` — **the price map keeps `I` invariant for hub-degrees `2 ≤ d ≤ 6`** (leg #1), by a pure
      rational box inequality.  (For `d ≥ 7` the hub is high-degree, handled by the ceiling, not this decouple.)
    * `PSCL`, `scl_of_step'` — the price-carrying predicate `∀ μ ∈ I, V_μ(b) ≤ V_μ(cherry)` and the well-founded
      recursion driving it (reusing `scl_of_child_step`), reducing the SCL to a per-hub step whose child IH is
      available at EVERY price in `I` — so it can be instantiated at the flowed price `μ'' ∈ I`.

  LEAF-EXCLUSION (the crux, RESOLVED — no `sorry`):
    * `leaf_le_cherry` — a leaf child satisfies `V_μ(leaf) ≤ V_μ(cherry)` for `μ ≤ 3/11`.
    * `muPP_le_three_eleven` — the child price `μ'' = muPP d μ ≤ 3/11` for hub-degrees `d ≥ 3`.
    Together: leaves violate the SCL only for `μ > 0.297`, but in the induction step (size `> 11`) they occur
    only at `d ≥ 3` where the child price is `≤ 3/11 < 0.297` — so `V_{μ''}(leaf) ≤ V_{μ''}(cherry)` HOLDS.  The
    sole `d = 2` leaf-hub is the cherry itself (size 2, a base case).  So the naive-false `∀b` SCL is repaired.
  LOG-ENCLOSURE TECHNIQUE (`hbroom` keystone, no `sorry`):
    * `two_le_log_gap` — `2 ≤ 11 log(3/2) − log(621/64)` via `Real.exp_one_lt_d9` (LOOSER rational bounds, NOT
      the tight frozen `10^30` enclosures) — the reusable method for the broom-vs-cherry leg #4.

  REMAINING (see plan `sorted-conjuring-clock`): the full `hbroom` (leg #4 for all broom degrees, the tighter
  +0.012 margin via the same `exp`-bound method) and the per-hub decouple assembly (tangent at the all-cherry
  reference + child IH at `μ''` + `residual ≤ margin` nlinarith).  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction

namespace R3Cert
namespace BGSCL

/-- The invariant price interval `I = [456/3703, 3/7]` (the largest window containing all hub prices
    `μ_d = 3/(4d−1)` and clear of the tie's low-price inversion `μ ≈ 0.038`). -/
def inI (μ : ℝ) : Prop := (456 : ℝ) / 3703 ≤ μ ∧ μ ≤ 3 / 7

/-- The concavity-tangent price map: a degree-`d` hub at price `μ` flows its children to price
    `μ'' = 3(4d−1−3μ)/(4d−1)²` (`= ν(S*)`, the tangent slope at the all-cherry reference). -/
noncomputable def muPP (d μ : ℝ) : ℝ := 3 * (4 * d - 1 - 3 * μ) / (4 * d - 1) ^ 2

/-- **Price-map invariance (leg #1).**  For hub-degrees `2 ≤ d ≤ 6`, the map `μ ↦ μ''` keeps `I` invariant:
    `μ ∈ I ⇒ μ'' ∈ I`.  Pure rational box inequality (`nlinarith`).  (`A = 456/3703` is the fixed point of the
    tightest `d = 6` map; degrees `≥ 7` are high-degree hubs handled by the ceiling, not this decouple.) -/
theorem muPP_mem_I {d μ : ℝ} (hd : 2 ≤ d) (hd6 : d ≤ 6) (h : inI μ) : inI (muPP d μ) := by
  obtain ⟨hlo, hhi⟩ := h
  have hpos : (0:ℝ) < (4 * d - 1) ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [muPP, le_div_iff₀ hpos]
    nlinarith [sq_nonneg (d - 2), sq_nonneg (d - 6),
      mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hd6)]
  · rw [muPP, div_le_iff₀ hpos]
    nlinarith [sq_nonneg (d - 2)]

/-- The price-carrying SCL predicate: `V_μ(b) ≤ V_μ(cherry)` for EVERY price `μ ∈ I`.  Carrying `∀ μ ∈ I` is
    what lets the induction instantiate the child IH at the flowed price `μ'' ∈ I` (`muPP_mem_I`). -/
def PSCL (b : Branch) : Prop := ∀ μ, inI μ → bV μ b ≤ bV μ cherry

/-- **The SCL from the per-hub step, price-flow version.**  Given the per-hub step (every hub whose children
    all satisfy `PSCL` satisfies `PSCL`), the price-carrying SCL holds for EVERY branch, by the well-founded
    recursion on `|b|`.  Reduces the SCL to the per-hub decouple with the child IH available at all `μ ∈ I`. -/
theorem scl_of_step' (hstep : ∀ cs : List Branch, (∀ c ∈ cs, PSCL c) → PSCL (Branch.node cs)) :
    ∀ b, PSCL b := by
  refine scl_of_child_step bsize bchildren PSCL bchildren_bsize_lt (fun a hIH => ?_)
  cases a with
  | node cs => exact hstep cs (fun c hc => hIH c (by simpa only [bchildren] using hc))

/-! ### (2) Leaf-exclusion — the crux, resolved.

A bare leaf `node []` VIOLATES the SCL for `μ > 0.297` (so `∀b, ∀μ∈I, V_μ b ≤ V_μ cherry` is false).  Resolution:
the child price `μ'' = muPP d μ` is `< 0.273 < 0.297` for ALL hub-degrees `d ≥ 3`, and a degree-2 hub with a
leaf child is exactly the cherry (size 2, a base case).  So in the induction step (size `> 11`), leaf children
occur only at `d ≥ 3`, where `V_{μ''}(leaf) ≤ V_{μ''}(cherry)` HOLDS.  The concrete facts: -/

/-- `y(leaf) = 1`. -/
theorem bY_leaf : bY (Branch.node []) = 1 := by rw [bY_node]; simp
/-- `ell(leaf) = −F*`. -/
theorem bell_leaf : bell (Branch.node []) = -FSTAR := by rw [bell_node]; simp
/-- `y(cherry) = 1/3`. -/
theorem bY_cherry : bY cherry = 1 / 3 := by
  rw [cherry, bY_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, bY_leaf]
  norm_num
/-- `ell(cherry) = log(3/2) − 2 F*`. -/
theorem bell_cherry : bell cherry = Real.log (3 / 2) - 2 * FSTAR := by
  rw [cherry, bell_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, bell_leaf, bY_leaf]
  norm_num
  ring

/-- The pivotal log inequality (margin `≈ 0.19`, proved via `Real.exp_one_lt_d9`, NOT the tight frozen
    enclosures): `2 ≤ 11·log(3/2) − log(621/64)`, i.e. `exp 2 ≤ 6561/736`. -/
theorem two_le_log_gap : (2:ℝ) ≤ 11 * Real.log (3 / 2) - Real.log (621 / 64) := by
  have hpow : 11 * Real.log (3 / 2) = Real.log ((3 / 2) ^ 11) := by rw [Real.log_pow]; ring
  have hcomb : 11 * Real.log (3 / 2) - Real.log (621 / 64) = Real.log (6561 / 736) := by
    rw [hpow, ← Real.log_div (by positivity) (by norm_num)]; norm_num
  rw [hcomb, Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [h2, Real.exp_pos 1, h1]

/-- **Leaf-exclusion (the crux, discharged).**  For every price `μ ≤ 3/11` — which covers every child price
    `μ'' = muPP d μ` at hub-degrees `d ≥ 3` (`muPP d μ ≤ 3/(4d−1) ≤ 3/11`) — a leaf child satisfies the SCL:
    `V_μ(leaf) ≤ V_μ(cherry)`.  So leaf children never break the decouple in the induction step (where they only
    occur at `d ≥ 3`); the sole `d = 2` leaf-hub is the cherry itself, a base case. -/
theorem leaf_le_cherry {μ : ℝ} (hμ : μ ≤ 3 / 11) : bV μ (Branch.node []) ≤ bV μ cherry := by
  rw [bV, bV, bell_leaf, bY_leaf, bell_cherry, bY_cherry]
  have h := two_le_log_gap
  have hF : FSTAR = Real.log (621 / 64) / 11 := rfl
  rw [hF]
  nlinarith [h, hμ]

/-- The child price `μ'' = muPP d μ` is `≤ 3/11` for hub-degrees `d ≥ 3`, `μ ≥ 0` — so `leaf_le_cherry`
    applies to leaf children in every `d ≥ 3` decouple. -/
theorem muPP_le_three_eleven {d μ : ℝ} (hd : 3 ≤ d) (hμ : 0 ≤ μ) : muPP d μ ≤ 3 / 11 := by
  have hpos : (0:ℝ) < (4 * d - 1) ^ 2 := by nlinarith
  rw [muPP, div_le_iff₀ hpos]
  nlinarith [hd, hμ, sq_nonneg (d - 3)]

end BGSCL
end R3Cert
