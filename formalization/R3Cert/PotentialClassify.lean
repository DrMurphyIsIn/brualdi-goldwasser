/-
  General-case infrastructure, piece 2: positive-part superadditivity and the cavity structural lemmas.

  The list-level Jensen reduction for `Plin y = (11/50)·(y − T0)₊` needs ONLY the superadditivity of the
  positive part, `(x + y)₊ ≤ x₊ + y₊` (since `m · Plin(mean) = (11/50)·(Σyᵢ − m·T0)₊`) — no convexity
  machinery.  The cavity lemmas locate every plain child on the `Pval` menu: a non-leaf has `cav < 1/2`
  (hence `≠ 1`), two-or-more children give `cav < 1/3`, and a single NON-LEAF child gives `cav > 1/3` —
  so a generic (non-arm, non-leaf) plain child never hits the special points `{1/3, 1}` and its `Pval`
  is the linear fold.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar
import R3Cert.PlainFormula
import R3Cert.Potential
import R3Cert.PotentialAux

namespace R3Cert

open Real

/-- **Positive-part superadditivity:** `(x + y)₊ ≤ x₊ + y₊`. -/
theorem posPart_add_le (x y : ℝ) : max 0 (x + y) ≤ max 0 x + max 0 y := by
  have hx : x ≤ max 0 x := le_max_right 0 x
  have hy : y ≤ max 0 y := le_max_right 0 y
  have hx0 : (0 : ℝ) ≤ max 0 x := le_max_left 0 x
  have hy0 : (0 : ℝ) ≤ max 0 y := le_max_left 0 y
  rcases le_total (x + y) 0 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

/-- **A non-leaf branch has cavity `< 1/2`** (`cav = 3/(3+3k+4c+3S)` with `k ≥ 1`, `S > 0`). -/
theorem cav_cons_lt_half (c : ℕ) (x : Branch) (rest : List Branch) :
    cav (Branch.node c (x :: rest)) < 1 / 2 := by
  have hS : 0 < cavSum (x :: rest) := cavSum_pos _ (List.cons_ne_nil x rest)
  have hk : (1 : ℝ) ≤ ((x :: rest).length : ℝ) := by
    rw [List.length_cons]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) rest.length]
  have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  rw [cav_eq, div_lt_iff₀ (by linarith)]
  linarith

/-- A non-leaf branch has cavity `< 1` (corollary). -/
theorem cav_cons_lt_one (c : ℕ) (x : Branch) (rest : List Branch) :
    cav (Branch.node c (x :: rest)) < 1 := by
  linarith [cav_cons_lt_half c x rest]

/-- **Two or more children give cavity `< 1/3`.** -/
theorem cav_two_lt_third (c : ℕ) (x y : Branch) (rest : List Branch) :
    cav (Branch.node c (x :: y :: rest)) < 1 / 3 := by
  have hS : 0 < cavSum (x :: y :: rest) := cavSum_pos _ (List.cons_ne_nil x (y :: rest))
  have hk : (2 : ℝ) ≤ ((x :: y :: rest).length : ℝ) := by
    rw [List.length_cons, List.length_cons]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) rest.length]
  have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  rw [cav_eq, div_lt_iff₀ (by linarith)]
  linarith

/-- **A single NON-LEAF child (plain node) gives cavity `> 1/3`** (`cav = 3/(6 + 3·cav x)` with
    `cav x < 1/2 < 1`). -/
theorem cav_one_generic_gt_third (c' : ℕ) (z : Branch) (r : List Branch) :
    1 / 3 < cav (Branch.node 0 [Branch.node c' (z :: r)]) := by
  set x := Branch.node c' (z :: r) with hx
  have hxh : cav x < 1 / 2 := cav_cons_lt_half c' z r
  have hxp : 0 < cav x := cav_pos x
  have hcs : cavSum [x] = cav x := by simp [cavSum]
  rw [cav_eq, hcs]
  have hden : (0 : ℝ) < 3 + 3 * (([x] : List Branch).length : ℝ) + 4 * ((0 : ℕ) : ℝ) + 3 * cav x := by
    simp only [List.length_cons, List.length_nil]; push_cast; linarith
  rw [lt_div_iff₀ hden]
  simp only [List.length_cons, List.length_nil]; push_cast
  linarith

end R3Cert
