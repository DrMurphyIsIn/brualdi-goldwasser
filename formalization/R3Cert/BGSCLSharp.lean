/-
  The SHARP Brualdi–Goldwasser rate ceiling: the equality case, characterized (2026-09-24).

  `bg_ceiling : ∀ b, bell b ≤ 0` (`BGSCLSubactionDispatch`) is the weak ceiling.  This module pins its
  equality locus EXACTLY, in the literal BGSCL model:

      `bell b = 0 ↔ IsNearStarTie b`,   `IsNearStarTie b := b = node [cherryBranch ×5]`,

  i.e. the unique `bell = 0` branch is the 5-arm spider (arms of length 2) rooted at its hub.

  PROOF.
  (⟸) `bell_nearStarTie`: `bell cherry = log(3/2) − 2F*`, `Σ bY = 5/3`, so
      `bell = 5(log(3/2) − 2F*) + log(23/18) − F* = 0` by the `27·23 = 621` identity `tie_identity_d6`.
  (⟹) `bell b = 0` ⇒ `IsTie b` (`bell_eq_zero_imp_tie`) ⇒ `bcc b = 5` (`isTie_imp_bcc_eq_five`) and the
      root cell is TIGHT.  The `d = 6` root cell is `tail_decouple` at `S0 = 5/3` with the per-child bound
      `phi_lb_d6`; we show `phi_lb_d6` is STRICT at every child other than the cherry
      (`phi_lb_d6_strict_of_ne_cherry`):
        * leaf (`bY = 1`) and non-cherry deg-2 (`bY ≥ 2/5`): `bY > 1/3`, the existing strict slice;
        * deg-3 / deg-4 / deg≥5: via the STRICT anchor `2F* − log(3/2) < 1/96` (`cherry_anchor_lt`;
          `log x < x − 1` at `x = (621/64)²(2/3)¹¹ ≠ 1`).  At deg-3 the non-strict anchor is EXACTLY tight
          (`1/96 − 1/23 + 73/2208 = 0`), so the strict anchor is load-bearing.
      One non-cherry child therefore makes the root cell STRICT (`tail_decouple_strict_child`), contradicting
      tightness; so all five children are cherries.

  No `sorry`, no `native_decide`, no new axioms.  `conjecture1_proved = False` (this is the SHARP form of the
  classical-branch ceiling only, not conjecture1).
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionTail
import R3Cert.BGSCLSubactionTailDecouple
import R3Cert.BGSCLSubactionDispatch
import R3Cert.BGSCLSubactionStrict
import R3Cert.BGSCLHdom

namespace R3Cert
namespace BGSCL

open Real

/-! ### (⟸) The near-star tie attains the ceiling. -/

/-- `bell(leaf) = −F*`. -/
theorem bell_leaf : bell (Branch.node []) = -FSTAR := by
  rw [bell_node]; simp

/-- `bY(cherry) = 1/3`. -/
theorem bY_cherryBranch : bY cherryBranch = 1/3 := by
  rw [cherryBranch, bY_node]; simp [bY_leaf]; norm_num

/-- `bell(cherry) = log(3/2) − 2F*`. -/
theorem bell_cherryBranch : bell cherryBranch = Real.log (3/2) - 2 * FSTAR := by
  rw [cherryBranch, bell_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bell_leaf, bY_leaf,
    List.length_cons, List.length_nil]
  norm_num; ring

/-- **(T1) The near-star tie attains the ceiling:** `bell(node [cherry ×5]) = 0`, the exact
    `27·23 = 621` identity `log(23/18) + 5·log(3/2) = 11·F*`. -/
theorem bell_nearStarTie :
    bell (Branch.node [cherryBranch, cherryBranch, cherryBranch, cherryBranch, cherryBranch]) = 0 := by
  rw [bell_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bell_cherryBranch,
    bY_cherryBranch, List.length_cons, List.length_nil]
  have hid := tie_identity_d6
  norm_num
  linarith

/-! ### (⟹) Every non-cherry child makes the degree-6 root cell strict. -/

/-- **The STRICT cherry anchor** `2F* − log(3/2) < 1/96` (`log x < x − 1` at `x = (621/64)²·(2/3)¹¹ ≠ 1`). -/
theorem cherry_anchor_lt : 2 * FSTAR - Real.log (3/2) < 1/96 := by
  rw [FSTAR]
  have hr := Real.log_lt_sub_one_of_pos
    (show (0:ℝ) < (621/64 : ℝ) ^ (2:ℕ) * (2/3 : ℝ) ^ (11:ℕ) by positivity) (by norm_num)
  have hsplit : Real.log ((621/64 : ℝ) ^ (2:ℕ) * (2/3 : ℝ) ^ (11:ℕ))
      = 2 * Real.log (621/64) - 11 * Real.log (3/2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (2/3 : ℝ) = (3/2)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (621/64 : ℝ) ^ (2:ℕ) * (2/3 : ℝ) ^ (11:ℕ) - 1 ≤ 11/96 := by norm_num
  linarith

/-- A non-cherry deg-2 hub has message strictly above the cherry value: `node [c']` with `c' ≠ leaf`
    has `bY c' ≤ 1/2`, hence `bY(node [c']) = 1/(2 + bY c') ≥ 2/5 > 1/3`. -/
theorem bY_deg2_gt_third_of_ne_leaf (c' : Branch) (hc' : c' ≠ Branch.node []) :
    (1:ℝ)/3 < bY (Branch.node [c']) := by
  have hy0 := bY_nonneg c'
  have hyd := bY_le_inv_deg c'
  have hbcc : 1 ≤ bcc c' := by
    cases c' with
    | node l =>
      cases l with
      | nil => exact absurd rfl hc'
      | cons _ _ => simp [bcc]
  have hle : bY c' ≤ 1/2 := by
    have h2 : (2:ℝ) ≤ (bcc c' : ℝ) + 1 := by
      have : (1:ℝ) ≤ (bcc c' : ℝ) := by exact_mod_cast hbcc
      linarith
    have : (1:ℝ) / ((bcc c' : ℝ) + 1) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  rw [bY_node]
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [lt_div_iff₀ (by positivity)]
  push_cast
  linarith

/-- **`phi_lb_d6` is STRICT off the cherry.**  For every child `c ≠ cherryBranch`,
    `(2F* − log(3/2) − 1/23) + (3/23)·bY c < ρwit c`. -/
theorem phi_lb_d6_strict_of_ne_cherry (c : Branch) (hc : c ≠ cherryBranch) :
    (2 * FSTAR - Real.log (3/2) - 1/23) + (3/23) * bY c < ρwit c := by
  have hy0 := bY_nonneg c
  have hyd := bY_le_inv_deg c
  have hA := cherry_anchor_lt
  rcases hbc : bcc c with _ | _ | _ | _ | n
  · -- leaf: bY = 1 > 1/3
    have hby1 : bY c = 1 := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact bY_leaf
    exact phi_lb_d6_strict_of_bY_gt c (by rw [hby1]; norm_num)
  · -- deg-2, not the cherry: its single child is not a leaf, so bY > 1/3
    cases c with
    | node cs =>
      simp only [bcc] at hbc
      obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hbc
      have hc' : c' ≠ Branch.node [] := by
        rintro rfl; exact hc rfl
      exact phi_lb_d6_strict_of_bY_gt _ (bY_deg2_gt_third_of_ne_leaf c' hc')
  · -- deg-3: bY ≤ 1/3, ρwit = bY/32; tight under the weak anchor, strict under `cherry_anchor_lt`
    have hby : bY c ≤ 1/3 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/32) * bY c := by simp only [ρwit, hbc]
    rw [hrc]; linarith
  · -- deg-4: bY ≤ 1/4, ρwit = bY/384
    have hby : bY c ≤ 1/4 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/384) * bY c := by simp only [ρwit, hbc]
    rw [hrc]; linarith
  · -- deg≥5: bY ≤ 1/5, ρwit = 0
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hby : bY c ≤ 1/5 := by
      rw [hbc] at hyd
      have hd5 : (5:ℝ) ≤ ((n + 4 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hle : (1:ℝ) / (((n + 4 : ℕ) : ℝ) + 1) ≤ 1/5 :=
        one_div_le_one_div_of_le (by norm_num) hd5
      linarith
    have hrc : ρwit c = 0 := by
      cases c with
      | node cs => simp only [bcc] at hbc; exact ρwit_node_high (by omega)
    rw [hrc]; linarith

/-- **The `d = 6` STRICT cell for any non-all-cherry hub.**  If `|cs| = 5` and some child is not the cherry,
    the root cell is STRICT. -/
theorem strict_tail_d6_of_ne_cherry (cs : List Branch) (hlen : cs.length = 5)
    (a : Branch) (ha : a ∈ cs) (hne : a ≠ cherryBranch) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 5/3) = 3/23 := by rw [hlen]; norm_num
  refine tail_decouple_strict_child cs (5/3) (2 * FSTAR - Real.log (3/2) - 1/23) h4 (by norm_num)
    ?_ a ha ?_ ?_
  · intro c _; rw [hσ]; exact phi_lb_d6 c
  · rw [hσ]; exact phi_lb_d6_strict_of_ne_cherry a hne
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 5/3 / (5 + 1) = 23/18 by norm_num,
        show (5:ℝ)/3 / ((5 + 1) + 5/3) = 5/23 by norm_num]
    linarith [tie_identity_d6]

/-- **Ties are exactly the near-star tie.**  A tie (`4 ≤ bcc`, tight root cell) is `node [cherry ×5]`. -/
theorem isTie_imp_nearStarTie {b : Branch} (h : IsTie b) : IsNearStarTie b := by
  have h5 := isTie_imp_bcc_eq_five h
  obtain ⟨_, hns⟩ := h
  cases b with
  | node cs =>
    have hlen : cs.length = 5 := by simpa only [bcc] using h5
    have hall : ∀ a ∈ cs, a = cherryBranch := by
      intro a ha
      by_contra hne
      exact hns (strictRootCell_of_ineq cs (strict_tail_d6_of_ne_cherry cs hlen a ha hne))
    have hrep : cs = List.replicate 5 cherryBranch := by
      rw [← hlen]; exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    rw [IsNearStarTie, hrep]; rfl

/-- **(T2) The equality case of the BG ceiling.**  `bell b = 0` iff `b` is the near-star tie
    `node [cherry ×5]` (the 5-arm spider with arms of length 2, rooted at its hub). -/
theorem bell_eq_zero_iff (b : Branch) : bell b = 0 ↔ IsNearStarTie b := by
  constructor
  · intro h; exact isTie_imp_nearStarTie (bell_eq_zero_imp_tie h)
  · intro h; rw [h]; exact bell_nearStarTie

/-- **The method residue is exactly the equality locus.**  `IsTie b ↔ bell b = 0`.  This settles the reverse
    direction left open (and conjectured false) in the scope note of `BGSCLSubactionStrict`: a deg≥5 hub with
    a tight root cell is forced to be `node [cherry ×5]`, whose telescope is tight throughout. -/
theorem isTie_iff_bell_eq_zero (b : Branch) : IsTie b ↔ bell b = 0 :=
  ⟨fun h => (bell_eq_zero_iff b).mpr (isTie_imp_nearStarTie h), bell_eq_zero_imp_tie⟩

/-- **Strict off the tie.**  `bell b < 0` for every branch other than the near-star tie. -/
theorem bell_lt_zero_of_not_nearStarTie {b : Branch} (h : ¬ IsNearStarTie b) : bell b < 0 :=
  lt_of_le_of_ne (bg_ceiling b) (fun h0 => h ((bell_eq_zero_iff b).mp h0))

/-- **(T3) The SHARP Brualdi–Goldwasser rate ceiling.**  `bell b ≤ 0` for every planted branch, with
    equality exactly at the near-star tie `node [cherry ×5]`. -/
theorem bg_sharp : (∀ b : Branch, bell b ≤ 0) ∧ (∀ b : Branch, bell b = 0 ↔ IsNearStarTie b) := by
  exact ⟨bg_ceiling, bell_eq_zero_iff⟩

end BGSCL
end R3Cert
