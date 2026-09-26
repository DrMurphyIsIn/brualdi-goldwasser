/-
  The remaining degree-3 `IsSubaction ρwit` cells (2026-09-03).

  Completes the degree-3 hub family started in `BGSCLSubactionDeg3.lean`
  (`subaction_deg3_highchildren`) and `BGSCLSubaction.lean` (`subaction_broom_d3`).
  A degree-3 hub has two children; the profiles by child degree are:

    (leaf,leaf)      -> subaction_broom_d3            [BGSCLSubaction]
    (deg>=3,deg>=3)  -> subaction_deg3_highchildren   [BGSCLSubactionDeg3]
    (deg-2,deg-2)    -> subaction_deg3_deg2children   [HERE]
    (leaf,deg-2)     -> subaction_deg3_leaf_deg2      [HERE]
    (leaf,deg>=3)    -> subaction_deg3_leaf_high      [HERE]
    (deg-2,deg>=3)   -> subaction_deg3_deg2_high      [HERE]  (redesigned, see below)

  The three leaf/deg-2/deg-2 cells consume the Telperion atoms `deg3_deg2children_enc`
  (tight_hi), `log32_sub2fstar`, `log139_sub2fstar` (tangent) from `BGSCLSubactionEnc2`.

  CELL (D) REDESIGN.  The (deg-2, deg>=3) profile has a genuine two-slope obstruction:
  a single `log_tangent` cannot slope-match BOTH the deg-2 child's `ρwit` slope (1/4)
  and the deg>=3 child's per-child lower-bound slope (3/11); matching one overshoots the
  other (fails by ~0.0043 at the (bY_d2, bY_h) = (1/3, 0) corner).  The fix here dissolves
  it WITHOUT the two-slope decouple: since the high child's message is small (`bY_h <= 1/3`),
  bound it into a constant, drop its (nonneg) `ρwit`, and reduce to a single-variable
  inequality in the deg-2 child's message closed by the ONE new tight_hi atom
  `log2_sub3fstar : log(4/3) + log(3/2) - 3F* <= 71/960`.

  Kernel-checked, no `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionEnc2

namespace R3Cert
namespace BGSCL

open Real

/-! ### Cell: degree-3 hub, two degree-2 children (`bcc cᵢ = 1`, `bY cᵢ ∈ [1/3,1/2]`).

  Decouple at `s0 = 1` (slope `1/(3+1) = 1/4` = ρwit(deg-2) slope ⇒ the per-child terms are
  message-independent), node-ρ `≤ 3/352`, enclosure `deg3_deg2children_enc`.  Margin `+0.0091`. -/
theorem subaction_deg3_deg2children (c1 c2 : Branch) (h1 : bcc c1 = 1) (h2 : bcc c2 = 1) :
    (Real.log (1 + (([c1, c2]).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hS_lo : (2:ℝ)/3 ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 3 + S := by linarith
  have htan := log_tangent (d := (3:ℝ)) (s := S) (s0 := (1:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + 1/3 = 4/3 by norm_num, show (3:ℝ) + 1 = 4 by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2]) = 1 / (3 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring_nf
  have hbcc_node : bcc (Branch.node [c1, c2]) = 2 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2]) = (1/32) * (1 / (3 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2]) ≤ 3/352 := by
    rw [hrnode]
    have hinv : 1 / (3 + S) ≤ 3/11 := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < 11/3 by norm_num)
        (show (11:ℝ)/3 ≤ 3 + S by linarith)
      rwa [show (1:ℝ)/(11/3) = 3/11 by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (3 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := deg3_deg2children_enc
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hlogarg : (1:ℝ) + (([c1, c2]).map bY).sum
      / ((([c1, c2] : List Branch).length : ℝ) + 1) = 1 + S / 3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; norm_num
  have hrhs : (([c1, c2]).map ρwit).sum = ρwit c1 + ρwit c2 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hS]

/-! ### Cell: degree-3 hub, one leaf + one degree-2 child (`bcc c = 1`).

  The leaf's `ρwit = F*` dominates the RHS; reduce to `e_node + ρwit(node) ≤ F*` in the single
  variable `bY c ∈ [1/3,1/2]` (`S = 1 + bY c`).  Tangent at the endpoint `s0 = 3/2`, node-ρ folded
  into a quadratic (`div_le_iff₀` + `nlinarith`), enclosure `log32_sub2fstar`.  Margin `+0.0008`. -/
theorem subaction_deg3_leaf_deg2 (c : Branch) (hc : bcc c = 1) :
    (Real.log (1 + (([Branch.node [], c]).map bY).sum
        / ((([Branch.node [], c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [Branch.node [], c]) ≤ (([Branch.node [], c]).map ρwit).sum := by
  have hy0 := bY_nonneg c
  have hy_lo : (1:ℝ)/3 ≤ bY c := bY_ge_third_of_bcc1 c hc
  have hy_hi : bY c ≤ 1/2 := by
    have h := bY_le_inv_deg c; rw [hc] at h; norm_num at h; linarith
  have hden : (0:ℝ) < 4 + bY c := by linarith
  have htan : Real.log (1 + (1 + bY c)/3) ≤ Real.log (3/2) + (2/9) * (bY c - 1/2) := by
    have h := log_tangent (d := (3:ℝ)) (s := 1 + bY c) (s0 := (3:ℝ)/2)
      (by norm_num) (by linarith) (by norm_num)
    rw [show (1:ℝ) + (3/2)/3 = 3/2 by norm_num, show (3:ℝ) + 3/2 = 9/2 by norm_num] at h
    calc Real.log (1 + (1 + bY c)/3)
        ≤ Real.log (3/2) + ((1 + bY c) - 3/2)/(9/2) := h
      _ = Real.log (3/2) + (2/9) * (bY c - 1/2) := by ring
  have hquad : (1/32 : ℝ) * (1 / (4 + bY c)) ≤ 1/144 - (2/9) * (bY c - 1/2) := by
    rw [show (1/32 : ℝ) * (1 / (4 + bY c)) = (1/32)/(4 + bY c) by ring, div_le_iff₀ hden]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1/2 - bY c by linarith)
      (show (0:ℝ) ≤ bY c - 1/3 by linarith), hy_hi, hy_lo]
  have henc := log32_sub2fstar
  have hrc_nn : 0 ≤ ρwit c := ρwit_nonneg c
  have hbYnode : bY (Branch.node [Branch.node [], c]) = 1 / (4 + bY c) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, bY_leaf]
    push_cast; ring
  have hbcc_node : bcc (Branch.node [Branch.node [], c]) = 2 := by simp [bcc]
  have hrnode : ρwit (Branch.node [Branch.node [], c]) = (1/32) * (1 / (4 + bY c)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hlogarg : (1:ℝ) + (([Branch.node [], c]).map bY).sum
      / ((([Branch.node [], c] : List Branch).length : ℝ) + 1) = 1 + (1 + bY c)/3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, bY_leaf]
    norm_num
  have hrhs : (([Branch.node [], c]).map ρwit).sum = FSTAR + ρwit c := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ρwit_leaf, add_zero]
  rw [hlogarg, hrhs, hrnode]
  linarith [htan, henc, hquad, hrc_nn]

/-! ### Cell: degree-3 hub, one leaf + one degree-≥3 child (`bcc c ≥ 2`, `bY c ∈ [0,1/3]`).

  Same "leaf `ρwit = F*` dominates" reduction; endpoint tangent at `s0 = 4/3`, node-ρ folded into a
  quadratic, enclosure `log139_sub2fstar`.  Margin `+0.038`. -/
theorem subaction_deg3_leaf_high (c : Branch) (hc : 2 ≤ bcc c) :
    (Real.log (1 + (([Branch.node [], c]).map bY).sum
        / ((([Branch.node [], c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [Branch.node [], c]) ≤ (([Branch.node [], c]).map ρwit).sum := by
  have hy0 := bY_nonneg c
  have hy3 : bY c ≤ 1/3 := by
    have h1 := bY_le_inv_deg c
    have hcast : (2:ℝ) ≤ (bcc c : ℝ) := by exact_mod_cast hc
    have h2 : (1:ℝ) / ((bcc c : ℝ) + 1) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hden : (0:ℝ) < 4 + bY c := by linarith
  have htan : Real.log (1 + (1 + bY c)/3) ≤ Real.log (13/9) + (3/13) * (bY c - 1/3) := by
    have h := log_tangent (d := (3:ℝ)) (s := 1 + bY c) (s0 := (4:ℝ)/3)
      (by norm_num) (by linarith) (by norm_num)
    rw [show (1:ℝ) + (4/3)/3 = 13/9 by norm_num, show (3:ℝ) + 4/3 = 13/3 by norm_num] at h
    calc Real.log (1 + (1 + bY c)/3)
        ≤ Real.log (13/9) + ((1 + bY c) - 4/3)/(13/3) := h
      _ = Real.log (13/9) + (3/13) * (bY c - 1/3) := by ring
  have hquad : (1/32 : ℝ) * (1 / (4 + bY c)) ≤ 3/416 - (3/13) * (bY c - 1/3) := by
    rw [show (1/32 : ℝ) * (1 / (4 + bY c)) = (1/32)/(4 + bY c) by ring, div_le_iff₀ hden]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1/3 - bY c by linarith) hy0, hy3, hy0]
  have henc := log139_sub2fstar
  have hrc_nn : 0 ≤ ρwit c := ρwit_nonneg c
  have hbYnode : bY (Branch.node [Branch.node [], c]) = 1 / (4 + bY c) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, bY_leaf]
    push_cast; ring
  have hbcc_node : bcc (Branch.node [Branch.node [], c]) = 2 := by simp [bcc]
  have hrnode : ρwit (Branch.node [Branch.node [], c]) = (1/32) * (1 / (4 + bY c)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hlogarg : (1:ℝ) + (([Branch.node [], c]).map bY).sum
      / ((([Branch.node [], c] : List Branch).length : ℝ) + 1) = 1 + (1 + bY c)/3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, bY_leaf]
    norm_num
  have hrhs : (([Branch.node [], c]).map ρwit).sum = FSTAR + ρwit c := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ρwit_leaf, add_zero]
  rw [hlogarg, hrhs, hrnode]
  linarith [htan, henc, hquad, hrc_nn]

/-! ### Cell (D) atom: `log(4/3) + log(3/2) - 3F* ≤ 71/960`  (tight_hi route, dogfooded).

  Fold `X = (4/3)¹¹·(3/2)¹¹·(621/64)⁻³ = 2⁻¹¹-free = 536870912/239483061 ≈ 2.2418 > 1`, `Q = 781/960 > 0`.
  The existing `tight` route needs `Q<0`; the degree-1 tangent needs `X−1 ≤ Q` (fails, `1.24 > 0.81`).
  tight_hi: `log X ≤ Q ⟺ X ≤ exp Q`, with a **degree-5** Taylor lower bound on `exp Q` (`Real.exp_bound`,
  n=4 is too weak here since `X` sits closer to `exp Q`): `exp Q ≥ 61122928451812033/27179089920000000 ≥ X`. -/
theorem log2_sub3fstar :
    Real.log (4/3 : ℝ) + Real.log (3/2 : ℝ) - (3 * FSTAR : ℝ) ≤ (71/960 : ℝ) := by
  rw [FSTAR]
  have hXpos : (0 : ℝ) < (4/3 : ℝ) ^ (11 : ℕ) * (3/2 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (3 : ℕ))⁻¹) := by
    positivity
  have hsplit : Real.log ((4/3 : ℝ) ^ (11 : ℕ) * (3/2 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (3 : ℕ))⁻¹))
      = 11 * Real.log (4/3 : ℝ) + 11 * Real.log (3/2 : ℝ) - 3 * Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hx : |(781/960 : ℝ)| ≤ 1 := by rw [abs_of_nonneg (by norm_num)]; norm_num
  have hb := Real.exp_bound hx (n := 5) (by norm_num)
  have hexpge : (61122928451812033/27179089920000000 : ℝ) ≤ Real.exp (781/960 : ℝ) := by
    have hlo := (abs_le.mp hb).1
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg] at hlo
    linarith
  have hXexp : (4/3 : ℝ) ^ (11 : ℕ) * (3/2 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (3 : ℕ))⁻¹)
      ≤ Real.exp (781/960 : ℝ) := by
    have hXle : (4/3 : ℝ) ^ (11 : ℕ) * (3/2 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (3 : ℕ))⁻¹)
        ≤ (61122928451812033/27179089920000000 : ℝ) := by norm_num
    linarith
  have hlogX : Real.log ((4/3 : ℝ) ^ (11 : ℕ) * (3/2 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (3 : ℕ))⁻¹))
      ≤ (781/960 : ℝ) := by
    rw [Real.log_le_iff_le_exp hXpos]; exact hXexp
  rw [hsplit] at hlogX
  linarith

/-! ### Cell (D): degree-3 hub, one degree-2 + one degree-≥3 child  (the redesigned two-slope cell).

  `c1` deg-2 (`bcc c1 = 1`), `c2` deg-≥3 (`bcc c2 ≥ 2`, `bY c2 ≤ 1/3`).  NO two-slope decouple: bound
  `bY c2 ≤ 1/3` into a constant, DROP `ρwit c2 ≥ 0`, tangent at `s0 = 1` (slope-match the deg-2 child),
  node-ρ `≤ 3/320`, and the single atom `log2_sub3fstar`.  Worst corner `(bY_d2,bY_h)=(1/3,1/3)`,
  atom margin `+0.0006`. -/
theorem subaction_deg3_deg2_high (c1 c2 : Branch) (h1 : bcc c1 = 1) (h2 : 2 ≤ bcc c2) :
    (Real.log (1 + (([c1, c2]).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy2_hi : bY c2 ≤ 1/3 := by
    have h1' := bY_le_inv_deg c2
    have hcast : (2:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have h3 : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hS_lo : (1:ℝ)/3 ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 3 + S := by linarith
  have htan := log_tangent (d := (3:ℝ)) (s := S) (s0 := (1:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + 1/3 = 4/3 by norm_num, show (3:ℝ) + 1 = 4 by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2]) = 1 / (3 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring_nf
  have hbcc_node : bcc (Branch.node [c1, c2]) = 2 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2]) = (1/32) * (1 / (3 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2]) ≤ 3/320 := by
    rw [hrnode]
    have hinv : 1 / (3 + S) ≤ 3/10 := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < 10/3 by norm_num)
        (show (10:ℝ)/3 ≤ 3 + S by linarith)
      rwa [show (1:ℝ)/(10/3) = 3/10 by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (3 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := log2_sub3fstar
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2_nn : 0 ≤ ρwit c2 := ρwit_nonneg c2
  have hlogarg : (1:ℝ) + (([c1, c2]).map bY).sum
      / ((([c1, c2] : List Branch).length : ℝ) + 1) = 1 + S / 3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; norm_num
  have hrhs : (([c1, c2]).map ρwit).sum = ρwit c1 + ρwit c2 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hlogarg, hrhs, hrc1]
  linarith [htan, hrnode_le, henc, hrc2_nn, hy2_hi, hS]

end BGSCL
end R3Cert
