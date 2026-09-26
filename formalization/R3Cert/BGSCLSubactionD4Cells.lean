/-
  The 35 degree-4 hub `IsSubaction ρwit` node cells (2026-09-03).

  A degree-4 hub has 3 children; `ρwit(node) = bY(node)/384 = 1/(384·(4+S))`, `S = Σ bY(childᵢ)`.  Every one
  of the 35 child-degree profiles (multisets from {leaf, 2, 3, 4, ≥5}) closes with a SINGLE `log_tangent` at
  its binding corner (no two-slope "drop-the-high-child" needed at d=4, unlike deg-3 cell (D)), reducing to
  the single-log enclosure ATOM `d4_*` already proven in `BGSCLSubactionD4.lean`.  This file is the mechanical
  "wiring": per-child message bound + node-ρ bound + tangent + atom + `linarith`, mirroring the degree-3 cells
  in `BGSCLSubactionDeg3Mid.lean`.  The `log(3/2)` and `F*` opaque terms cancel exactly between each atom's
  `(kL, kF)` folds and the per-child `ρwit` sum, so `linarith` closes each cell over the whole message box.

  Naming: `subaction_deg4_<XYZ>`, `X ≤ Y ≤ Z` the child classes in ascending bcc order
  (L = leaf/bcc0, 2 = bcc1, 3 = bcc2, 4 = bcc3, H = deg≥5/bcc≥4).  The atom `d4_*` for the same multiset uses
  the D4.lean convention (digits ascending, leaf last).  Kernel-checked, no `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionD4

namespace R3Cert
namespace BGSCL

open Real

/-- Cell `LLL` (uses `d4_LLL`). -/
theorem subaction_deg4_LLL (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 0) (h3 : bcc c3 = 0) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2e : bY c2 = 1 := by
    have hc2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hc2, bY_leaf]
  have hy3e : bY c3 = 1 := by
    have hc3 : c3 = Branch.node [] := by
      cases c3 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h3; omega
    rw [hc3, bY_leaf]
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (3:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (3:ℝ)/4 = (7/4:ℝ) by norm_num, show (4:ℝ) + (3:ℝ) = (7:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2688:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/7:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (7:ℝ) by norm_num)
        (show (7:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(7:ℝ) = (1/7:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_LLL
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = FSTAR := by
    have hcr2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hcr2, ρwit_leaf]
  have hrc3 : ρwit c3 = FSTAR := by
    have hcr3 : c3 = Branch.node [] := by
      cases c3 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h3; omega
    rw [hcr3, ρwit_leaf]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hy2e, hy3e, hS]

/-- Cell `LL2` (uses `d4_2LL`). -/
theorem subaction_deg4_LL2 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 0) (h3 : bcc c3 = 1) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2e : bY c2 = 1 := by
    have hc2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hc2, bY_leaf]
  have hy3_lo : (1:ℝ)/3 ≤ bY c3 := bY_ge_third_of_bcc1 c3 h3
  have hy3_hi : bY c3 ≤ 1/2 := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (7/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (7/3:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (7/3:ℝ)/4 = (19/12:ℝ) by norm_num, show (4:ℝ) + (7/3:ℝ) = (19/3:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2432:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/19:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (19/3:ℝ) by norm_num)
        (show (19/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(19/3:ℝ) = (3/19:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_2LL` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (19/12:ℝ) + (1 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (-1/2432:ℝ) :=
    tangent_atom (19/12:ℝ) (1) (5) (-1/2432:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = FSTAR := by
    have hcr2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hcr2, ρwit_leaf]
  have hrc3 : ρwit c3 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c3 - 1/3) := by
    simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hy2e, hS]

/-- Cell `LL3` (uses `d4_3LL`). -/
theorem subaction_deg4_LL3 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 0) (h3 : bcc c3 = 2) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2e : bY c2 = 1 := by
    have hc2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hc2, bY_leaf]
  have hy3_hi : bY c3 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (2:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (7/3:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (7/3:ℝ)/4 = (19/12:ℝ) by norm_num, show (4:ℝ) + (7/3:ℝ) = (19/3:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2304:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/6:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (6:ℝ) by norm_num)
        (show (6:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(6:ℝ) = (1/6:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_3LL
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = FSTAR := by
    have hcr2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hcr2, ρwit_leaf]
  have hrc3 : ρwit c3 = (1/32) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hy2e, hS]

/-- Cell `LL4` (uses `d4_4LL`). -/
theorem subaction_deg4_LL4 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 0) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2e : bY c2 = 1 := by
    have hc2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hc2, bY_leaf]
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (2:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (9/4:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (9/4:ℝ)/4 = (25/16:ℝ) by norm_num, show (4:ℝ) + (9/4:ℝ) = (25/4:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2304:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/6:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (6:ℝ) by norm_num)
        (show (6:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(6:ℝ) = (1/6:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_4LL
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = FSTAR := by
    have hcr2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hcr2, ρwit_leaf]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hy2e, hS]

/-- Cell `LLH` (uses `d4_5LL`). -/
theorem subaction_deg4_LLH (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 0) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2e : bY c2 = 1 := by
    have hc2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hc2, bY_leaf]
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (2:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (11/5:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (11/5:ℝ)/4 = (31/20:ℝ) by norm_num, show (4:ℝ) + (11/5:ℝ) = (31/5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2304:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/6:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (6:ℝ) by norm_num)
        (show (6:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(6:ℝ) = (1/6:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_5LL
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = FSTAR := by
    have hcr2 : c2 = Branch.node [] := by
      cases c2 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h2; omega
    rw [hcr2, ρwit_leaf]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hy1e, hy2e, hrc3_nn, hy3_hi, hS]

/-- Cell `L22` (uses `d4_22L`). -/
theorem subaction_deg4_L22 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 1) (h3 : bcc c3 = 1) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_lo : (1:ℝ)/3 ≤ bY c3 := bY_ge_third_of_bcc1 c3 h3
  have hy3_hi : bY c3 ≤ 1/2 := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (5/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (5/3:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (5/3:ℝ)/4 = (17/12:ℝ) by norm_num, show (4:ℝ) + (5/3:ℝ) = (17/3:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2176:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/17:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (17/3:ℝ) by norm_num)
        (show (17/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(17/3:ℝ) = (3/17:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+2); the `d4_22L` in D4.lean has kL=-2 (loose, wrong sign to combine)
  have henc : Real.log (17/12:ℝ) + (2 : ℤ) * Real.log (3/2) - (6 : ℤ) * FSTAR ≤ (-1/2176:ℝ) :=
    tangent_atom (17/12:ℝ) (2) (6) (-1/2176:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3 : ρwit c3 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c3 - 1/3) := by
    simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hS]

/-- Cell `L23` (uses `d4_23L`). -/
theorem subaction_deg4_L23 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 1) (h3 : bcc c3 = 2) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (4/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (5/3:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (5/3:ℝ)/4 = (17/12:ℝ) by norm_num, show (4:ℝ) + (5/3:ℝ) = (17/3:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2048:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/16:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (16/3:ℝ) by norm_num)
        (show (16/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(16/3:ℝ) = (3/16:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_23L` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (17/12:ℝ) + (1 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (61/6144:ℝ) :=
    tangent_atom (17/12:ℝ) (1) (4) (61/6144:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/32) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hS]

/-- Cell `L24` (uses `d4_24L`). -/
theorem subaction_deg4_L24 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 1) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (4/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (19/12:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (19/12:ℝ)/4 = (67/48:ℝ) by norm_num, show (4:ℝ) + (19/12:ℝ) = (67/12:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2048:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/16:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (16/3:ℝ) by norm_num)
        (show (16/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(16/3:ℝ) = (3/16:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_24L` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (67/48:ℝ) + (1 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (1/6144:ℝ) :=
    tangent_atom (67/48:ℝ) (1) (4) (1/6144:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hS]

/-- Cell `L2H` (uses `d4_25L`). -/
theorem subaction_deg4_L2H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 1) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (4/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (23/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (23/15:ℝ)/4 = (83/60:ℝ) by norm_num, show (4:ℝ) + (23/15:ℝ) = (83/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/2048:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/16:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (16/3:ℝ) by norm_num)
        (show (16/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(16/3:ℝ) = (3/16:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_25L` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (83/60:ℝ) + (1 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (-1/2048:ℝ) :=
    tangent_atom (83/60:ℝ) (1) (4) (-1/2048:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hy1e, hrc3_nn, hy3_hi, hS]

/-- Cell `L33` (uses `d4_33L`). -/
theorem subaction_deg4_L33 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 2) (h3 : bcc c3 = 2) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (5/3:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (5/3:ℝ)/4 = (17/12:ℝ) by norm_num, show (4:ℝ) + (5/3:ℝ) = (17/3:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_33L
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/32) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hS]

/-- Cell `L34` (uses `d4_34L`). -/
theorem subaction_deg4_L34 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 2) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (19/12:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (19/12:ℝ)/4 = (67/48:ℝ) by norm_num, show (4:ℝ) + (19/12:ℝ) = (67/12:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_34L
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hS]

/-- Cell `L3H` (uses `d4_35L`). -/
theorem subaction_deg4_L3H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (23/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (23/15:ℝ)/4 = (83/60:ℝ) by norm_num, show (4:ℝ) + (23/15:ℝ) = (83/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_35L
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hy1e, hrc3_nn, hy3_hi, hS]

/-- Cell `L44` (uses `d4_44L`). -/
theorem subaction_deg4_L44 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 3) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (3/2:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (3/2:ℝ)/4 = (11/8:ℝ) by norm_num, show (4:ℝ) + (3/2:ℝ) = (11/2:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_44L
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hy1e, hS]

/-- Cell `L4H` (uses `d4_45L`). -/
theorem subaction_deg4_L4H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : bcc c2 = 3) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (29/20:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (29/20:ℝ)/4 = (109/80:ℝ) by norm_num, show (4:ℝ) + (29/20:ℝ) = (109/20:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_45L
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hy1e, hrc3_nn, hy3_hi, hS]

/-- Cell `LHH` (uses `d4_55L`). -/
theorem subaction_deg4_LHH (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 0) (h2 : 4 ≤ bcc c2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1e : bY c1 = 1 := by
    have hc1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hc1, bY_leaf]
  have hy2_hi : bY c2 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c2
    have hcast : (4:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have hb2 : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (7/5:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (7/5:ℝ)/4 = (27/20:ℝ) by norm_num, show (4:ℝ) + (7/5:ℝ) = (27/5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_55L
  have hrc1 : ρwit c1 = FSTAR := by
    have hcr1 : c1 = Branch.node [] := by
      cases c1 with
      | node cs => cases cs with
        | nil => rfl
        | cons a t => simp only [bcc, List.length_cons] at h1; omega
    rw [hcr1, ρwit_leaf]
  have hrc2_nn : 0 ≤ ρwit c2 := ρwit_nonneg c2
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1]
  linarith [htan, hrnode_le, henc, hy1e, hrc2_nn, hy2_hi, hrc3_nn, hy3_hi, hS]

/-- Cell `222` (uses `d4_222`). -/
theorem subaction_deg4_222 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 1) (h3 : bcc c3 = 1) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_lo : (1:ℝ)/3 ≤ bY c3 := bY_ge_third_of_bcc1 c3 h3
  have hy3_hi : bY c3 ≤ 1/2 := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (1:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (1:ℝ)/4 = (5/4:ℝ) by norm_num, show (4:ℝ) + (1:ℝ) = (5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1920:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/5:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (5:ℝ) by norm_num)
        (show (5:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(5:ℝ) = (1/5:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+3); the `d4_222` in D4.lean has kL=-3 (loose, wrong sign to combine)
  have henc : Real.log (5/4:ℝ) + (3 : ℤ) * Real.log (3/2) - (7 : ℤ) * FSTAR ≤ (-1/1920:ℝ) :=
    tangent_atom (5/4:ℝ) (3) (7) (-1/1920:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3 : ρwit c3 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c3 - 1/3) := by
    simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `223` (uses `d4_223`). -/
theorem subaction_deg4_223 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 1) (h3 : bcc c3 = 2) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (2/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (1:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (1:ℝ)/4 = (5/4:ℝ) by norm_num, show (4:ℝ) + (1:ℝ) = (5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1792:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/14:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (14/3:ℝ) by norm_num)
        (show (14/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(14/3:ℝ) = (3/14:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+2); the `d4_223` in D4.lean has kL=-2 (loose, wrong sign to combine)
  have henc : Real.log (5/4:ℝ) + (2 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (53/5376:ℝ) :=
    tangent_atom (5/4:ℝ) (2) (5) (53/5376:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/32) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `224` (uses `d4_224`). -/
theorem subaction_deg4_224 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 1) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (2/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (11/12:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (11/12:ℝ)/4 = (59/48:ℝ) by norm_num, show (4:ℝ) + (11/12:ℝ) = (59/12:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1792:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/14:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (14/3:ℝ) by norm_num)
        (show (14/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(14/3:ℝ) = (3/14:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+2); the `d4_224` in D4.lean has kL=-2 (loose, wrong sign to combine)
  have henc : Real.log (59/48:ℝ) + (2 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (1/10752:ℝ) :=
    tangent_atom (59/48:ℝ) (2) (5) (1/10752:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `22H` (uses `d4_225`). -/
theorem subaction_deg4_22H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 1) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_lo : (1:ℝ)/3 ≤ bY c2 := bY_ge_third_of_bcc1 c2 h2
  have hy2_hi : bY c2 ≤ 1/2 := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (2/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (13/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (13/15:ℝ)/4 = (73/60:ℝ) by norm_num, show (4:ℝ) + (13/15:ℝ) = (73/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1792:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/14:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (14/3:ℝ) by norm_num)
        (show (14/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(14/3:ℝ) = (3/14:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+2); the `d4_225` in D4.lean has kL=-2 (loose, wrong sign to combine)
  have henc : Real.log (73/60:ℝ) + (2 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (-1/1792:ℝ) :=
    tangent_atom (73/60:ℝ) (2) (5) (-1/1792:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c2 - 1/3) := by
    simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hrc3_nn, hy3_hi, hS]

/-- Cell `233` (uses `d4_233`). -/
theorem subaction_deg4_233 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 2) (h3 : bcc c3 = 2) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (1:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (1:ℝ)/4 = (5/4:ℝ) by norm_num, show (4:ℝ) + (1:ℝ) = (5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1664:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/13:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (13/3:ℝ) by norm_num)
        (show (13/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(13/3:ℝ) = (3/13:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_233` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (5/4:ℝ) + (1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (101/4992:ℝ) :=
    tangent_atom (5/4:ℝ) (1) (3) (101/4992:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/32) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `234` (uses `d4_234`). -/
theorem subaction_deg4_234 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 2) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (11/12:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (11/12:ℝ)/4 = (59/48:ℝ) by norm_num, show (4:ℝ) + (11/12:ℝ) = (59/12:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1664:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/13:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (13/3:ℝ) by norm_num)
        (show (13/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(13/3:ℝ) = (3/13:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_234` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (59/48:ℝ) + (1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (209/19968:ℝ) :=
    tangent_atom (59/48:ℝ) (1) (3) (209/19968:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `23H` (uses `d4_235`). -/
theorem subaction_deg4_23H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (13/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (13/15:ℝ)/4 = (73/60:ℝ) by norm_num, show (4:ℝ) + (13/15:ℝ) = (73/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1664:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/13:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (13/3:ℝ) by norm_num)
        (show (13/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(13/3:ℝ) = (3/13:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_235` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (73/60:ℝ) + (1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (49/4992:ℝ) :=
    tangent_atom (73/60:ℝ) (1) (3) (49/4992:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hrc3_nn, hy3_hi, hS]

/-- Cell `244` (uses `d4_244`). -/
theorem subaction_deg4_244 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 3) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (5/6:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (5/6:ℝ)/4 = (29/24:ℝ) by norm_num, show (4:ℝ) + (5/6:ℝ) = (29/6:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1664:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/13:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (13/3:ℝ) by norm_num)
        (show (13/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(13/3:ℝ) = (3/13:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_244` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (29/24:ℝ) + (1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (7/9984:ℝ) :=
    tangent_atom (29/24:ℝ) (1) (3) (7/9984:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `24H` (uses `d4_245`). -/
theorem subaction_deg4_24H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : bcc c2 = 3) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (47/60:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (47/60:ℝ)/4 = (287/240:ℝ) by norm_num, show (4:ℝ) + (47/60:ℝ) = (287/60:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1664:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/13:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (13/3:ℝ) by norm_num)
        (show (13/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(13/3:ℝ) = (3/13:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_245` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (287/240:ℝ) + (1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (1/19968:ℝ) :=
    tangent_atom (287/240:ℝ) (1) (3) (1/19968:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hrc3_nn, hy3_hi, hS]

/-- Cell `2HH` (uses `d4_255`). -/
theorem subaction_deg4_2HH (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 1) (h2 : 4 ≤ bcc c2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_lo : (1:ℝ)/3 ≤ bY c1 := bY_ge_third_of_bcc1 c1 h1
  have hy1_hi : bY c1 ≤ 1/2 := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c2
    have hcast : (4:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have hb2 : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (1/3:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (11/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (11/15:ℝ)/4 = (71/60:ℝ) by norm_num, show (4:ℝ) + (11/15:ℝ) = (71/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1664:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (3/13:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (13/3:ℝ) by norm_num)
        (show (13/3:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(13/3:ℝ) = (3/13:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  -- correctly-signed atom (kL=+1); the `d4_255` in D4.lean has kL=-1 (loose, wrong sign to combine)
  have henc : Real.log (71/60:ℝ) + (1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (-1/1664:ℝ) :=
    tangent_atom (71/60:ℝ) (1) (3) (-1/1664:ℝ) (by norm_num) (by norm_num)
  have hrc1 : ρwit c1 = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c1 - 1/3) := by
    simp only [ρwit, h1]
  have hrc2_nn : 0 ≤ ρwit c2 := ρwit_nonneg c2
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1]
  linarith [htan, hrnode_le, henc, hrc2_nn, hy2_hi, hrc3_nn, hy3_hi, hS]

/-- Cell `333` (uses `d4_333`). -/
theorem subaction_deg4_333 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 2) (h2 : bcc c2 = 2) (h3 : bcc c3 = 2) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (1:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (1:ℝ)/4 = (5/4:ℝ) by norm_num, show (4:ℝ) + (1:ℝ) = (5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_333
  have hrc1 : ρwit c1 = (1/32) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/32) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `334` (uses `d4_334`). -/
theorem subaction_deg4_334 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 2) (h2 : bcc c2 = 2) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (11/12:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (11/12:ℝ)/4 = (59/48:ℝ) by norm_num, show (4:ℝ) + (11/12:ℝ) = (59/12:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_334
  have hrc1 : ρwit c1 = (1/32) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `33H` (uses `d4_335`). -/
theorem subaction_deg4_33H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 2) (h2 : bcc c2 = 2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (13/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (13/15:ℝ)/4 = (73/60:ℝ) by norm_num, show (4:ℝ) + (13/15:ℝ) = (73/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_335
  have hrc1 : ρwit c1 = (1/32) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/32) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hrc3_nn, hy3_hi, hS]

/-- Cell `344` (uses `d4_344`). -/
theorem subaction_deg4_344 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 2) (h2 : bcc c2 = 3) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (5/6:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (5/6:ℝ)/4 = (29/24:ℝ) by norm_num, show (4:ℝ) + (5/6:ℝ) = (29/6:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_344
  have hrc1 : ρwit c1 = (1/32) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `34H` (uses `d4_345`). -/
theorem subaction_deg4_34H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 2) (h2 : bcc c2 = 3) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (47/60:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (47/60:ℝ)/4 = (287/240:ℝ) by norm_num, show (4:ℝ) + (47/60:ℝ) = (287/60:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_345
  have hrc1 : ρwit c1 = (1/32) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hrc3_nn, hy3_hi, hS]

/-- Cell `3HH` (uses `d4_355`). -/
theorem subaction_deg4_3HH (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 2) (h2 : 4 ≤ bcc c2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/3:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c2
    have hcast : (4:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have hb2 : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (11/15:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (11/15:ℝ)/4 = (71/60:ℝ) by norm_num, show (4:ℝ) + (11/15:ℝ) = (71/15:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_355
  have hrc1 : ρwit c1 = (1/32) * bY c1 := by simp only [ρwit, h1]
  have hrc2_nn : 0 ≤ ρwit c2 := ρwit_nonneg c2
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1]
  linarith [htan, hrnode_le, henc, hrc2_nn, hy2_hi, hrc3_nn, hy3_hi, hS]

/-- Cell `444` (uses `d4_444`). -/
theorem subaction_deg4_444 (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 3) (h2 : bcc c2 = 3) (h3 : bcc c3 = 3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c3; rw [h3] at h; norm_num at h; linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (3/4:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (3/4:ℝ)/4 = (19/16:ℝ) by norm_num, show (4:ℝ) + (3/4:ℝ) = (19/4:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_444
  have hrc1 : ρwit c1 = (1/384) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3 : ρwit c3 = (1/384) * bY c3 := by simp only [ρwit, h3]
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2, hrc3]
  linarith [htan, hrnode_le, henc, hS]

/-- Cell `44H` (uses `d4_445`). -/
theorem subaction_deg4_44H (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 3) (h2 : bcc c2 = 3) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c2; rw [h2] at h; norm_num at h; linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (7/10:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (7/10:ℝ)/4 = (47/40:ℝ) by norm_num, show (4:ℝ) + (7/10:ℝ) = (47/10:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_445
  have hrc1 : ρwit c1 = (1/384) * bY c1 := by simp only [ρwit, h1]
  have hrc2 : ρwit c2 = (1/384) * bY c2 := by simp only [ρwit, h2]
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1, hrc2]
  linarith [htan, hrnode_le, henc, hrc3_nn, hy3_hi, hS]

/-- Cell `4HH` (uses `d4_455`). -/
theorem subaction_deg4_4HH (c1 c2 c3 : Branch)
    (h1 : bcc c1 = 3) (h2 : 4 ≤ bcc c2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/4:ℝ) := by
    have h := bY_le_inv_deg c1; rw [h1] at h; norm_num at h; linarith
  have hy2_hi : bY c2 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c2
    have hcast : (4:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have hb2 : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (13/20:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (13/20:ℝ)/4 = (93/80:ℝ) by norm_num, show (4:ℝ) + (13/20:ℝ) = (93/20:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_455
  have hrc1 : ρwit c1 = (1/384) * bY c1 := by simp only [ρwit, h1]
  have hrc2_nn : 0 ≤ ρwit c2 := ρwit_nonneg c2
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs, hrc1]
  linarith [htan, hrnode_le, henc, hrc2_nn, hy2_hi, hrc3_nn, hy3_hi, hS]

/-- Cell `HHH` (uses `d4_555`). -/
theorem subaction_deg4_HHH (c1 c2 c3 : Branch)
    (h1 : 4 ≤ bcc c1) (h2 : 4 ≤ bcc c2) (h3 : 4 ≤ bcc c3) :
    (Real.log (1 + (([c1, c2, c3]).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3]).map ρwit).sum := by
  have hy1_0 := bY_nonneg c1
  have hy2_0 := bY_nonneg c2
  have hy3_0 := bY_nonneg c3
  have hy1_hi : bY c1 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c1
    have hcast : (4:ℝ) ≤ (bcc c1 : ℝ) := by exact_mod_cast h1
    have hb2 : (1:ℝ) / ((bcc c1 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy2_hi : bY c2 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c2
    have hcast : (4:ℝ) ≤ (bcc c2 : ℝ) := by exact_mod_cast h2
    have hb2 : (1:ℝ) / ((bcc c2 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hy3_hi : bY c3 ≤ (1/5:ℝ) := by
    have hbi := bY_le_inv_deg c3
    have hcast : (4:ℝ) ≤ (bcc c3 : ℝ) := by exact_mod_cast h3
    have hb2 : (1:ℝ) / ((bcc c3 : ℝ) + 1) ≤ 1/5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set S := bY c1 + bY c2 + bY c3 with hS
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hSmin : (0:ℝ) ≤ S := by rw [hS]; linarith
  have hden : (0:ℝ) < 4 + S := by linarith
  have htan := log_tangent (d := (4:ℝ)) (s := S) (s0 := (3/5:ℝ)) (by norm_num) hS0 (by norm_num)
  rw [show (1:ℝ) + (3/5:ℝ)/4 = (23/20:ℝ) by norm_num, show (4:ℝ) + (3/5:ℝ) = (23/5:ℝ) by norm_num] at htan
  have hbYnode : bY (Branch.node [c1, c2, c3]) = 1 / (4 + S) := by
    rw [bY_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hbcc_node : bcc (Branch.node [c1, c2, c3]) = 3 := by simp [bcc]
  have hrnode : ρwit (Branch.node [c1, c2, c3]) = (1/384) * (1 / (4 + S)) := by
    rw [ρwit, hbcc_node, hbYnode]; norm_num
  have hrnode_le : ρwit (Branch.node [c1, c2, c3]) ≤ (1/1536:ℝ) := by
    rw [hrnode]
    have hinv : 1 / (4 + S) ≤ (1/4:ℝ) := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < (4:ℝ) by norm_num)
        (show (4:ℝ) ≤ 4 + S by linarith)
      rwa [show (1:ℝ)/(4:ℝ) = (1/4:ℝ) by norm_num] at h
    have hinv_nn : (0:ℝ) ≤ 1 / (4 + S) := by positivity
    nlinarith [hinv, hinv_nn]
  have henc := d4_555
  have hrc1_nn : 0 ≤ ρwit c1 := ρwit_nonneg c1
  have hrc2_nn : 0 ≤ ρwit c2 := ρwit_nonneg c2
  have hrc3_nn : 0 ≤ ρwit c3 := ρwit_nonneg c3
  have hlogarg : (1:ℝ) + (([c1, c2, c3]).map bY).sum
      / ((([c1, c2, c3] : List Branch).length : ℝ) + 1) = 1 + S / 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [hS]; ring
  have hrhs : (([c1, c2, c3]).map ρwit).sum = ρwit c1 + ρwit c2 + ρwit c3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [hlogarg, hrhs]
  linarith [htan, hrnode_le, henc, hrc1_nn, hy1_hi, hrc2_nn, hy2_hi, hrc3_nn, hy3_hi, hS]
end BGSCL
end R3Cert
