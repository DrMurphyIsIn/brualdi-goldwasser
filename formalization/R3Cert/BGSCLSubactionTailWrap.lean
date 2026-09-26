/-
  The tail (deg≥5) STRAGGLER cells + the unified `tail_wrapper` (2026-09-04).

  The `tail_decouple` backbone (`R3Cert.BGSCLSubactionTailDecouple`) already closes the two uniform-reference
  regimes of `IsSubaction ρwit` for a tail hub (`d = |cs|+1 ≥ 5`, `ρwit(node cs) = 0`):
    * `subaction_tail_deg4` — `|cs| ∈ [9,60]` (deg-4 reference `S0 = |cs|/4`), and
    * `subaction_tail_deg5` — `|cs| ≥ 64`   (deg-5 reference `S0 = |cs|/5`),
  plus the tie cell `subaction_tail_d6` — `|cs| = 5` (all-cherry reference `S0 = 5/3`).

  This file discharges the SEVEN remaining "straggler" degrees and assembles the full-tail closer:

    * CHERRY cells `|cs| ∈ {4,6,7,8}` (degrees `d ∈ {5,7,8,9}`): `tail_decouple` at the all-cherry reference
      `S0 = |cs|/3` (`σ = 3/(4d−1)`), per-child min `phi_lb_cherry`, and the B-obligation
      `log((4d−1)/(3d)) ≤ (2d−1)F* − (d−1)log(3/2)` = `tail_all_deg2` at the concrete `d` (the `(d−1)/(4d−1)`
      terms cancel exactly; `m = a − σ/3`, `a = 2F* − log(3/2)`).

    * BOUNDARY cells `|cs| ∈ {61,62,63}` (degrees `d ∈ {62,63,64}`): the transition zone where neither
      `|cs|/4` nor `|cs|/5` is slack enough.  Handled by pinning the reference so `σ = 5/384` exactly
      (`S0 = 384/5 − d`), per-child min `phi_lb_deg4` (which is TIGHT at `σ = 5/384`, `m = −1/384`), and a
      crude `log x ≤ x−1` B-obligation: the log argument collapses to `384/(5d)` and `(384/(5d))¹¹·64/621`
      is ≤ `1 + 11·extra` with ample slack.

    * `cherry_anchor_le_tight` — the tight UPPER cherry anchor `2F* − log(3/2) ≤ 133/17061` (the mirror of
      `cherry_anchor_ge_tight`; needed nowhere below in the end, since the cherry B-terms cancel exactly, but
      delivered as the requested tight upper bound via the exact `(1/11)·log(529/486)` identity).

  Finally `tail_wrapper` dispatches `interval_cases`/`omega` over `|cs|` on the gap-free partition
  `{4} ∪ {5} ∪ {6,7,8} ∪ [9,60] ∪ {61,62,63} ∪ [64,∞)`, closing `IsSubaction ρwit` for EVERY tail hub.

  Kernel-checked vs `R3Cert.BGSCLSubactionTailDecouple`/`BGSCLSubactionTail`/`BGSCLSubaction`.  No `sorry`.
  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionTail
import R3Cert.BGSCLSubactionTailDecouple

namespace R3Cert
namespace BGSCL

open Real

/-! ### The tight UPPER cherry anchor (mirror of `cherry_anchor_ge_tight`). -/

/-- **Tight upper cherry anchor** `2F* − log(3/2) ≤ 133/17061`.  Mirror of `cherry_anchor_ge_tight`: uses the
    exact `2F* − log(3/2) = (1/11)·log(529/486)` (`529/486 = (621/64)²·(2/3)¹¹`) and bounds `log(529/486)`
    ABOVE via `529/486 ≤ exp(11·C)` (`Real.log_le_iff_le_exp` + `Real.exp_bound`, a degree-3 Taylor LOWER
    bound on `exp`).  `133/17061 = 11·(133/17061)/11 ≈ 0.007795`, a clean rational `≥ 2F* − log(3/2) ≈ 0.007707`. -/
theorem cherry_anchor_le_tight : 2 * FSTAR - Real.log (3/2) ≤ 133/17061 := by
  have hkey : (2:ℝ) * FSTAR - Real.log (3/2) = (1/11) * Real.log (529/486) := by
    rw [FSTAR, show (529/486:ℝ) = (621/64)^(2:ℕ) * (2/3)^(11:ℕ) by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (2/3:ℝ) = (3/2)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hkey]
  -- 11·(133/17061) = 1463/17061 = 133/1551.  Show log(529/486) ≤ 133/1551.
  have hlog : Real.log (529/486) ≤ (133:ℝ)/1551 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hb := Real.exp_bound (x := (133/1551 : ℝ)) (by norm_num) (n := 3) (by norm_num)
    have hb1 := (abs_le.mp hb).1
    have hs : ∑ i ∈ Finset.range 3, (133/1551:ℝ)^i / (i.factorial:ℝ)
        = 1 + 133/1551 + (133/1551)^2/2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hs] at hb1
    -- exp(133/1551) ≥ (1 + 133/1551 + (133/1551)²/2) − err ≥ 529/486
    have herr : |(133/1551:ℝ)|^3 * ((3+1)/((Nat.factorial 3:ℝ)*3))
        ≤ (1 + 133/1551 + (133/1551)^2/2) - 529/486 := by
      norm_num [Nat.factorial]
    linarith [hb1, herr]
  linarith [hlog]

/-! ### The cherry (all-deg-2 reference) per-child min, parameterized by degree. -/

/-- **Per-child min for the cherry (all-deg-2) reference.**  For any `σ ∈ (0, 3/23]` and `m = a − σ/3`
    (`a = 2F* − log(3/2)`), `m + σ·bY c ≤ ρwit c` for every branch.  Valid for `σ ∈ [1/11, 3/23]`, the range
    covering the four cherry straggler degrees (`σ ∈ {1/8,1/10,1/11}`).  The cherry-corner `m = a − σ/3` is
    tight at the deg-2 child (`bY = 1/3`); the other child types are dominated using the TIGHT upper anchor
    `cherry_anchor_le_tight` (`a ≤ 133/17061`): deg-4 (`a ≤ 1/1536 + σ/12`, the binding constraint that forces
    `σ ≥ 1/11`), deg-3 (`3a ≤ σ`), deg-≥5 (`a ≤ (2/15)σ`); leaf via the anchor `1/6 ≤ log(3/2) − F*`
    (so `(2/3)σ ≤ (2/3)(3/19) = 2/19 ≤ 1/6`). -/
theorem phi_lb_cherry (σ : ℝ) (hσlo : 1/11 ≤ σ) (hσhi : σ ≤ 3/19) (c : Branch) :
    (2 * FSTAR - Real.log (3/2) - σ/3) + σ * bY c ≤ ρwit c := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hy0 := bY_nonneg c
  have hyd := bY_le_inv_deg c
  have hAub := cherry_anchor_le_tight   -- 2F* − log(3/2) ≤ 133/17061  (a ≤ ~0.007796)
  -- lower anchor `1/9 ≤ log(3/2) − F*` (needed for σ up to 3/19 in the leaf case, since (2/3)(3/19)=2/19≤1/9):
  -- 11·(log(3/2) − F*) = log((3/2)¹¹·64/621) and (3/2)¹¹·64/621 ≈ 8.914 ≥ exp(11/9) ≈ 3.395.
  have hEl : (1:ℝ)/9 ≤ Real.log (3/2) - FSTAR := by
    rw [FSTAR]
    have hY : (0:ℝ) < (3/2 : ℝ) ^ (11:ℕ) * (64/621) := by positivity
    have hlog : Real.log ((3/2 : ℝ) ^ (11:ℕ) * (64/621))
        = 11 * Real.log (3/2) - Real.log (621/64) := by
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
          show (64/621 : ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
      push_cast; ring
    have hge : (11:ℝ)/9 ≤ Real.log ((3/2 : ℝ) ^ (11:ℕ) * (64/621)) := by
      rw [Real.le_log_iff_exp_le hY]
      -- exp(11/9) = exp(1)·exp(2/9) ≤ 2.7182818286 · (deg-4 Taylor ub) ≤ 4 ≤ (3/2)¹¹·64/621.
      have he29 : Real.exp (2/9 : ℝ) ≤ (1 + 2/9 + (2/9)^2/2 + (2/9)^3/6) + (2/9:ℝ)^4 * ((4+1)/((Nat.factorial 4:ℝ)*4)) := by
        have hb := Real.exp_bound (x := (2/9 : ℝ)) (by rw [abs_of_nonneg] <;> norm_num) (n := 4) (by norm_num)
        have hhi := (abs_le.mp hb).2
        have hs : ∑ i ∈ Finset.range 4, (2/9:ℝ)^i / (i.factorial:ℝ)
            = 1 + 2/9 + (2/9)^2/2 + (2/9)^3/6 := by simp [Finset.sum_range_succ, Nat.factorial]
        have habs : |(2/9:ℝ)| = 2/9 := by rw [abs_of_nonneg]; norm_num
        rw [hs, habs] at hhi; linarith
      have hsplit : Real.exp (11/9 : ℝ) = Real.exp 1 * Real.exp (2/9 : ℝ) := by
        rw [← Real.exp_add]; norm_num
      calc Real.exp (11/9 : ℝ) = Real.exp 1 * Real.exp (2/9 : ℝ) := hsplit
        _ ≤ 2.7182818286 * ((1 + 2/9 + (2/9)^2/2 + (2/9)^3/6) + (2/9:ℝ)^4 * ((4+1)/((Nat.factorial 4:ℝ)*4))) := by
            apply mul_le_mul (le_of_lt Real.exp_one_lt_d9) he29 (le_of_lt (Real.exp_pos _)) (by norm_num)
        _ ≤ 4 := by norm_num [Nat.factorial]
        _ ≤ (3/2 : ℝ) ^ (11:ℕ) * (64/621) := by norm_num
    rw [hlog] at hge; linarith
  rcases hbc : bcc c with _ | _ | _ | _ | n
  · -- leaf: bY = 1, ρwit = F*.
    have hby1 : bY c = 1 := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact bY_leaf
    have hrc : ρwit c = FSTAR := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact ρwit_leaf
    rw [hby1, hrc]
    -- goal ⟺ F* − log(3/2) + (2/3)σ ≤ 0; from hEl (1/6 ≤ log(3/2)−F*) and σ ≤ 3/19 ⇒ (2/3)σ ≤ 2/19 ≤ 1/6.
    nlinarith [hEl, hσhi]
  · have hby3 : (1:ℝ)/3 ≤ bY c := bY_ge_third_of_bcc1 c hbc
    have hrc : ρwit c = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c - 1/3) := by
      simp only [ρwit, hbc]
    rw [hrc]
    -- goal ⟺ (σ − 1/4)(bY − 1/3) ≤ 0 (deg-2 corner, tight at bY = 1/3).
    nlinarith [hσhi, mul_nonneg (show (0:ℝ) ≤ bY c - 1/3 by linarith)
      (show (0:ℝ) ≤ 1/4 - σ by linarith)]
  · have hby : bY c ≤ 1/3 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/32) * bY c := by simp only [ρwit, hbc]
    rw [hrc]
    -- (a − σ/3) + σ·bY ≤ bY/32 ⟺ a − σ/3 + bY(σ − 1/32) ≤ 0.  σ ≥ 1/11 > 1/32; worst bY = 0: a ≤ σ/3.
    -- 3a ≤ 3·(133/17061) ≈ 0.0234 ≤ 1/11 ≤ σ.
    nlinarith [hAub, hσlo, hby, hy0,
      mul_nonneg hy0 (show (0:ℝ) ≤ σ - 1/32 by linarith)]
  · have hby : bY c ≤ 1/4 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/384) * bY c := by simp only [ρwit, hbc]
    rw [hrc]
    -- (a − σ/3) + σ·bY ≤ bY/384 ⟺ a − σ/3 + bY(σ − 1/384) ≤ 0.  worst bY = 1/4: a ≤ 1/1536 + σ/12.
    -- a ≤ 133/17061 ≤ 1/1536 + (1/11)/12 ≤ 1/1536 + σ/12.  This is the constraint forcing σ ≥ 1/11.
    nlinarith [hAub, hσlo, hby, hy0,
      mul_nonneg (show (0:ℝ) ≤ 1/4 - bY c by linarith) (show (0:ℝ) ≤ σ - 1/384 by linarith)]
  · have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hby : bY c ≤ 1/5 := by
      rw [hbc] at hyd
      have hd5 : (5:ℝ) ≤ ((n + 4 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hle : (1:ℝ) / (((n + 4 : ℕ) : ℝ) + 1) ≤ 1/5 :=
        one_div_le_one_div_of_le (by norm_num) hd5
      linarith
    have hrc : ρwit c = 0 := by
      cases c with
      | node cs => simp only [bcc] at hbc; exact ρwit_node_high (by omega)
    rw [hrc]
    -- (a − σ/3) + σ·bY ≤ 0.  worst bY = 1/5: a ≤ (2/15)σ.  a ≤ 133/17061 ≤ (2/15)(1/11).
    nlinarith [hAub, hσlo, hby, hy0, mul_nonneg (show (0:ℝ) ≤ σ by linarith)
      (show (0:ℝ) ≤ 1/5 - bY c by linarith)]

/-! ### The four CHERRY straggler cells `d ∈ {5,7,8,9}` (`|cs| ∈ {4,6,7,8}`).

  Each is a `tail_decouple` instantiation with the cherry-corner per-child min `phi_lb_cherry` (`m = a − σ/3`,
  `a = 2F* − log(3/2)`).  The reference `S0` (hence `σ = 1/(d+S0)`) is chosen in the per-degree feasibility
  window `[deg-4 floor, B ceiling]`: the deg-4 CHILD needs `σ ≥ 12(a − 1/1536) ≈ 0.085` (so `σ ≥ 1/11`), while
  the B-obligation needs `σ` not too large.
    * `d = 5` (`S0 = 4/3`, `σ = 3/19`) and `d = 7` (`S0 = 2`, `σ = 1/9`): the all-cherry reference `S0 = (d−1)/3`,
      so B collapses EXACTLY to `tail_all_deg2` at the concrete `d` (the `(d−1)/(4d−1)` terms cancel).
    * `d = 8` (`S0 = 2`, `σ = 1/10`) and `d = 9` (`S0 = 2`, `σ = 1/11`): shifted references (the cherry `σ` would
      undershoot the deg-4 floor), so B is `log(arg) ≤ F* + rational`, discharged by the exact 11-fold
      `11·(log(arg) − F*) = log(arg¹¹·(3/2)^{11(d−1)}·(64/621)^{2d−1})` and a Taylor exp LOWER bound
      (`Real.log_le_iff_le_exp` + `Real.exp_bound`): `arg ≤ exp(rational)`. -/

/-- **CHERRY cell `d = 5`** (`|cs| = 4`).  `S0 = 4/3`, `σ = 3/19`, B = `tail_all_deg2 5`. -/
theorem subaction_tail_d5 (cs : List Branch) (hlen : cs.length = 4) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple cs (4/3) (2 * FSTAR - Real.log (3/2) - (3/19)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 4/3) = 3/19 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (3/19) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 4/3 / (4 + 1) = 19/15 by norm_num,
        show (4:ℝ)/3 / ((4 + 1) + 4/3) = 4/19 by norm_num]
    have h := tail_all_deg2 5 (by norm_num)
    push_cast at h
    rw [show (4 * (5:ℝ) - 1) / (3 * 5) = 19/15 by norm_num] at h
    linarith

/-- **CHERRY cell `d = 7`** (`|cs| = 6`).  `S0 = 2`, `σ = 3/27 = 1/9`, B = `tail_all_deg2 7`. -/
theorem subaction_tail_d7 (cs : List Branch) (hlen : cs.length = 6) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple cs 2 (2 * FSTAR - Real.log (3/2) - (1/9)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 2) = 1/9 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (1/9) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 2 / (6 + 1) = 9/7 by norm_num,
        show (2:ℝ) / ((6 + 1) + 2) = 2/9 by norm_num]
    have h := tail_all_deg2 7 (by norm_num)
    push_cast at h
    rw [show (4 * (7:ℝ) - 1) / (3 * 7) = 9/7 by norm_num] at h
    linarith

/-- The d=8 B-fold: `log(5/4) ≤ (15·F* − 7·log(3/2)) − 1/30`, i.e. `arg = 5/4` meets the shifted reference.
    Exact 11-fold `11·log(5/4) − 15·log(621/64) + 77·log(3/2) = log(val)`, `val = (5/4)¹¹·(3/2)⁷⁷·(64/621)¹⁵ ≈ 0.663`;
    since `−11/30 < 0`, `log(val) ≤ −11/30 ⟺ val ≤ exp(−11/30) = 1/exp(11/30)`, reduced to `val ≤ 1/tub` where
    `tub ≥ exp(11/30)` is a degree-3 Taylor UPPER bound on `exp` (`Real.exp_bound`). -/
theorem henc_cherry_d8 : Real.log (5/4) ≤ (15 * FSTAR - 7 * Real.log (3/2)) - 1/30 := by
  set val : ℝ := (5/4:ℝ)^(11:ℕ) * (3/2:ℝ)^(77:ℕ) * ((621/64:ℝ)^(15:ℕ))⁻¹ with hvaldef
  have hvalpos : (0:ℝ) < val := by rw [hvaldef]; positivity
  have hlog : Real.log val = 11 * Real.log (5/4) + 77 * Real.log (3/2) - 15 * Real.log (621/64) := by
    rw [hvaldef, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  -- exp(11/30) ≤ 1 + 11/30 + (11/30)²/2 + err  (degree-3 Taylor UPPER bound); call the RHS `tub`.
  have hb := Real.exp_bound (x := (11/30 : ℝ)) (by norm_num) (n := 3) (by norm_num)
  have hhi := (abs_le.mp hb).2
  have hs : ∑ i ∈ Finset.range 3, (11/30:ℝ)^i / (i.factorial:ℝ) = 1 + 11/30 + (11/30)^2/2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hhi
  have hexpub : Real.exp (11/30) ≤ (2140657 : ℝ)/1458000 := by
    have herr : (1 + 11/30 + (11/30)^2/2) + |(11/30:ℝ)|^3 * ((3+1)/((Nat.factorial 3:ℝ)*3))
        ≤ (2140657 : ℝ)/1458000 := by norm_num [Nat.factorial]
    linarith [hhi, herr]
  have hexppos : (0:ℝ) < Real.exp (11/30) := Real.exp_pos _
  -- val ≤ exp(−11/30) = 1/exp(11/30);  since exp(11/30) ≤ tub and val·tub ≤ 1.
  have hvalle : val ≤ Real.exp (-(11/30)) := by
    rw [Real.exp_neg]
    rw [le_inv_comm₀ hvalpos hexppos]
    calc Real.exp (11/30) ≤ (2140657:ℝ)/1458000 := hexpub
      _ ≤ val⁻¹ := by rw [hvaldef, le_inv_comm₀ (by norm_num) (by positivity)]; norm_num
  have hfinal : Real.log val ≤ -(11/30) := by
    rw [Real.log_le_iff_le_exp hvalpos]; exact hvalle
  rw [hlog] at hfinal
  simp only [FSTAR]
  linarith

/-- **CHERRY cell `d = 8`** (`|cs| = 7`).  Shifted reference `S0 = 2` (`σ = 1/10`); B via `henc_cherry_d8`. -/
theorem subaction_tail_d8 (cs : List Branch) (hlen : cs.length = 7) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple cs 2 (2 * FSTAR - Real.log (3/2) - (1/10)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 2) = 1/10 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (1/10) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 2 / (7 + 1) = 5/4 by norm_num,
        show (2:ℝ) / ((7 + 1) + 2) = 1/5 by norm_num]
    -- B: 0 ≤ 7·(a − 1/30) + F* − log(5/4) + 1/5, a = 2F* − log(3/2).
    -- ⟺ log(5/4) ≤ 7·(2F* − log(3/2)) + F* − 7/30 + 1/5 = 15F* − 7log(3/2) − 1/30.
    have h := henc_cherry_d8
    linarith

/-- The d=9 B-fold: `log(11/9) ≤ (17·F* − 8·log(3/2)) − 2/33`.  Exact 11-fold
    `11·log(11/9) − 17·log(621/64) + 88·log(3/2) = log(val)`, `val = (11/9)¹¹·(3/2)⁸⁸·(64/621)¹⁷ ≈ 0.476`;
    `log(val) ≤ −2/3 ⟺ val ≤ exp(−2/3) = 1/exp(2/3)`, reduced to `val ≤ 1/2` (`exp(2/3) ≤ 2`, a degree-4
    Taylor UPPER bound). -/
theorem henc_cherry_d9 : Real.log (11/9) ≤ (17 * FSTAR - 8 * Real.log (3/2)) - 2/33 := by
  set val : ℝ := (11/9:ℝ)^(11:ℕ) * (3/2:ℝ)^(88:ℕ) * ((621/64:ℝ)^(17:ℕ))⁻¹ with hvaldef
  have hvalpos : (0:ℝ) < val := by rw [hvaldef]; positivity
  have hlog : Real.log val = 11 * Real.log (11/9) + 88 * Real.log (3/2) - 17 * Real.log (621/64) := by
    rw [hvaldef, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  -- exp(2/3) ≤ 2  (degree-4 Taylor UPPER bound)
  have hb := Real.exp_bound (x := (2/3 : ℝ)) (by norm_num) (n := 4) (by norm_num)
  have hhi := (abs_le.mp hb).2
  have hs : ∑ i ∈ Finset.range 4, (2/3:ℝ)^i / (i.factorial:ℝ)
      = 1 + 2/3 + (2/3)^2/2 + (2/3)^3/6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hhi
  have hexpub : Real.exp (2/3) ≤ (2:ℝ) := by
    have herr : (1 + 2/3 + (2/3)^2/2 + (2/3)^3/6) + |(2/3:ℝ)|^4 * ((4+1)/((Nat.factorial 4:ℝ)*4))
        ≤ (2:ℝ) := by norm_num [Nat.factorial]
    linarith [hhi, herr]
  have hexppos : (0:ℝ) < Real.exp (2/3) := Real.exp_pos _
  have hvalle : val ≤ Real.exp (-(2/3)) := by
    rw [Real.exp_neg, le_inv_comm₀ hvalpos hexppos]
    calc Real.exp (2/3) ≤ (2:ℝ) := hexpub
      _ ≤ val⁻¹ := by rw [hvaldef, le_inv_comm₀ (by norm_num) (by positivity)]; norm_num
  have hfinal : Real.log val ≤ -(2/3) := by
    rw [Real.log_le_iff_le_exp hvalpos]; exact hvalle
  rw [hlog] at hfinal
  simp only [FSTAR]
  linarith

/-- **CHERRY cell `d = 9`** (`|cs| = 8`).  Shifted reference `S0 = 2` (`σ = 1/11`); B via `henc_cherry_d9`. -/
theorem subaction_tail_d9 (cs : List Branch) (hlen : cs.length = 8) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple cs 2 (2 * FSTAR - Real.log (3/2) - (1/11)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 2) = 1/11 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (1/11) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 2 / (8 + 1) = 11/9 by norm_num,
        show (2:ℝ) / ((8 + 1) + 2) = 2/11 by norm_num]
    -- B ⟺ log(11/9) ≤ 8·(2F* − log(3/2)) + F* − 8/33 + 2/11 = 17F* − 8log(3/2) − 2/33.
    have h := henc_cherry_d9
    linarith


/-! ### The three BOUNDARY straggler cells `d ∈ {62,63,64}` (`|cs| ∈ {61,62,63}`).

  The transition zone.  Pin the reference so `σ = 5/384` exactly (`S0 = 384/5 − d`, `d = |cs|+1`): then the
  deg-4 per-child min `phi_lb_deg4` applies at its tight lower corner (`m = 1/1536 − (5/384)/4 = −1/384`), and
  the log argument at the reference collapses to `384/(5d)` (since `(|cs|+1) + S0 = 384/5`).  The B-obligation
  `log(384/(5d)) ≤ F* + extra` is discharged by the exact fold `11·(log(384/(5d)) − F*) = log((384/(5d))¹¹·64/621)`
  and the crude `log x ≤ x − 1` (the fold value is ≤ `1 + 11·extra` with wide slack). -/

/-- Shared boundary closer: for a tail hub with `|cs| = L`, reference `S0 = 384/5 − (L+1)` (so `σ = 5/384`),
    given `S0 ≥ 0` and the B-obligation as a raw numeric inequality. -/
private theorem tail_boundary_cell (cs : List Branch) (L : ℕ) (hLge : 4 ≤ L) (hlen : cs.length = L)
    (hS0 : (0:ℝ) ≤ 384/5 - ((L:ℝ) + 1))
    (hB : (0:ℝ) ≤ (L:ℝ) * (-1/384)
            + (FSTAR - Real.log (1 + (384/5 - ((L:ℝ)+1)) / ((L:ℝ) + 1))
               + (384/5 - ((L:ℝ)+1)) / (((L:ℝ) + 1) + (384/5 - ((L:ℝ)+1))))) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  subst hlen
  refine tail_decouple cs (384/5 - ((cs.length:ℝ)+1)) (-1/384) h4 hS0 ?_ hB
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + (384/5 - ((cs.length:ℝ)+1))) = 5/384 := by
      have : ((cs.length : ℝ) + 1) + (384/5 - ((cs.length:ℝ)+1)) = 384/5 := by ring
      rw [this]; norm_num
    rw [hσ]
    have := phi_lb_deg4 (5/384) (by norm_num) (by norm_num) c
    -- phi_lb_deg4 gives (1/1536 − (5/384)/4) + (5/384)·bY ≤ ρwit; 1/1536 − 5/1536 = −1/384
    have heq : (1/1536 - (5/384)/4 : ℝ) = -1/384 := by norm_num
    rw [heq] at this
    exact this

/-- Discharge the boundary B-obligation for a concrete `|cs| = L` via the exact fold and `log x ≤ x − 1`.
    `arg = 1 + S0/(L+1) = 384/(5(L+1))`; `11·(log arg − F*) = log(arg¹¹·64/621)`; the fold value is
    `≤ 1 + 11·extra`, so `log(fold) ≤ 11·extra` and `B ≥ 0`. -/
private theorem tail_boundary_B (L : ℕ) (hL : 61 ≤ L) (hL2 : L ≤ 63) :
    (0:ℝ) ≤ (L:ℝ) * (-1/384)
      + (FSTAR - Real.log (1 + (384/5 - ((L:ℝ)+1)) / ((L:ℝ) + 1))
         + (384/5 - ((L:ℝ)+1)) / (((L:ℝ) + 1) + (384/5 - ((L:ℝ)+1)))) := by
  -- (L+1)+S0 = 384/5, so the last term is S0/(384/5) = 5·S0/384; and arg = (384/5)/(L+1).
  have hden : ((L:ℝ) + 1) + (384/5 - ((L:ℝ)+1)) = 384/5 := by ring
  have hLpos : (0:ℝ) < (L:ℝ) + 1 := by positivity
  have harg : (1:ℝ) + (384/5 - ((L:ℝ)+1)) / ((L:ℝ) + 1) = (384/5) / ((L:ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hLpos), add_mul, div_mul_cancel₀ _ (ne_of_gt hLpos), one_mul]; ring
  rw [hden, harg]
  -- Let A = (384/5)/(L+1).  Bound log A ≤ F* + [ (5·S0/384) − L/384 ] =: F* + extra.
  -- Exact: 11·(log A − F*) = log(A¹¹ · 64/621) ≤ A¹¹·64/621 − 1.  Suffices A¹¹·64/621 − 1 ≤ 11·extra.
  have hApos : (0:ℝ) < (384/5) / ((L:ℝ) + 1) := by positivity
  -- 11·log A − log(621/64) = log(A¹¹ · 64/621)
  have hlog11 : (11:ℝ) * Real.log ((384/5) / ((L:ℝ) + 1)) - Real.log (621/64)
      = Real.log (((384/5) / ((L:ℝ) + 1))^(11:ℕ) * (64/621)) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621:ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  have hfold := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < ((384/5) / ((L:ℝ) + 1))^(11:ℕ) * (64/621) by positivity)
  rw [← hlog11] at hfold
  -- Now bound the fold value − 1 by 11·extra, and F* = log(621/64)/11.
  interval_cases L
  · -- L = 61
    have hv : (((384/5:ℝ) / ((61:ℝ) + 1))^(11:ℕ) * (64/621)) - 1 ≤ 11 * ((5 * (384/5 - 62) / 384) - 61/384) := by
      norm_num
    simp only [FSTAR]
    push_cast at hfold ⊢
    nlinarith [hfold, hv]
  · -- L = 62
    have hv : (((384/5:ℝ) / ((62:ℝ) + 1))^(11:ℕ) * (64/621)) - 1 ≤ 11 * ((5 * (384/5 - 63) / 384) - 62/384) := by
      norm_num
    simp only [FSTAR]
    push_cast at hfold ⊢
    nlinarith [hfold, hv]
  · -- L = 63
    have hv : (((384/5:ℝ) / ((63:ℝ) + 1))^(11:ℕ) * (64/621)) - 1 ≤ 11 * ((5 * (384/5 - 64) / 384) - 63/384) := by
      norm_num
    simp only [FSTAR]
    push_cast at hfold ⊢
    nlinarith [hfold, hv]

/-- **BOUNDARY cell `d = 62`** (`|cs| = 61`). -/
theorem subaction_tail_d62 (cs : List Branch) (hlen : cs.length = 61) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum :=
  tail_boundary_cell cs 61 (by norm_num) hlen (by norm_num) (tail_boundary_B 61 (by norm_num) (by norm_num))

/-- **BOUNDARY cell `d = 63`** (`|cs| = 62`). -/
theorem subaction_tail_d63 (cs : List Branch) (hlen : cs.length = 62) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum :=
  tail_boundary_cell cs 62 (by norm_num) hlen (by norm_num) (tail_boundary_B 62 (by norm_num) (by norm_num))

/-- **BOUNDARY cell `d = 64`** (`|cs| = 63`). -/
theorem subaction_tail_d64 (cs : List Branch) (hlen : cs.length = 63) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum :=
  tail_boundary_cell cs 63 (by norm_num) hlen (by norm_num) (tail_boundary_B 63 (by norm_num) (by norm_num))

/-! ### The unified tail wrapper. -/

/-- **`tail_wrapper`.**  `IsSubaction ρwit` at EVERY tail hub (`|cs| ≥ 4`, degree `≥ 5`), unifying all tail
    cells over the gap-free partition of `|cs|`:
    `{4} → d5`, `{5} → d6`, `{6,7,8} → d7/d8/d9`, `[9,60] → deg4`, `{61,62,63} → d62/d63/d64`, `[64,∞) → deg5`. -/
theorem tail_wrapper (cs : List Branch) (hlen : 4 ≤ cs.length) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  rcases (show cs.length = 4 ∨ cs.length = 5 ∨ cs.length = 6 ∨ cs.length = 7 ∨ cs.length = 8
      ∨ (9 ≤ cs.length ∧ cs.length ≤ 60) ∨ cs.length = 61 ∨ cs.length = 62 ∨ cs.length = 63
      ∨ 64 ≤ cs.length by omega) with
    h | h | h | h | h | ⟨h1, h2⟩ | h | h | h | h
  · exact subaction_tail_d5 cs h
  · exact subaction_tail_d6 cs h
  · exact subaction_tail_d7 cs h
  · exact subaction_tail_d8 cs h
  · exact subaction_tail_d9 cs h
  · exact subaction_tail_deg4 cs h1 h2
  · exact subaction_tail_d62 cs h
  · exact subaction_tail_d63 cs h
  · exact subaction_tail_d64 cs h
  · exact subaction_tail_deg5 cs h

end BGSCL
end R3Cert
