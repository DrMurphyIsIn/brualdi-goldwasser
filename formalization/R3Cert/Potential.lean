/-
  The EXPLICIT discharging potential for the plain-tree bound `logPhi <= 0`.

  From proof_via_explicit_potential.py: `phi(y) = 0.22 * (y - T0)_+`, `T0 = rhoB - 1`, in the FOLDED
  super-solution.  Because only ARMS have cavity `1/3` and only LEAVES have cavity `1` (no structural node
  shares those -- for a plain node `cav = 1/(1+nch+S) = 1/3` forces the arm, `= 1` forces the leaf), the
  folded charge is absorbed into the potential VALUES: set `Pval(1/3) = |omega|` and `Pval(1) = Lval`, and
  `Pval(y) = 0.22*(y-T0)_+` elsewhere.  With these values the RAW per-node super-solution

      eroot 0 ch <= (Σ_{b∈ch} Pval(cav b)) - Pval(cav (node 0 ch))     (ValidPotential-style, plain nodes)

  is EQUIVALENT to the folded super-solution (verified numerically, 0 violation over plain trees N<=16),
  with EQUALITY at arm and leaf nodes (`eroot(arm)+|omega| = Lval`, `eroot(leaf)+Lval = 0`).  This file
  defines `Pval` and proves `Pval >= 0` and the two boundary values; the per-node super-solution and the
  plain telescoping are subsequent increments.

  Genuine proofs (no `sorry`, no `Prop := True`).
-/
import Mathlib
import R3Cert.ExactCruxes
import R3Cert.Sweep

namespace R3Cert

open Real

/-- `Lval > 0`. -/
theorem Lval_pos : 0 < Lval := by
  unfold Lval
  have := Real.log_pos (by norm_num : (1 : ℝ) < 621 / 64); linarith

/-- `T0 = rhoB - 1` (the potential threshold; `log(1+T0) = Lval`). -/
noncomputable def T0 : ℝ := rhoB - 1

/-- The explicit RAW potential: `|omega|` at the arm cavity `1/3`, `Lval` at the leaf cavity `1`, and
    `0.22*(y - T0)_+ = (11/50)*max 0 (y - T0)` on structural cavities. -/
noncomputable def Pval (y : ℝ) : ℝ :=
  if y = 1 / 3 then -omegaVal
  else if y = 1 then Lval
  else (11 / 50) * max 0 (y - T0)

/-- `Pval (1/3) = |omega|`  (the arm-unit value). -/
theorem Pval_third : Pval (1 / 3) = -omegaVal := by
  unfold Pval; rw [if_pos rfl]

/-- `Pval 1 = Lval`  (the leaf value). -/
theorem Pval_one : Pval 1 = Lval := by
  unfold Pval; rw [if_neg (by norm_num : (1 : ℝ) ≠ 1 / 3), if_pos rfl]

/-- On structural cavities (`y ≠ 1/3`, `y ≠ 1`), `Pval y = 0.22*(y - T0)_+`. -/
theorem Pval_struct (y : ℝ) (h3 : y ≠ 1 / 3) (h1 : y ≠ 1) :
    Pval y = (11 / 50) * max 0 (y - T0) := by
  unfold Pval; rw [if_neg h3, if_neg h1]

/-- **`Pval >= 0` everywhere** (`-omega > 0`, `Lval > 0`, `max 0 (·) >= 0`). -/
theorem Pval_nonneg (y : ℝ) : 0 ≤ Pval y := by
  unfold Pval
  split_ifs with h1 h2
  · linarith [omegaVal_neg]
  · exact Lval_pos.le
  · exact mul_nonneg (by norm_num) (le_max_left 0 _)

end R3Cert
