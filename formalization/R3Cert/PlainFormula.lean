/-
  THE PLAIN-TREE CLOSED FORM -- the per-node cavity and root increment for cherry-free nodes.

  After `Plainify.lean` reduces `Phi <= 1` to plain (cherry-free, `c = 0`) trees, the per-node data
  collapses to a clean parameter-free form (`plain_tree_reduction.py`):

      cav (node 0 ch) = 1 / (k + 1 + S),
      eroot 0 ch      = -L + log(1 + S/(k+1)) = -L - log(k+1) - log(cav (node 0 ch)),

  where `k = ch.length` (number of children), `S = cavSum ch` (sum of child cavities), `L = log rhoB`.
  So for a plain tree, `logPhi = sum_v [ -L + log(1 + S_v/(k_v+1)) ]`.  This file machine-checks the
  per-node identities (all no-sorry); they are the clean building blocks of the plain-tree conjecture.
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar

namespace R3Cert

open Real

/-- **Plain node cavity:** `cav (node 0 ch) = 1 / (k + 1 + S)`, `k = ch.length`, `S = cavSum ch`. -/
theorem cav_plain_node (ch : List Branch) :
    cav (Branch.node 0 ch) = 1 / ((ch.length : ℝ) + 1 + cavSum ch) := by
  have hS : (0 : ℝ) ≤ cavSum ch := cavSum_nonneg ch
  rw [cav_eq, div_eq_div_iff (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
  push_cast
  ring

/-- `ac 0 k = rhoB⁻¹` for any child count `k` (the `(3/2)^0` and `(1 + 0/·)` factors are trivial). -/
theorem ac_zero (k : ℕ) : ac 0 k = rhoB⁻¹ := by simp [ac]

/-- `zc 0 k = 1 / (k + 1)`. -/
theorem zc_zero (k : ℕ) : zc 0 k = 1 / ((k : ℝ) + 1) := by
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [zc, div_eq_div_iff (ne_of_gt (by positivity)) (ne_of_gt h1)]
  push_cast
  ring

/-- **Plain root increment (log form):** `eroot 0 ch = -L + log(1 + S/(k+1))`. -/
theorem eroot_plain_node (ch : List Branch) :
    eroot 0 ch = -Lval + Real.log (1 + cavSum ch / ((ch.length : ℝ) + 1)) := by
  rw [eroot, ac_zero, zc_zero, Real.log_inv, logRhoB, div_mul_eq_mul_div, one_mul]

/-- **Plain root increment (closed form):** `eroot 0 ch = -L - log(k+1) - log(cav (node 0 ch))`. -/
theorem eroot_plain_node' (ch : List Branch) :
    eroot 0 ch = -Lval - Real.log ((ch.length : ℝ) + 1) - Real.log (cav (Branch.node 0 ch)) := by
  have hS : (0 : ℝ) ≤ cavSum ch := cavSum_nonneg ch
  have h1 : (0 : ℝ) < (ch.length : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < (ch.length : ℝ) + 1 + cavSum ch := by positivity
  rw [eroot_plain_node, cav_plain_node,
    show (1 : ℝ) + cavSum ch / ((ch.length : ℝ) + 1)
        = ((ch.length : ℝ) + 1 + cavSum ch) / ((ch.length : ℝ) + 1) from by field_simp,
    Real.log_div (ne_of_gt hx) (ne_of_gt h1),
    Real.log_div (one_ne_zero) (ne_of_gt hx), Real.log_one]
  ring

end R3Cert
