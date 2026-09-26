/-
  The arithmetic bound on the FULL near-star family `N(c,k)` -- `c` cherries + `k` cherry-arms.

  `TieHarmonic.lean` proved `f(c) <= 0` for the `k = 1` slice `G(c) = N(c,1)`.  This file extends it to the
  whole 2-parameter family, formalized as the CONCRETE `Reach.Branch` gadget

      armB      = node 0 [node 0 []]          (one cherry-arm),
      nearStarB c k = node c (replicate k armB)   (root: c cherries + k cherry-arms),

  and proves the SPLIT-INVARIANCE + reduction

      cav (nearStarB c k)    = 3 / (4(c+k)+3),
      logPhi (nearStarB c k) = gVal (c+k)        (depends only on s = c+k, not the split!),

  by the exact cavity telescoping: `logPhi = k·logPhi(armB) + eroot`, with the root increment
  `eroot = log(ac·(1+z·S))` collapsing -- the `(3k+3+4c)` factors in `ac` and `(1+z·S)` cancel -- to
  `c·log(3/2) - (1+2c)·L + log(4(c+k)+3) - log(3(c+k+1))`, and `logPhi(armB) = -2L + log(3/2)`.  Summed, the
  `c`- and `k`-parts merge into `gVal(c+k)`.

  Hence, from the already-proven `gVal_nonpos`, the ENTIRE near-star family satisfies `logPhi (nearStarB c k)
  <= 0`, with equality exactly on the tie diagonal `c+k = 5` (all 6 ties `(0,5),(1,4),(2,3),(3,2),(4,1),(5,0)`,
  cavity `3/23`), via `gVal_five_zero`.

  NOTE (honest scope): this is the near-star family -- a proven instance of the tree-induction conclusion
  `logPhi B <= 0` on a real 2-parameter gadget family -- NOT the full `Phi <= 1` (arbitrary children), which
  still needs `Reach.phi_le_one_of_potential` conditional on the open crux `exists P, ValidPotential P`.
-/
import Mathlib
import R3Cert.Reach
import R3Cert.TieHarmonic

namespace R3Cert

open Real

/-- `log rhoB = Lval` (`rhoB^11 = 621/64`, `Lval = log(621/64)/11`). -/
theorem logRhoB : Real.log rhoB = Lval := by
  have h : (11 : ℝ) * Real.log rhoB = Real.log (621 / 64) := by
    rw [← rhoB_pow11, Real.log_pow]; push_cast; ring
  unfold Lval; linarith

/-- One cherry-arm `ARM = (0, [(0,[])])`. -/
def armB : Branch := Branch.node 0 [Branch.node 0 []]

/-- The near-star gadget `N(c,k)`: root with `c` cherries and `k` cherry-arm children. -/
def nearStarB (c k : ℕ) : Branch := Branch.node c (List.replicate k armB)

/-! ### Replicate telescoping (identical children) -/

theorem cavSum_replicate (b : Branch) (k : ℕ) : cavSum (List.replicate k b) = (k : ℝ) * cav b := by
  induction k with
  | zero => simp [cavSum]
  | succ n ih => rw [List.replicate_succ, cavSum, ih]; push_cast; ring

theorem logPhiSum_replicate (b : Branch) (k : ℕ) : logPhiSum (List.replicate k b) = (k : ℝ) * logPhi b := by
  induction k with
  | zero => simp [logPhiSum]
  | succ n ih => rw [List.replicate_succ, logPhiSum, ih]; push_cast; ring

/-! ### Cavities of the leaf, the arm, and the near-star -/

theorem cav_leaf : cav (Branch.node 0 []) = 1 := by
  rw [cav_eq]; simp only [cavSum, List.length_nil, Nat.cast_zero]; norm_num

theorem cavSum_leaf1 : cavSum [Branch.node 0 []] = 1 := by
  simp [cavSum, cav_leaf]

theorem cav_arm : cav armB = 1 / 3 := by
  unfold armB
  rw [cav_eq]
  simp only [List.length_cons, List.length_nil, Nat.cast_zero, cavSum_leaf1]
  norm_num

theorem nearStar_cavSum (k : ℕ) : cavSum (List.replicate k armB) = (k : ℝ) / 3 := by
  rw [cavSum_replicate, cav_arm]; ring

theorem nearStar_cav (c k : ℕ) : cav (nearStarB c k) = 3 / (4 * ((c : ℝ) + (k : ℝ)) + 3) := by
  unfold nearStarB
  rw [cav_eq, List.length_replicate, nearStar_cavSum]
  rw [show (3 : ℝ) + 3 * (k : ℝ) + 4 * (c : ℝ) + 3 * ((k : ℝ) / 3) = 4 * ((c : ℝ) + (k : ℝ)) + 3 from by ring]

/-! ### Log-amplitudes of the leaf and the arm -/

theorem logPhi_leaf : logPhi (Branch.node 0 []) = -Lval := by
  have hac00 : ac 0 0 = rhoB⁻¹ := by simp [ac]
  simp only [logPhi, logPhiSum, eroot, List.length_nil, cavSum, mul_zero, add_zero, zero_add,
    Real.log_one]
  rw [hac00, Real.log_inv, logRhoB]

theorem logPhi_arm : logPhi armB = -2 * Lval + Real.log (3 / 2) := by
  have hac01 : ac 0 1 = rhoB⁻¹ := by simp [ac]
  have hzc01 : zc 0 1 = 1 / 2 := by rw [zc]; norm_num
  unfold armB
  rw [show logPhi (Branch.node 0 [Branch.node 0 []])
        = logPhiSum [Branch.node 0 []] + eroot 0 [Branch.node 0 []] from rfl]
  rw [show logPhiSum [Branch.node 0 []] = logPhi (Branch.node 0 []) + logPhiSum [] from rfl]
  rw [logPhi_leaf, show logPhiSum ([] : List Branch) = 0 from rfl, eroot]
  simp only [List.length_cons, List.length_nil, cavSum_leaf1]
  rw [hac01, hzc01, Real.log_inv, logRhoB, show (1 : ℝ) + 1 / 2 * 1 = 3 / 2 from by norm_num]
  ring

/-! ### The root increment collapses -- the exact telescoping cancellation -/

theorem nearStar_eroot (c k : ℕ) :
    eroot c (List.replicate k armB) =
      (c : ℝ) * Real.log (3 / 2) - (1 + 2 * (c : ℝ)) * Lval
        + Real.log (4 * ((c : ℝ) + (k : ℝ)) + 3) - Real.log (3 * ((c : ℝ) + (k : ℝ) + 1)) := by
  have hp1 : (0 : ℝ) < (3 / 2 : ℝ) ^ c := by positivity
  have hp2 : (0 : ℝ) < 4 * ((c : ℝ) + (k : ℝ)) + 3 := by positivity
  have hp3 : (0 : ℝ) < rhoB ^ (1 + 2 * c) := pow_pos rhoB_pos _
  have hp4 : (0 : ℝ) < 3 * ((c : ℝ) + (k : ℝ) + 1) := by positivity
  have hd1 : (0 : ℝ) < 3 * ((k : ℝ) + 1 + (c : ℝ)) := by positivity
  have hd2 : (0 : ℝ) < 3 * ((k : ℝ) + 1 + (c : ℝ)) + (c : ℝ) := by positivity
  have hac_pos : (0 : ℝ) < ac c k := by
    rw [ac]; exact div_pos (mul_pos hp1 (by positivity)) hp3
  have hfac_pos : (0 : ℝ) < 1 + zc c k * cavSum (List.replicate k armB) := by
    rw [nearStar_cavSum, zc]; positivity
  have hprod : ac c k * (1 + zc c k * cavSum (List.replicate k armB))
      = (3 / 2 : ℝ) ^ c * (4 * ((c : ℝ) + (k : ℝ)) + 3)
          / (rhoB ^ (1 + 2 * c) * (3 * ((c : ℝ) + (k : ℝ) + 1))) := by
    rw [nearStar_cavSum]
    unfold ac zc
    field_simp
    ring
  rw [eroot, List.length_replicate, ← Real.log_mul (ne_of_gt hac_pos) (ne_of_gt hfac_pos), hprod,
    Real.log_div (ne_of_gt (mul_pos hp1 hp2)) (ne_of_gt (mul_pos hp3 hp4)),
    Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2), Real.log_mul (ne_of_gt hp3) (ne_of_gt hp4),
    Real.log_pow, Real.log_pow, logRhoB]
  push_cast; ring

/-! ### The family reduction and bound -/

/-- **Split-invariance / reduction: `logPhi (N(c,k)) = gVal (c+k)`** -- depends only on `s = c+k`. -/
theorem nearStar_logPhi (c k : ℕ) : logPhi (nearStarB c k) = gVal (c + k) := by
  unfold nearStarB
  simp only [logPhi]
  rw [logPhiSum_replicate, logPhi_arm, nearStar_eroot]
  unfold gVal
  push_cast; ring

/-- **`logPhi (N(c,k)) <= 0` for the whole near-star family**, from the proven `gVal_nonpos`. -/
theorem nearStar_nonpos (c k : ℕ) : logPhi (nearStarB c k) ≤ 0 := by
  rw [nearStar_logPhi]; exact gVal_nonpos (c + k)

/-- **The tie diagonal: `logPhi (N(c,k)) = 0` exactly when `c+k = 5`** (all 6 ties, cavity `3/23`). -/
theorem nearStar_tie (c k : ℕ) (h : c + k = 5) : logPhi (nearStarB c k) = 0 := by
  rw [nearStar_logPhi, h]; exact gVal_five_zero

/-- **The full near-star family arithmetic bound, packaged.** -/
theorem nearStar_family_le_zero (c k : ℕ) :
    logPhi (nearStarB c k) ≤ 0 ∧ (c + k = 5 → logPhi (nearStarB c k) = 0) :=
  ⟨nearStar_nonpos c k, fun h => nearStar_tie c k h⟩

end R3Cert
