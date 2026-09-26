/-
  The near-star (all-arm-children) super-solution `gVal k + Pval (3/(4k+3)) <= 0` for all `k`, and the
  `ValidPotentialPlain`-form super-solution at a near-star node `node 0 (replicate k armB)`.

  k=0: leaf (`gVal 0 = -Lval`, `Pval 1 = Lval`).  k>=3: `gVal_add_Pval_ge3` (Pval=0).
  k=1,2: `gVal_k_le` + `log x <= x-1` reduce to polynomial-in-rhoB inequalities on `(1229/1000, 123/100)`,
  made linear in the power atoms via explicit lower bounds `rhoB^n >= (1229/1000)^n`.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar
import R3Cert.Sweep
import R3Cert.JTail
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialGVal

namespace R3Cert

open Real

theorem gVal_zero_eq : gVal 0 = -Lval := by unfold gVal; norm_num

theorem Pval_37 : Pval (3 / 7) = (11 / 50) * (3 / 7 - T0) := by
  rw [Pval_struct (3 / 7) (by norm_num) (by norm_num),
      max_eq_right (show (0 : ℝ) ≤ 3 / 7 - T0 by unfold T0; linarith [rhoB_lt_four_thirds])]

theorem Pval_311 : Pval (3 / 11) = (11 / 50) * (3 / 11 - T0) := by
  rw [Pval_struct (3 / 11) (by norm_num) (by norm_num),
      max_eq_right (show (0 : ℝ) ≤ 3 / 11 - T0 by unfold T0; linarith [rhoB_lt_123])]

/-- Near-star `k = 1`. -/
theorem gVal_add_Pval_one : gVal 1 + Pval (3 / 7) ≤ 0 := by
  rw [Pval_37]; unfold T0
  have hr3 : (0 : ℝ) < rhoB ^ 3 := pow_pos rhoB_pos 3
  have hb3 : ((1229 : ℝ) / 1000) ^ 3 ≤ rhoB ^ 3 := by gcongr; exact rhoB_gt_1229.le
  have hb4 : ((1229 : ℝ) / 1000) ^ 4 ≤ rhoB ^ 4 := by gcongr; exact rhoB_gt_1229.le
  have hpoly : (7 / 4 : ℝ) - rhoB ^ 3 + (11 / 50) * (10 / 7 - rhoB) * rhoB ^ 3 ≤ 0 := by
    nlinarith [hb3, hb4]
  have hg3 : gVal 1 * rhoB ^ 3 ≤ 7 / 4 - rhoB ^ 3 := by
    have h := mul_le_mul_of_nonneg_right gVal_one_le hr3.le
    rwa [sub_mul, div_mul_cancel₀ _ (ne_of_gt hr3), one_mul] at h
  nlinarith [hg3, hpoly, hr3, rhoB_pos]

/-- Near-star `k = 2`. -/
theorem gVal_add_Pval_two : gVal 2 + Pval (3 / 11) ≤ 0 := by
  rw [Pval_311]; unfold T0
  have hr5 : (0 : ℝ) < rhoB ^ 5 := pow_pos rhoB_pos 5
  have hb5 : ((1229 : ℝ) / 1000) ^ 5 ≤ rhoB ^ 5 := by gcongr; exact rhoB_gt_1229.le
  have hb6 : ((1229 : ℝ) / 1000) ^ 6 ≤ rhoB ^ 6 := by gcongr; exact rhoB_gt_1229.le
  have hpoly : (11 / 4 : ℝ) - rhoB ^ 5 + (11 / 50) * (14 / 11 - rhoB) * rhoB ^ 5 ≤ 0 := by
    nlinarith [hb5, hb6]
  have hg5 : gVal 2 * rhoB ^ 5 ≤ 11 / 4 - rhoB ^ 5 := by
    have h := mul_le_mul_of_nonneg_right gVal_two_le hr5.le
    rwa [sub_mul, div_mul_cancel₀ _ (ne_of_gt hr5), one_mul] at h
  nlinarith [hg5, hpoly, hr5, rhoB_pos]

/-- **The near-star super-solution for all `k`:** `gVal k + Pval (3/(4k+3)) <= 0`. -/
theorem nearStar_super (k : ℕ) : gVal k + Pval (3 / (4 * (k : ℝ) + 3)) ≤ 0 := by
  rcases k with _ | _ | _ | n
  · rw [gVal_zero_eq, show (3 : ℝ) / (4 * ((0 : ℕ) : ℝ) + 3) = 1 by norm_num, Pval_one]; linarith
  · rw [show (3 : ℝ) / (4 * ((1 : ℕ) : ℝ) + 3) = 3 / 7 by norm_num]; exact gVal_add_Pval_one
  · rw [show (3 : ℝ) / (4 * ((2 : ℕ) : ℝ) + 3) = 3 / 11 by norm_num]; exact gVal_add_Pval_two
  · exact gVal_add_Pval_ge3 (by omega)

/-- **Super-solution at a near-star node** `node 0 (replicate k armB)` (`ValidPotentialPlain` form). -/
theorem superSol_nearStar (k : ℕ) :
    eroot 0 (List.replicate k armB) ≤
      ((List.replicate k armB).map (fun b => Pval (cav b))).sum
        - Pval (cav (Branch.node 0 (List.replicate k armB))) := by
  -- RHS map: each armB has cav 1/3, Pval = -omegaVal
  have hmap : (List.replicate k armB).map (fun b => Pval (cav b)) = List.replicate k (-omegaVal) := by
    rw [List.map_replicate, cav_arm, Pval_third]
  -- cav node = 3/(4k+3)
  have hcav : cav (Branch.node 0 (List.replicate k armB)) = 3 / (4 * (k : ℝ) + 3) := by
    have h := nearStar_cav 0 k; unfold nearStarB at h
    rw [h]; push_cast; ring
  -- eroot = gVal k - k*omegaVal
  have heroot : eroot 0 (List.replicate k armB) = gVal k - (k : ℝ) * omegaVal := by
    have h := nearStar_logPhi 0 k
    unfold nearStarB at h
    rw [logPhi, logPhiSum_replicate, logPhi_arm] at h
    have ho : (-2 * Lval + Real.log (3 / 2)) = omegaVal := by unfold omegaVal; ring
    rw [ho, Nat.zero_add] at h
    linarith [h]
  rw [hmap, List.sum_replicate, nsmul_eq_mul, hcav, heroot]
  nlinarith [nearStar_super k]

end R3Cert
