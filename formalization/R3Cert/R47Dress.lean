/-
  R4-R7 campaign, PHASE 5a: the dressing layer -- P2a raw hub forms speak the certified
  (F, z) language.

  Per P5_SEAM_DESIGN.md (S1/S2/S4):
  * `fold_FZ`      -- the EXACT per-vertex folding: the raw cherry block
    `(3/2)^c (1 + c/(3D) + T/D)` (D = d + c the full degree) equals
    `F(d,c) (1 + z(d,c) T')` with the dressed activity `z(d,c) = 3/(3d+4c)` -- the
    identity `3D + c = 3d + 4c` behind the loaded-tree model, connecting the P2a
    backbone recursion to the certificate table's `Fw`/`zw`;
  * `q_dressed_armU` -- a load-j arm's dressed cavity contribution `Q/D` is EXACTLY
    `zw 1 j` (so load-5 arms give 3/23, load-4 arms 3/19: the constants wired into
    `beforeD`/`afterD`); with the numeric cap facts `zw_one_four_le`/`zw_one_five_le`;
  * `Zopen_le_Ztot_dt`, `q_dressed_le_of_udeg` -- the generic subtree bounds: cavity
    ratio at most 1, and any neighbour of full degree >= 6 meets the 3/16 cap (the
    backbone-tail bound; note the crude 1/D bound FAILS for load-4 arms at D = 5,
    which is why `q_dressed_armU`'s exact value is load-bearing).

  Nothing here asserts per-step monotonicity; this is the S1/S2/S4 toolkit for the
  P5c head-merge identity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Cert

namespace R3Cert
namespace Step3

open RTree

/-! ### Generic subtree cavity bounds -/

/-- The open partition function never exceeds the total (Matched >= 0). -/
theorem Zopen_le_Ztot_dt (K : UTree) : Zopen (dtSub K) ≤ Ztot (dtSub K) := by
  cases K with
  | node cs =>
    rw [dtSub_node, Zopen, Ztot]
    have h := Matched_dtCh_nonneg (cs.length + 1) cs
    linarith

/-- Any neighbour of full degree at least 6 meets the 3/16 environment cap. -/
theorem q_dressed_le_of_udeg (K : UTree) (h6 : 6 ≤ udeg K) :
    Zopen (dtSub K) / Ztot (dtSub K) / (udeg K : ℝ) ≤ 3 / 16 := by
  have hD : (6 : ℝ) ≤ (udeg K : ℝ) := by exact_mod_cast h6
  have hZt : 0 < Ztot (dtSub K) := Ztot_dt_pos K
  have hle := Zopen_le_Ztot_dt K
  rw [div_div, div_le_iff₀ (mul_pos hZt (by linarith : (0 : ℝ) < (udeg K : ℝ)))]
  nlinarith [mul_nonneg hZt.le (by linarith : (0 : ℝ) ≤ (udeg K : ℝ) - 6)]

/-! ### Arm dressed activities are exact -/

/-- **A load-j arm's dressed cavity contribution is exactly the loaded activity**:
    `Q/D = 3/(4j+3) = zw 1 j`. -/
theorem q_dressed_armU (j : ℕ) :
    Zopen (dtSub (armU j)) / Ztot (dtSub (armU j)) / (udeg (armU j) : ℝ) = zw 1 j := by
  rw [Q_armU, udeg_armU, zw]
  push_cast
  have h1 : (4 * (j : ℝ) + 3) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (3 * 1 + 4 * (j : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

theorem zw_one_four : zw 1 4 = 3 / 19 := by norm_num [zw]

theorem zw_one_four_le : zw 1 4 ≤ 3 / 16 := by norm_num [zw]

theorem zw_one_five_le : zw 1 5 ≤ 3 / 16 := by norm_num [zw]

/-! ### The per-vertex folding identity -/

/-- **The dressing lemma**: the raw cherry-block form of a hub of structural degree `d`
    and load `c` (full degree `D = d + c`) folds exactly into the certified
    `F(d,c) (1 + z(d,c) T)` form -- via `3D + c = 3d + 4c`.  `T` is the dressed
    neighbour sum `Σ Qᵢ/Dᵢ`. -/
theorem fold_FZ (d c : ℕ) (T : ℝ) (hd : 0 < d) :
    (3 / 2 : ℝ) ^ c * (1 + (c : ℝ) / (3 * ((d : ℝ) + (c : ℝ)))
        + 1 / ((d : ℝ) + (c : ℝ)) * T)
      = Fw (d : ℝ) c * (1 + zw (d : ℝ) c * T) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  cases c with
  | zero =>
    rw [Fw_zero]
    simp only [zw]
    push_cast
    have hD : ((d : ℝ) + 0) ≠ 0 := by positivity
    have hz : (3 * (d : ℝ) + 4 * 0) ≠ 0 := by positivity
    field_simp
    ring
  | succ n =>
    simp only [Fw, zw, Nat.add_sub_cancel]
    push_cast
    have hD : ((d : ℝ) + ((n : ℝ) + 1)) ≠ 0 := by positivity
    have hD2 : (2 * ((d : ℝ) + ((n : ℝ) + 1))) ≠ 0 := by positivity
    have hz : (3 * (d : ℝ) + 4 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    field_simp
    ring

end Step3
end R3Cert
