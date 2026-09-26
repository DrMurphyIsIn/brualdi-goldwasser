import R3Cert.R47Parse
import R3Cert.BridgeStep4c
import R3Cert.PotentialFinal
import R3Cert.R47StepSize
import R3Cert.ExactCruxes
import R3Cert.R47Tree
import R3Cert.R47Dress
import R3Cert.R47BackboneAmp

/-!
  # Rate port, step 4: `Z ≤ rhoB^n`

  The stratum-(i) rate bound `pi(T) ≤ (4/3) rhoB^n` (`P5_SEAM_DESIGN.md`,
  `rate_bound_fixed_n.py`) is a four-step argument:
  (1) the phantom-root split `pi = A0 + A1/d`, `Z = A0 + A1/(d+1)`;
  (2) `S ≤ 1` at a leaf root; (3) `R = (1+S/d)/(1+S/(d+1)) ≤ 4/3` (leaf root);
  (4) `Z ≤ rhoB^n`.

  This file lands step (4) as a genuine assembly of already-green lemmas — no new
  mathematics — closing the Z-bound corner of `HypRatePort`:

    `Ztot (dtSub t) = Ztot (litRealize (parseB t))`   (`Ztot_dtSub_eq_lit`, green)
      `= exp (logPhi (parseB t)) · rhoB ^ (Vb (parseB t))`  (`exp_logPhi_mul_rhoB_pow`, green)
      `= exp (logPhi (parseB t)) · rhoB ^ (usize t)`   (`Vb_parseB`, green)
      `≤ 1 · rhoB ^ (usize t)`                          (`phi_le_one`: exp(logPhi) ≤ 1)

  Steps (1)-(3) are then `pi_le_rate` below: the phantom-root split falls out of
  `Ztot_single` (`Aobj (node [K]) = A0 + A1/m`, `Ztot (dtSub (node [K])) =
  A0 + A1/(2m)`), and `pi ≤ (4/3)·Z ⟺ A1 ≤ m·A0`, which follows from
  `Zopen_le_Ztot_dt` + `m ≥ 1` + `A0 > 0` — no `S ≤ 1` injection needed.  Ground
  truth: `rate_bound_fixed_n.py` (exact on every tree ≤ 9).  The rooting-choice
  seam (every ≥2-vertex tree HAS a leaf rooting) stays at `HypRatePort` assembly.
  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

open RTree

/-- **Step 4 of the rate port**: `Ztot (dtSub t) ≤ rhoB ^ (usize t)` — the
    phantom-root partition function of any tree is bounded by `rhoB^n`, assembled
    from the parse identity, the local amplitude bridge, and `phi_le_one`. -/
theorem Ztot_dtSub_le_rhoB_pow (t : UTree) : Ztot (dtSub t) ≤ rhoB ^ usize t := by
  have hb : Real.exp (logPhi (parseB t)) * rhoB ^ (usize t)
      = Ztot (litRealize (parseB t)) := by
    have h := exp_logPhi_mul_rhoB_pow (parseB t)
    rwa [Vb_parseB] at h
  rw [Ztot_dtSub_eq_lit t, ← hb]
  have hexp : Real.exp (logPhi (parseB t)) ≤ 1 := by
    calc Real.exp (logPhi (parseB t))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr (phi_le_one (parseB t))
      _ = 1 := Real.exp_zero
  have hpow : (0 : ℝ) ≤ rhoB ^ usize t := le_of_lt (pow_pos rhoB_pos _)
  calc Real.exp (logPhi (parseB t)) * rhoB ^ usize t
      ≤ 1 * rhoB ^ usize t := mul_le_mul_of_nonneg_right hexp hpow
    _ = rhoB ^ usize t := one_mul _

/-- A single-child node's total partition function:
    `Ztot (node [(w, c)]) = Ztot c + w · Zopen c`. -/
theorem Ztot_single (w : ℝ) (c : RTree) :
    Ztot (RTree.node [(w, c)]) = Ztot c + w * Zopen c := by
  show Popen [(w, c)] + Matched [(w, c)] = Ztot c + w * Zopen c
  rw [Popen_cons, Matched_cons]
  simp only [Popen, Matched]
  ring

/-- **The full rate bound** `pi(T) ≤ (4/3) rhoB^n` for a leaf rooting `node [K]`.

    The phantom-root split falls out of `Ztot_single`:
    `Aobj (node [K]) = A0 + A1/m` and `Ztot (dtSub (node [K])) = A0 + A1/(2m)`,
    with `A0 = Ztot (dtSub K)`, `A1 = Zopen (dtSub K)`, `m = udeg K`.  Then
    `pi ≤ (4/3)·Z ⟺ A1 ≤ m·A0`, which follows from `Zopen_le_Ztot_dt` (`A1 ≤ A0`),
    `m ≥ 1` and `A0 > 0` — no S≤1 injection needed.  Chaining step (4)
    (`Ztot_dtSub_le_rhoB_pow` on `node [K]`) closes it.  The rooting choice (that
    every tree with ≥2 vertices HAS a leaf rooting) stays at assembly
    (`HypRatePort` quantifies over it). -/
theorem pi_le_rate (K : UTree) :
    Aobj (UTree.node [K]) ≤ 4 / 3 * rhoB ^ usize (UTree.node [K]) := by
  have hA0pos : 0 < Ztot (dtSub K) := Ztot_dt_pos K
  have hA1pos : 0 < Zopen (dtSub K) := Zopen_dt_pos K
  have hle : Zopen (dtSub K) ≤ Ztot (dtSub K) := Zopen_le_Ztot_dt K
  have hm1 : (1 : ℝ) ≤ (udeg K : ℝ) := by
    have h := childCount_dtSub_succ K
    have hk : 1 ≤ udeg K := by omega
    exact_mod_cast hk
  have hmpos : (0 : ℝ) < (udeg K : ℝ) := by linarith
  have hm0 : (udeg K : ℝ) ≠ 0 := ne_of_gt hmpos
  -- the two objects, unfolded via Ztot_single
  have haobj : Aobj (UTree.node [K])
      = Ztot (dtSub K) + (1 / (udeg K : ℝ)) * Zopen (dtSub K) := by
    rw [Aobj, dtRealize_node, dtChildren_cons, dtChildren_nil, Ztot_single]
    simp [List.length_cons, List.length_nil]
  have hZobj : Ztot (dtSub (UTree.node [K]))
      = Ztot (dtSub K) + (1 / (2 * (udeg K : ℝ))) * Zopen (dtSub K) := by
    rw [dtSub_node, dtChildren_cons, dtChildren_nil, Ztot_single]
    simp [List.length_cons, List.length_nil]
  -- key algebra: A1 ≤ m·A0
  have hkeyalg : Zopen (dtSub K) ≤ (udeg K : ℝ) * Ztot (dtSub K) := by
    nlinarith [hle, hm1, hA0pos,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (udeg K : ℝ) - 1) (le_of_lt hA0pos)]
  -- pi ≤ (4/3)·Z
  have hkey : Aobj (UTree.node [K]) ≤ 4 / 3 * Ztot (dtSub (UTree.node [K])) := by
    rw [haobj, hZobj, ← sub_nonneg]
    have hdiff :
        4 / 3 * (Ztot (dtSub K) + 1 / (2 * (udeg K : ℝ)) * Zopen (dtSub K))
          - (Ztot (dtSub K) + 1 / (udeg K : ℝ) * Zopen (dtSub K))
        = 1 / 3 * (Ztot (dtSub K) - 1 / (udeg K : ℝ) * Zopen (dtSub K)) := by
      field_simp
      ring
    rw [hdiff]
    have hpos : 0 ≤ Ztot (dtSub K) - 1 / (udeg K : ℝ) * Zopen (dtSub K) := by
      rw [sub_nonneg, div_mul_eq_mul_div, one_mul, div_le_iff₀ hmpos]
      linarith [hkeyalg, mul_comm (Ztot (dtSub K)) ((udeg K : ℝ))]
    exact mul_nonneg (by norm_num) hpos
  -- chain step (4)
  have hstep4 : Ztot (dtSub (UTree.node [K])) ≤ rhoB ^ usize (UTree.node [K]) :=
    Ztot_dtSub_le_rhoB_pow _
  calc Aobj (UTree.node [K])
      ≤ 4 / 3 * Ztot (dtSub (UTree.node [K])) := hkey
    _ ≤ 4 / 3 * rhoB ^ usize (UTree.node [K]) :=
        mul_le_mul_of_nonneg_left hstep4 (by norm_num)

end Step3
end R3Cert
