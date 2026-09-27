/-
  R4-R7 campaign, PHASE 5c (part 2): the head-merge identities.

  THE TWO IDENTITIES (validated exactly in rationals, 60/60 states, all 36 cells,
  before any Lean here -- P5_SEAM_DESIGN.md):

      Aobj (before-state) = Kblock * (beforeD at the state's data)
      Aobj (after-state)  = Kblock * (afterD  at the state's data)

  `Kblock = armProd armsA * armProd armsB * prod(tail Ztots)` (the common positive
  block), structural degrees `da = |armsA| + 1`, `db = |armsB| + |tail| + 1`,
  `sigma_Q = sigmaArms armsA`, `sigma_r = sigmaArms others + qSum tail`.

  Engine: `Ztot_hubNode_dressed` (part 1) at the root and at the donor, `Zopen_hubNode`,
  and the exact cancellation `F z = (3/2)^c / D` (`Fw_mul_zw`).  The after side's
  `Wt^k = (76/115)^k` emerges from the arm-Ztot ratio `(513/80)/(621/64)`.

  With the CI-green 36-cell table (P4) and the box bounds (P5b) these pin the
  head-merge comparison; the per-step monotonicity assembly is P5d.  Nothing here
  asserts per-step monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Head

namespace R3Cert
namespace Step3

open RTree

/-! ### Blocks and helpers -/

/-- The Ztot product of an arm-load list. -/
noncomputable def armProd (arms : List ℕ) : ℝ :=
  (arms.map fun j => Ztot (dtSub (armU j))).prod

/-- The common positive block of the head-merge comparison. -/
noncomputable def Kblock (armsA armsB : List ℕ) (rest : List Hub) : ℝ :=
  armProd armsA * armProd armsB * ((tailU rest).map fun K => Ztot (dtSub K)).prod

theorem armProd_double (arms : List ℕ) :
    ((arms.map armU).map fun K => Ztot (dtSub K)).prod = armProd arms := by
  rw [List.map_map]
  rfl

theorem armProd_append (l1 l2 : List ℕ) :
    armProd (l1 ++ l2) = armProd l1 * armProd l2 := by
  simp [armProd]

theorem armProd_replicate (n j : ℕ) :
    armProd (List.replicate n j) = Ztot (dtSub (armU j)) ^ n := by
  simp [armProd, List.map_replicate, List.prod_replicate]

theorem armProd_perm {l1 l2 : List ℕ} (h : l1.Perm l2) : armProd l1 = armProd l2 :=
  (h.map _).prod_eq

theorem armProd_singleton (j : ℕ) : armProd [j] = Ztot (dtSub (armU j)) := by
  simp [armProd]

theorem qSum_singleton (K : UTree) :
    qSum [K] = Zopen (dtSub K) / Ztot (dtSub K) / (udeg K : ℝ) := by
  simp [qSum]

/-- Numeric arm Ztots: `F(1,4) = 513/80`, `F(1,5) = 621/64`. -/
theorem Ztot_armU_four : Ztot (dtSub (armU 4)) = 513 / 80 := by
  rw [Ztot_dtSub_armU]; norm_num

theorem Ztot_armU_five : Ztot (dtSub (armU 5)) = 621 / 64 := by
  rw [Ztot_dtSub_armU]; norm_num

/-- The two-hub assembly as a PURE SCALAR identity (all structure as plain real
    variables -- no casts or defs for the algebra to mangle). -/
theorem twohub_scalar (PA PB Pr Fa za Fb zb SA SB D X32 : ℝ)
    (hD : D ≠ 0) (hZt : PB * Pr * (Fb * (1 + zb * SB)) ≠ 0)
    (h32 : X32 = Fb * zb * D) :
    PA * (PB * Pr * (Fb * (1 + zb * SB)))
      * (Fa * (1 + za * (SA + PB * X32 * Pr / (PB * Pr * (Fb * (1 + zb * SB))) / D)))
    = PA * PB * Pr
        * (Fa * Fb * ((1 + za * SA) * (1 + zb * SB) + za * zb)) := by
  subst h32
  have hZt' : PB * Pr * Fb + PB * Pr * Fb * zb * SB ≠ 0 := by
    rw [show PB * Pr * Fb + PB * Pr * Fb * zb * SB
        = PB * Pr * (Fb * (1 + zb * SB)) from by ring]
    exact hZt
  field_simp
  linear_combination (PA * PB * Pr * Fb * zb * Fa * za) * mul_inv_cancel₀ hZt'

/-! ### The BEFORE identity (raw two-hub form) -/

/-! ### The BEFORE identity (certificate-slot form) -/

/-! ### The AFTER identity -/

end Step3
end R3Cert
