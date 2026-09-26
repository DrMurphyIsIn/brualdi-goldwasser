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

/-- The exact cancellation `F(d,c) z(d,c) = (3/2)^c / (d+c)`. -/
theorem Fw_mul_zw (d c : ℕ) (hd : 0 < d) :
    Fw (d : ℝ) c * zw (d : ℝ) c = (3 / 2) ^ c / ((d : ℝ) + (c : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  cases c with
  | zero =>
    rw [Fw_zero]
    simp only [zw]
    push_cast
    have h1 : (3 * (d : ℝ) + 4 * 0) ≠ 0 := by positivity
    have h2 : ((d : ℝ) + 0) ≠ 0 := by positivity
    field_simp
    ring
  | succ n =>
    simp only [Fw, zw, Nat.add_sub_cancel]
    push_cast
    have h1 : ((d : ℝ) + ((n : ℝ) + 1)) ≠ 0 := by positivity
    have h2 : (2 * ((d : ℝ) + ((n : ℝ) + 1))) ≠ 0 := by positivity
    have h3 : (3 * (d : ℝ) + 4 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    field_simp
    ring

/-- The open partition function of a hub node: the pure child-block product. -/
theorem Zopen_hubNode (d : ℕ) (arms : List ℕ) (c : ℕ) (ts : List UTree) :
    Zopen (RTree.node (dtChildren d (arms.map armU ++ List.replicate c cherryU ++ ts)))
      = armProd arms * (3 / 2) ^ c * (ts.map fun K => Ztot (dtSub K)).prod := by
  rw [Zopen, dtChildren_append, dtChildren_append, Popen_append, Popen_append,
    Popen_dtChildren, Popen_dtChildren, Popen_dtChildren, armProd_double]
  have hcherry : ((List.replicate c cherryU).map fun K => Ztot (dtSub K)).prod
      = (3 / 2) ^ c := by
    rw [List.map_replicate, Ztot_dtSub_cherryU, List.prod_replicate]
  rw [hcherry]

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

/-- **The head two-hub identity, before side** (raw form: full donor arm sum, no
    split).  With `da = |armsA| + 1`, `db = |armsB| + |tail| + 1`:
    `Aobj = Kblock * Fa Fb ((1 + za sQ)(1 + zb sB) + za zb)`. -/
theorem Aobj_head_before_raw (armsA : List ℕ) (cA : ℕ) (armsB : List ℕ) (cb : ℕ)
    (rest : List Hub) :
    Aobj (backboneU ((armsA, cA) :: (armsB, cb) :: rest))
      = Kblock armsA armsB rest
        * (Fw ((armsA.length + 1 : ℕ) : ℝ) cA
            * Fw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb
            * ((1 + zw ((armsA.length + 1 : ℕ) : ℝ) cA * sigmaArms armsA)
                * (1 + zw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb
                    * (sigmaArms armsB + qSum (tailU rest)))
              + zw ((armsA.length + 1 : ℕ) : ℝ) cA
                * zw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb)) := by
  set B : UTree := backboneU ((armsB, cb) :: rest) with hB
  have hAobj : Aobj (backboneU ((armsA, cA) :: (armsB, cb) :: rest))
      = Ztot (RTree.node (dtChildren ((armsA.length + 1) + cA)
          (armsA.map armU ++ List.replicate cA cherryU ++ [B]))) := by
    show Ztot (dtRealize (backboneU ((armsA, cA) :: (armsB, cb) :: rest))) = _
    rw [backboneU_eq, dtRealize_node]
    have htail : tailU ((armsB, cb) :: rest) = [B] := tailU_cons _ _
    rw [htail]
    have hlen : (armsA.map armU ++ List.replicate cA cherryU ++ [B]).length
        = (armsA.length + 1) + cA := by
      simp [List.length_append]
      omega
    rw [hlen]
  have hBsub : dtSub B
      = RTree.node (dtChildren ((armsB.length + (tailU rest).length + 1) + cb)
          (armsB.map armU ++ List.replicate cb cherryU ++ tailU rest)) := by
    rw [hB, backboneU_eq, dtSub_node]
    have hlen : (armsB.map armU ++ List.replicate cb cherryU ++ tailU rest).length + 1
        = (armsB.length + (tailU rest).length + 1) + cb := by
      simp [List.length_append]
      omega
    rw [hlen]
  have hudegB : (udeg B : ℝ)
      = ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) + (cb : ℝ) := by
    rw [hB, udeg_backbone]
    push_cast
    ring
  have hZtB : Ztot (dtSub B)
      = (armProd armsB * ((tailU rest).map fun K => Ztot (dtSub K)).prod)
        * (Fw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb
            * (1 + zw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb
                * (sigmaArms armsB + qSum (tailU rest)))) := by
    rw [hBsub, Ztot_hubNode_dressed _ cb armsB (tailU rest) (by omega)
      (fun K _ => Ztot_dt_pos K), armProd_double]
  have hZoB : Zopen (dtSub B)
      = armProd armsB * (3 / 2) ^ cb
        * ((tailU rest).map fun K => Ztot (dtSub K)).prod := by
    rw [hBsub, Zopen_hubNode]
  rw [hAobj, Ztot_hubNode_dressed (armsA.length + 1) cA armsA [B] (by omega)
    (fun K _ => Ztot_dt_pos K), armProd_double, qSum_singleton]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hZtB, hZoB, hudegB]
  have hzt : (0 : ℝ) < Ztot (dtSub B) := Ztot_dt_pos B
  rw [hZtB] at hzt
  have hDB : ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) + (cb : ℝ) ≠ 0 := by
    positivity
  have hFZ := Fw_mul_zw (armsB.length + (tailU rest).length + 1) cb (by omega)
  have h32 : ((3 : ℝ) / 2) ^ cb
      = Fw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb
        * zw ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cb
        * (((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) + (cb : ℝ)) := by
    rw [hFZ]
    field_simp
  rw [Kblock]
  exact twohub_scalar _ _ _ _ _ _ _ _ _ _ _ hDB hzt.ne' h32

/-! ### The BEFORE identity (certificate-slot form) -/

/-- The before identity in `beforeD` form: the donor split `armsB ~ k fives ++ others`
    feeds the certificate slot `k * (3/23) + sr`. -/
theorem Aobj_head_before (armsA : List ℕ) (cA : ℕ) (armsB others : List ℕ) (cb k : ℕ)
    (rest : List Hub) (hsplit : armsB.Perm (List.replicate k 5 ++ others)) :
    Aobj (backboneU ((armsA, cA) :: (armsB, cb) :: rest))
      = Kblock armsA armsB rest
        * beforeD ((armsA.length + 1 : ℕ) : ℝ)
            ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cA cb k
            (sigmaArms armsA) (sigmaArms others + qSum (tailU rest)) := by
  rw [Aobj_head_before_raw armsA cA armsB cb rest]
  have hsum : sigmaArms armsB = (k : ℝ) * (3 / 23) + sigmaArms others := by
    rw [sigmaArms_perm hsplit, sigmaArms_append, sigmaArms_replicate, zw_one_five]
  rw [hsum, beforeD]
  ring

/-! ### The AFTER identity -/

/-- **The head identity, after side.**  The merged state realizes to exactly the
    afterD form times the SAME common block (donor arms in canonical split order):
    the k borrows drop to load 4 and `Wt^k` emerges from `(513/80)/(621/64) = 76/115`;
    the donor lands as the load-5 arm (`+ 3/23` in the slot). -/
theorem Aobj_head_after (armsA : List ℕ) (cA : ℕ) (others : List ℕ) (k : ℕ)
    (rest : List Hub) :
    Aobj (backboneU ((armsA ++ List.replicate k 4 ++ others ++ [5], cA) :: rest))
      = Kblock armsA (List.replicate k 5 ++ others) rest
        * afterD ((armsA.length + 1 : ℕ) : ℝ)
            ((k + others.length + (tailU rest).length + 1 : ℕ) : ℝ) cA k
            (sigmaArms armsA) (sigmaArms others + qSum (tailU rest)) := by
  set M : List ℕ := armsA ++ List.replicate k 4 ++ others ++ [5] with hM
  have hAobj : Aobj (backboneU ((M, cA) :: rest))
      = Ztot (RTree.node (dtChildren ((M.length + (tailU rest).length) + cA)
          (M.map armU ++ List.replicate cA cherryU ++ tailU rest))) := by
    show Ztot (dtRealize (backboneU ((M, cA) :: rest))) = _
    rw [backboneU_eq, dtRealize_node]
    have hlen : (M.map armU ++ List.replicate cA cherryU ++ tailU rest).length
        = (M.length + (tailU rest).length) + cA := by
      simp [List.length_append]
      omega
    rw [hlen]
  have hMpos : 0 < M.length + (tailU rest).length := by
    rw [hM]
    simp [List.length_append]
  rw [hAobj, Ztot_hubNode_dressed (M.length + (tailU rest).length) cA M (tailU rest)
    hMpos (fun K _ => Ztot_dt_pos K), armProd_double]
  -- split the merged product (the Wt^k mechanism) and the merged sum
  have hMprod : armProd M
      = armProd armsA
        * ((76 / 115 : ℝ) ^ k * (621 / 64 : ℝ) ^ k * armProd others * (621 / 64)) := by
    rw [hM, armProd_append, armProd_append, armProd_append, armProd_replicate,
      armProd_singleton, Ztot_armU_four, Ztot_armU_five,
      show ((513 : ℝ) / 80) ^ k = (76 / 115 : ℝ) ^ k * (621 / 64 : ℝ) ^ k from by
        rw [← mul_pow]; norm_num]
    ring
  have hMsum : sigmaArms M
      = sigmaArms armsA + ((k : ℝ) * (3 / 19) + (sigmaArms others + 3 / 23)) := by
    have h5 : sigmaArms [5] = 3 / 23 := by
      simp [sigmaArms, zw_one_five]
    rw [hM, sigmaArms_append, sigmaArms_append, sigmaArms_append, sigmaArms_replicate,
      zw_one_four, h5]
    ring
  -- align the structural-degree cast with the afterD argument
  have hdeg : ((M.length + (tailU rest).length : ℕ) : ℝ)
      = ((armsA.length + 1 : ℕ) : ℝ)
        + ((k + others.length + (tailU rest).length + 1 : ℕ) : ℝ) - 1 := by
    rw [hM]
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    push_cast
    ring
  rw [hMprod, hMsum, hdeg, Kblock, armProd_append, armProd_replicate, Ztot_armU_five,
    afterD]
  ring

end Step3
end R3Cert
