/-
  R4-R7 campaign, PHASE 5e (part 3, second file): the VEE-form merge identities
  (hubward direction) -- the head identities with an UP-chain present.

  Validated exactly (60/60 random Vee states, all 36 load cells): rooted at the
  absorber with the donor in the DOWN position,

      AobjV up a ((armsB,cb) :: down) = KblockV * beforeD daV dbV cA cb k sQV srV
      AobjV up (merged) down          = KblockV * afterD  daV dbV cA k    sQV srV

  with `daV = |armsA| + |tailU up| + 1` (the up-edge joins the absorber's degree),
  `sQV = sigmaArms armsA + qSum (tailU up)` (the up-block is one more capped
  neighbour), `KblockV = Kblock * (up-block Ztots)`.  This file: `qSum_append` and
  the BEFORE identity (raw donor sum).  Per the pinned construction notes: the
  donor-side haves are the HeadId ones verbatim (`down` for `rest`), and the endgame
  instantiates `twohub_scalar` EXPLICITLY and closes by `linear_combination` (ring
  glue on both sides; the up-factors reassociate into the PA/SA slots, the division
  subterm is a ring-atom -- no transcription of goal shapes).

  The split form, the AFTER identity, the mirror (donor-in-up) identities, and both
  `vee_merge_le` directions are the next files.  Nothing here asserts per-step
  monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47RotateV

namespace R3Cert
namespace Step3

open RTree

/-! ### qSum over concatenation -/

theorem qSum_append (l1 l2 : List UTree) : qSum (l1 ++ l2) = qSum l1 + qSum l2 := by
  simp [qSum]

/-! ### The hubward Vee BEFORE identity (raw form) -/

/-- **The Vee two-hub identity, before side** (up-chain present; raw donor sum).
    The absorber's degree gains the up-edge and its sigma slot gains the up-block's
    dressed cavity; the common block gains the up-block's Ztots. -/
theorem Aobj_vee_before_raw (armsA : List ℕ) (cA : ℕ) (armsB : List ℕ) (cb : ℕ)
    (down up : List Hub) :
    AobjV up (armsA, cA) ((armsB, cb) :: down)
      = Kblock armsA armsB down * ((tailU up).map fun K => Ztot (dtSub K)).prod
        * (Fw ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ) cA
            * Fw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
            * ((1 + zw ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ) cA
                  * (sigmaArms armsA + qSum (tailU up)))
                * (1 + zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
                    * (sigmaArms armsB + qSum (tailU down)))
              + zw ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ) cA
                * zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb)) := by
  set B : UTree := backboneU ((armsB, cb) :: down) with hB
  -- realize the Vee root: children = armsA ++ cherries ++ ([B] ++ tailU up)
  have hAobj : AobjV up (armsA, cA) ((armsB, cb) :: down)
      = Ztot (RTree.node (dtChildren ((armsA.length + (tailU up).length + 1) + cA)
          (armsA.map armU ++ List.replicate cA cherryU ++ ([B] ++ tailU up)))) := by
    show Ztot (dtRealize (UTree.node
        (armsA.map armU ++ List.replicate cA cherryU ++ tailU ((armsB, cb) :: down)
          ++ tailU up))) = _
    rw [tailU_cons, dtRealize_node,
      show armsA.map armU ++ List.replicate cA cherryU ++ [B] ++ tailU up
        = armsA.map armU ++ List.replicate cA cherryU ++ ([B] ++ tailU up) from by
          simp]
    have hlen : (armsA.map armU ++ List.replicate cA cherryU ++ ([B] ++ tailU up)).length
        = (armsA.length + (tailU up).length + 1) + cA := by
      simp [List.length_append]
      omega
    rw [hlen]
  -- the donor block (verbatim HeadId haves with `down` for `rest`)
  have hBsub : dtSub B
      = RTree.node (dtChildren ((armsB.length + (tailU down).length + 1) + cb)
          (armsB.map armU ++ List.replicate cb cherryU ++ tailU down)) := by
    rw [hB, backboneU_eq, dtSub_node]
    have hlen : (armsB.map armU ++ List.replicate cb cherryU ++ tailU down).length + 1
        = (armsB.length + (tailU down).length + 1) + cb := by
      simp [List.length_append]
      omega
    rw [hlen]
  have hudegB : (udeg B : ℝ)
      = ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) + (cb : ℝ) := by
    rw [hB, udeg_backbone]
    push_cast
    ring
  have hZtB : Ztot (dtSub B)
      = (armProd armsB * ((tailU down).map fun K => Ztot (dtSub K)).prod)
        * (Fw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
            * (1 + zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
                * (sigmaArms armsB + qSum (tailU down)))) := by
    rw [hBsub, Ztot_hubNode_dressed _ cb armsB (tailU down) (by omega)
      (fun K _ => Ztot_dt_pos K), armProd_double]
  have hZoB : Zopen (dtSub B)
      = armProd armsB * (3 / 2) ^ cb
        * ((tailU down).map fun K => Ztot (dtSub K)).prod := by
    rw [hBsub, Zopen_hubNode]
  -- dressed root with the two-block ts
  rw [hAobj, Ztot_hubNode_dressed (armsA.length + (tailU up).length + 1) cA armsA
    ([B] ++ tailU up) (by omega) (fun K _ => Ztot_dt_pos K), armProd_double,
    qSum_append, qSum_singleton]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [hZtB, hZoB, hudegB]
  have hzt : (0 : ℝ) < Ztot (dtSub B) := Ztot_dt_pos B
  rw [hZtB] at hzt
  have hDB : ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) + (cb : ℝ) ≠ 0 := by
    positivity
  have hFZ := Fw_mul_zw (armsB.length + (tailU down).length + 1) cb (by omega)
  have h32 : ((3 : ℝ) / 2) ^ cb
      = Fw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
        * zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
        * (((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) + (cb : ℝ)) := by
    rw [hFZ]
    field_simp
  rw [Kblock]
  have hmid := twohub_scalar
      (armProd armsA * ((tailU up).map fun K => Ztot (dtSub K)).prod)
      (armProd armsB) (((tailU down).map fun K => Ztot (dtSub K)).prod)
      (Fw ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ) cA)
      (zw ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ) cA)
      (Fw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb)
      (zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb)
      (sigmaArms armsA + qSum (tailU up))
      (sigmaArms armsB + qSum (tailU down))
      (((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) + (cb : ℝ))
      (((3 : ℝ) / 2) ^ cb) hDB hzt.ne' h32
  linear_combination hmid

/-! ### The hubward Vee BEFORE identity (certificate-slot form) -/

/-- The Vee before identity in `beforeD` form: the donor split feeds the certificate
    slot `k * (3/23) + sr`, exactly as in the head case. -/
theorem Aobj_vee_before (armsA : List ℕ) (cA : ℕ) (armsB others : List ℕ) (cb k : ℕ)
    (down up : List Hub) (hsplit : armsB.Perm (List.replicate k 5 ++ others)) :
    AobjV up (armsA, cA) ((armsB, cb) :: down)
      = Kblock armsA armsB down * ((tailU up).map fun K => Ztot (dtSub K)).prod
        * beforeD ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ)
            ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cA cb k
            (sigmaArms armsA + qSum (tailU up))
            (sigmaArms others + qSum (tailU down)) := by
  rw [Aobj_vee_before_raw armsA cA armsB cb down up]
  have hsum : sigmaArms armsB = (k : ℝ) * (3 / 23) + sigmaArms others := by
    rw [sigmaArms_perm hsplit, sigmaArms_append, sigmaArms_replicate, zw_one_five]
  rw [hsum, beforeD]
  ring

/-! ### The hubward Vee AFTER identity -/

/-- **The Vee after identity**: the merged state rooted with the up-chain present.
    Same Wt^k mechanism; the up-block joins the degree, the sigma slot, and the
    common block exactly as in the before side. -/
theorem Aobj_vee_after (armsA : List ℕ) (cA : ℕ) (others : List ℕ) (k : ℕ)
    (down up : List Hub) :
    AobjV up (armsA ++ List.replicate k 4 ++ others ++ [5], cA) down
      = Kblock armsA (List.replicate k 5 ++ others) down
        * ((tailU up).map fun K => Ztot (dtSub K)).prod
        * afterD ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ)
            ((k + others.length + (tailU down).length + 1 : ℕ) : ℝ) cA k
            (sigmaArms armsA + qSum (tailU up))
            (sigmaArms others + qSum (tailU down)) := by
  set M : List ℕ := armsA ++ List.replicate k 4 ++ others ++ [5] with hM
  have hAobj : AobjV up (M, cA) down
      = Ztot (RTree.node (dtChildren
          ((M.length + ((tailU down).length + (tailU up).length)) + cA)
          (M.map armU ++ List.replicate cA cherryU ++ (tailU down ++ tailU up)))) := by
    show Ztot (dtRealize (UTree.node
        (M.map armU ++ List.replicate cA cherryU ++ tailU down ++ tailU up))) = _
    rw [dtRealize_node,
      show M.map armU ++ List.replicate cA cherryU ++ tailU down ++ tailU up
        = M.map armU ++ List.replicate cA cherryU ++ (tailU down ++ tailU up) from by
          simp]
    have hlen : (M.map armU ++ List.replicate cA cherryU
        ++ (tailU down ++ tailU up)).length
        = (M.length + ((tailU down).length + (tailU up).length)) + cA := by
      simp [List.length_append]
      omega
    rw [hlen]
  have hMpos : 0 < M.length + ((tailU down).length + (tailU up).length) := by
    rw [hM]
    simp [List.length_append]
  rw [hAobj, Ztot_hubNode_dressed (M.length + ((tailU down).length + (tailU up).length))
    cA M (tailU down ++ tailU up) hMpos (fun K _ => Ztot_dt_pos K), armProd_double,
    qSum_append]
  simp only [List.map_append, List.prod_append]
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
  have hdeg : ((M.length + ((tailU down).length + (tailU up).length) : ℕ) : ℝ)
      = ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ)
        + ((k + others.length + (tailU down).length + 1 : ℕ) : ℝ) - 1 := by
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
