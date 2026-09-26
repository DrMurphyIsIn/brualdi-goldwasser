/-
  R4-R7 campaign, PHASE 5e (part 3, third file): the MIRROR (anti-hubward) merge
  identities -- the donor in the UP position.

  Validated exactly (59/59 in-family, incl. monotonicity): rooted at the absorber b
  with the donor a heading the UP-chain,

      AobjV ((armsA,cA) :: upRest) (armsB,cb) down
        = K * beforeD (deg_b) (deg_a) cb cA k' sQ_b sr_a

  with `deg_b = |armsB| + |tailU down| + 1`, `deg_a = |armsA| + |tailU upRest| + 1`
  (the donor CARRIES the rest of the up-chain -- its movers include it),
  `sQ_b = sigmaArms armsB + qSum (tailU down)`,
  `sr_a = sigmaArms othersA + qSum (tailU upRest)` -- the ROLE-SWAPPED instantiation
  of the same certified table.

  THE MIRROR-AFTER IS FREE: the merged state is `Aobj_vee_after` with renamed
  arguments; `afterD_shift` (degree/slot sums invariance) transports its afterD form
  to the mirror's (dA, dB) split when the monotonicity assembles.

  Nothing here asserts per-step monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47VeeId

namespace R3Cert
namespace Step3

open RTree

/-! ### afterD depends only on the degree and slot SUMS -/

theorem afterD_shift (da db da' db' sQ sr sQ' sr' : ℝ) (cA k : ℕ)
    (hdeg : da + db = da' + db') (hsum : sQ + sr = sQ' + sr') :
    afterD da db cA k sQ sr = afterD da' db' cA k sQ' sr' := by
  unfold afterD
  rw [show da + db - 1 = da' + db' - 1 from by linarith,
    show sQ + (k : ℝ) * (3 / 19) + sr + 3 / 23
      = sQ' + (k : ℝ) * (3 / 19) + sr' + 3 / 23 from by linarith]

/-! ### The MIRROR BEFORE identity (raw form) -/

/-- **The mirror two-hub identity, before side**: the donor heads the up-chain of the
    absorber's rooting; same certified D-form at the role-swapped instantiation. -/
theorem Aobj_mirror_before_raw (armsA : List ℕ) (cA : ℕ) (armsB : List ℕ) (cb : ℕ)
    (down upRest : List Hub) :
    AobjV ((armsA, cA) :: upRest) (armsB, cb) down
      = Kblock armsB armsA upRest * ((tailU down).map fun K => Ztot (dtSub K)).prod
        * (Fw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
            * Fw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA
            * ((1 + zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
                  * (sigmaArms armsB + qSum (tailU down)))
                * (1 + zw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA
                    * (sigmaArms armsA + qSum (tailU upRest)))
              + zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb
                * zw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA)) := by
  set A : UTree := backboneU ((armsA, cA) :: upRest) with hA
  -- realize the root at b: children = armsB ++ cherries ++ (tailU down ++ [A])
  have hAobj : AobjV ((armsA, cA) :: upRest) (armsB, cb) down
      = Ztot (RTree.node (dtChildren ((armsB.length + (tailU down).length + 1) + cb)
          (armsB.map armU ++ List.replicate cb cherryU ++ (tailU down ++ [A])))) := by
    show Ztot (dtRealize (UTree.node
        (armsB.map armU ++ List.replicate cb cherryU ++ tailU down
          ++ tailU ((armsA, cA) :: upRest)))) = _
    rw [tailU_cons, dtRealize_node,
      show armsB.map armU ++ List.replicate cb cherryU ++ tailU down ++ [A]
        = armsB.map armU ++ List.replicate cb cherryU ++ (tailU down ++ [A]) from by
          simp]
    have hlen : (armsB.map armU ++ List.replicate cb cherryU
        ++ (tailU down ++ [A])).length
        = (armsB.length + (tailU down).length + 1) + cb := by
      simp [List.length_append]
      omega
    rw [hlen]
  -- the donor block (a, carrying upRest)
  have hAsub : dtSub A
      = RTree.node (dtChildren ((armsA.length + (tailU upRest).length + 1) + cA)
          (armsA.map armU ++ List.replicate cA cherryU ++ tailU upRest)) := by
    rw [hA, backboneU_eq, dtSub_node]
    have hlen : (armsA.map armU ++ List.replicate cA cherryU
        ++ tailU upRest).length + 1
        = (armsA.length + (tailU upRest).length + 1) + cA := by
      simp [List.length_append]
      omega
    rw [hlen]
  have hudegA : (udeg A : ℝ)
      = ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) + (cA : ℝ) := by
    rw [hA, udeg_backbone]
    push_cast
    ring
  have hZtA : Ztot (dtSub A)
      = (armProd armsA * ((tailU upRest).map fun K => Ztot (dtSub K)).prod)
        * (Fw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA
            * (1 + zw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA
                * (sigmaArms armsA + qSum (tailU upRest)))) := by
    rw [hAsub, Ztot_hubNode_dressed _ cA armsA (tailU upRest) (by omega)
      (fun K _ => Ztot_dt_pos K), armProd_double]
  have hZoA : Zopen (dtSub A)
      = armProd armsA * (3 / 2) ^ cA
        * ((tailU upRest).map fun K => Ztot (dtSub K)).prod := by
    rw [hAsub, Zopen_hubNode]
  -- dressed root at b with the two-block ts (down first, donor last)
  rw [hAobj, Ztot_hubNode_dressed (armsB.length + (tailU down).length + 1) cb armsB
    (tailU down ++ [A]) (by omega) (fun K _ => Ztot_dt_pos K), armProd_double,
    qSum_append, qSum_singleton]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [hZtA, hZoA, hudegA]
  have hzt : (0 : ℝ) < Ztot (dtSub A) := Ztot_dt_pos A
  rw [hZtA] at hzt
  have hDA : ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) + (cA : ℝ) ≠ 0 := by
    positivity
  have hFZ := Fw_mul_zw (armsA.length + (tailU upRest).length + 1) cA (by omega)
  have h32 : ((3 : ℝ) / 2) ^ cA
      = Fw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA
        * zw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA
        * (((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) + (cA : ℝ)) := by
    rw [hFZ]
    field_simp
  rw [Kblock]
  have hmid := twohub_scalar
      (armProd armsB * ((tailU down).map fun K => Ztot (dtSub K)).prod)
      (armProd armsA) (((tailU upRest).map fun K => Ztot (dtSub K)).prod)
      (Fw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb)
      (zw ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cb)
      (Fw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA)
      (zw ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cA)
      (sigmaArms armsB + qSum (tailU down))
      (sigmaArms armsA + qSum (tailU upRest))
      (((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) + (cA : ℝ))
      (((3 : ℝ) / 2) ^ cA) hDA hzt.ne' h32
  linear_combination hmid

/-! ### The MIRROR BEFORE identity (certificate-slot form) -/

/-- The mirror before identity in `beforeD` form (the DONOR's split feeds the slot;
    role-swapped instantiation `beforeD deg_b deg_a cb cA k'`). -/
theorem Aobj_mirror_before (armsA othersA : List ℕ) (cA : ℕ) (armsB : List ℕ)
    (cb k : ℕ) (down upRest : List Hub)
    (hsplit : armsA.Perm (List.replicate k 5 ++ othersA)) :
    AobjV ((armsA, cA) :: upRest) (armsB, cb) down
      = Kblock armsB armsA upRest * ((tailU down).map fun K => Ztot (dtSub K)).prod
        * beforeD ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ)
            ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cb cA k
            (sigmaArms armsB + qSum (tailU down))
            (sigmaArms othersA + qSum (tailU upRest)) := by
  rw [Aobj_mirror_before_raw armsA cA armsB cb down upRest]
  have hsum : sigmaArms armsA = (k : ℝ) * (3 / 23) + sigmaArms othersA := by
    rw [sigmaArms_perm hsplit, sigmaArms_append, sigmaArms_replicate, zw_one_five]
  rw [hsum, beforeD]
  ring

end Step3
end R3Cert
