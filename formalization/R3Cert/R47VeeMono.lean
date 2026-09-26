/-
  R4-R7 campaign, PHASE 5e (part 3, fourth file): the Vee merge reductions -- BOTH
  directions reduced to certificate instances.

  * `vee_merge_le_of_cellD`    -- hubward at any rooting: if the certificate
    comparison holds at the Vee data, the merge does not decrease `AobjV`;
  * `mirror_merge_le_of_cellD` -- anti-hubward: the donor heads the up-chain; the
    before side is the role-swapped identity, the after side is `Aobj_vee_after`
    with renamed arguments transported by `afterD_shift` (the degree and slot SUMS
    coincide: `|armsA| = k' + |othersA|` aligns the partitions).

  The box-data dispatch (the 36 adapters at the Vee/mirror instantiations) is the
  next file.  Nothing here asserts unconditional per-step monotonicity.
  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47MirrorId
import R3Cert.R47Dispatch

namespace R3Cert
namespace Step3

open RTree

/-! ### The hubward Vee reduction -/

/-- **The Vee reduction, hubward.**  With `daV = |armsA| + |tailU up| + 1`,
    `dbV = |armsB| + |tailU down| + 1`, `sQV = sigmaArms armsA + qSum (tailU up)`,
    `srV = sigmaArms others + qSum (tailU down)`: the certificate comparison at the
    Vee data bounds the rooted merge. -/
theorem vee_merge_le_of_cellD (armsA : List ℕ) (cA : ℕ) (armsB others : List ℕ)
    (cb k : ℕ) (down up : List Hub)
    (hsplit : armsB.Perm (List.replicate k 5 ++ others))
    (hcell : beforeD ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ)
        ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cA cb k
        (sigmaArms armsA + qSum (tailU up))
        (sigmaArms others + qSum (tailU down))
      ≤ afterD ((armsA.length + (tailU up).length + 1 : ℕ) : ℝ)
        ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ) cA k
        (sigmaArms armsA + qSum (tailU up))
        (sigmaArms others + qSum (tailU down))) :
    AobjV up (armsA, cA) ((armsB, cb) :: down)
      ≤ AobjV up (armsA ++ List.replicate k 4 ++ others ++ [5], cA) down := by
  have hlenB : armsB.length = k + others.length := by
    simpa [List.length_append, List.length_replicate] using hsplit.length_eq
  have hdb : ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ)
      = ((k + others.length + (tailU down).length + 1 : ℕ) : ℝ) := by
    rw [hlenB]
  have hKeq : Kblock armsA armsB down
      = Kblock armsA (List.replicate k 5 ++ others) down := by
    rw [Kblock, Kblock, armProd_perm hsplit]
  rw [hdb] at hcell
  rw [Aobj_vee_before armsA cA armsB others cb k down up hsplit,
    Aobj_vee_after armsA cA others k down up, hKeq, hdb]
  have hK : 0 < Kblock armsA (List.replicate k 5 ++ others) down
      * ((tailU up).map fun K => Ztot (dtSub K)).prod := by
    have h1 := Kblock_pos armsA (List.replicate k 5 ++ others) down
    have h2 := listProd_pos (tailU up)
    positivity
  exact mul_le_mul_of_nonneg_left hcell hK.le

/-! ### The anti-hubward (mirror) reduction -/

/-- **The mirror reduction.**  The donor `(armsA, cA)` heads the up-chain; the
    certificate comparison at the ROLE-SWAPPED data (`beforeD deg_b deg_a cb cA k`)
    bounds the merge into the second hub.  The after side is the Vee after identity
    with renamed arguments, transported by `afterD_shift` (`|armsA| = k + |othersA|`
    makes both the degree and slot sums coincide). -/
theorem mirror_merge_le_of_cellD (armsA othersA : List ℕ) (cA : ℕ) (armsB : List ℕ)
    (cb k : ℕ) (down upRest : List Hub)
    (hsplit : armsA.Perm (List.replicate k 5 ++ othersA))
    (hcell : beforeD ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ)
        ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cb cA k
        (sigmaArms armsB + qSum (tailU down))
        (sigmaArms othersA + qSum (tailU upRest))
      ≤ afterD ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ)
        ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cb k
        (sigmaArms armsB + qSum (tailU down))
        (sigmaArms othersA + qSum (tailU upRest))) :
    AobjV ((armsA, cA) :: upRest) (armsB, cb) down
      ≤ AobjV upRest (armsB ++ List.replicate k 4 ++ othersA ++ [5], cb) down := by
  have hlenA : armsA.length = k + othersA.length := by
    simpa [List.length_append, List.length_replicate] using hsplit.length_eq
  -- transport the certificate's afterD to the Vee-after partition
  have hshift : afterD ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ)
        ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cb k
        (sigmaArms armsB + qSum (tailU down))
        (sigmaArms othersA + qSum (tailU upRest))
      = afterD ((armsB.length + (tailU upRest).length + 1 : ℕ) : ℝ)
        ((k + othersA.length + (tailU down).length + 1 : ℕ) : ℝ) cb k
        (sigmaArms armsB + qSum (tailU upRest))
        (sigmaArms othersA + qSum (tailU down)) := by
    apply afterD_shift
    · push_cast
      rw [hlenA]
      push_cast
      ring
    · ring
  rw [hshift] at hcell
  have hKeq : Kblock armsB armsA upRest
      = armProd armsB * armProd (List.replicate k 5 ++ othersA)
        * ((tailU upRest).map fun K => Ztot (dtSub K)).prod := by
    rw [Kblock, armProd_perm hsplit]
  rw [Aobj_mirror_before armsA othersA cA armsB cb k down upRest hsplit,
    Aobj_vee_after armsB cb othersA k down upRest, hKeq]
  have hK : 0 < armProd armsB * armProd (List.replicate k 5 ++ othersA)
      * ((tailU upRest).map fun K => Ztot (dtSub K)).prod
      * ((tailU down).map fun K => Ztot (dtSub K)).prod := by
    have h1 := armProd_pos armsB
    have h2 := armProd_pos (List.replicate k 5 ++ othersA)
    have h3 := listProd_pos (tailU upRest)
    have h4 := listProd_pos (tailU down)
    positivity
  calc armProd armsB * armProd (List.replicate k 5 ++ othersA)
        * ((tailU upRest).map fun K => Ztot (dtSub K)).prod
        * ((tailU down).map fun K => Ztot (dtSub K)).prod
        * beforeD ((armsB.length + (tailU down).length + 1 : ℕ) : ℝ)
            ((armsA.length + (tailU upRest).length + 1 : ℕ) : ℝ) cb cA k
            (sigmaArms armsB + qSum (tailU down))
            (sigmaArms othersA + qSum (tailU upRest))
      ≤ armProd armsB * armProd (List.replicate k 5 ++ othersA)
          * ((tailU upRest).map fun K => Ztot (dtSub K)).prod
          * ((tailU down).map fun K => Ztot (dtSub K)).prod
          * afterD ((armsB.length + (tailU upRest).length + 1 : ℕ) : ℝ)
              ((k + othersA.length + (tailU down).length + 1 : ℕ) : ℝ) cb k
              (sigmaArms armsB + qSum (tailU upRest))
              (sigmaArms othersA + qSum (tailU down)) :=
        mul_le_mul_of_nonneg_left hcell hK.le
    _ = Kblock armsB (List.replicate k 5 ++ othersA) down
          * ((tailU upRest).map fun K => Ztot (dtSub K)).prod
          * afterD ((armsB.length + (tailU upRest).length + 1 : ℕ) : ℝ)
              ((k + othersA.length + (tailU down).length + 1 : ℕ) : ℝ) cb k
              (sigmaArms armsB + qSum (tailU upRest))
              (sigmaArms othersA + qSum (tailU down)) := by
        rw [Kblock]
        ring

end Step3
end R3Cert
