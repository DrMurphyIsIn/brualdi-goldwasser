/-
  R4-R7 campaign, PHASE 5d (part 1): the head-merge monotonicity reduction.

  Per P5_SEAM_DESIGN.md (S4/S5), this file reduces the head-merge comparison to a
  single beforeD-vs-afterD instance and certifies the box data the 36-cell table
  needs on the certified family:

  * `armProd_pos`/`Kblock_pos` -- the common block is strictly positive, so the
    comparison divides out;
  * `qSum_tailU_nonneg`/`qSum_tailU_le` -- the state tail's dressed cavity lies in
    `[0, |tail| * 3/16]` on the capped family (>= 5 arms => full degree >= 6);
  * `sigmaArms_floor` -- any nonempty balanced arm list clears the direct-row one-arm
    floor 3/23 (a load-4 arm gives 3/19 > 3/23);
  * `head_merge_le_of_cellD` -- THE REDUCTION: if the certificate comparison
    `beforeD <= afterD` holds at the state's data, the head merge does not decrease
    `Aobj` (the R47HeadId identities + Kblock positivity).

  HONEST BOUNDARY: the degree ordering `db <= da` (S5) enters only in part 2's cell
  dispatch, as a hypothesis -- the anti-hubward direction is a named residual.
  Nothing here asserts per-step monotonicity yet.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47HeadId

namespace R3Cert
namespace Step3

open RTree

/-! ### Positivity of the common block -/

theorem armProd_cons (a : ℕ) (rest : List ℕ) :
    armProd (a :: rest) = Ztot (dtSub (armU a)) * armProd rest := by
  rw [armProd, armProd, List.map_cons, List.prod_cons]

theorem armProd_pos (arms : List ℕ) : 0 < armProd arms := by
  induction arms with
  | nil => simp [armProd]
  | cons a rest ih =>
    have ha := Ztot_dtSub_armU_pos a
    rw [armProd_cons]
    positivity

theorem listProd_pos (ts : List UTree) :
    0 < (ts.map fun K => Ztot (dtSub K)).prod := by
  induction ts with
  | nil => simp
  | cons K rest ih =>
    have hK := Ztot_dt_pos K
    rw [List.map_cons, List.prod_cons]
    positivity

theorem Kblock_pos (armsA armsB : List ℕ) (rest : List Hub) :
    0 < Kblock armsA armsB rest := by
  have h1 := armProd_pos armsA
  have h2 := armProd_pos armsB
  have h3 := listProd_pos (tailU rest)
  rw [Kblock]
  positivity

/-! ### Tail cavity bounds on the capped family -/

theorem qSum_tailU_nonneg (rest : List Hub) : 0 ≤ qSum (tailU rest) := by
  cases rest with
  | nil => simp [tailU_nil, qSum]
  | cons h t =>
    rw [tailU_cons, qSum_singleton]
    have h1 := Zopen_dt_pos (backboneU (h :: t))
    have h2 := Ztot_dt_pos (backboneU (h :: t))
    positivity

/-- On the capped family the tail's dressed cavity is under the per-neighbour cap. -/
theorem qSum_tailU_le (rest : List Hub) (hcap : Capped rest) :
    qSum (tailU rest) ≤ ((tailU rest).length : ℝ) * (3 / 16) := by
  cases rest with
  | nil => simp [tailU_nil, qSum]
  | cons h t =>
    obtain ⟨arms, c⟩ := h
    rw [tailU_cons, qSum_singleton]
    have h5 : 5 ≤ arms.length := hcap (arms, c) (by simp)
    have h6 := udeg_backbone_ge_six arms c t h5
    have hle := q_dressed_le_of_udeg (backboneU ((arms, c) :: t)) h6
    simp only [List.length_cons, List.length_nil]
    push_cast
    linarith

/-! ### The direct-row one-arm floor -/

/-- Any nonempty balanced arm list clears the floor 3/23. -/
theorem sigmaArms_floor (arms : List ℕ) (hbal : BalancedArms arms)
    (hne : arms ≠ []) : 3 / 23 ≤ sigmaArms arms := by
  cases arms with
  | nil => exact absurd rfl hne
  | cons a rest =>
    have hrest : 0 ≤ sigmaArms rest := sum_zw_arms_nonneg rest
    have ha : 3 / 23 ≤ zw 1 a := by
      rcases hbal a (by simp) with rfl | rfl
      · rw [zw_one_four]; norm_num
      · rw [zw_one_five]
    have hcons : sigmaArms (a :: rest) = zw 1 a + sigmaArms rest := by
      simp [sigmaArms]
    rw [hcons]
    linarith

/-! ### The head-merge reduction -/

/-- **THE REDUCTION.**  If the certificate comparison holds at the state's data --
    `da = |armsA| + 1`, `db = |armsB| + |tail| + 1`, `sQ = sigmaArms armsA`,
    `sr = sigmaArms others + qSum tail` -- then the head merge does not decrease the
    objective.  (The 36-cell dispatch supplies the hypothesis in part 2.) -/
theorem head_merge_le_of_cellD (armsA : List ℕ) (cA : ℕ) (armsB others : List ℕ)
    (cb k : ℕ) (rest : List Hub)
    (hsplit : armsB.Perm (List.replicate k 5 ++ others))
    (hcell : beforeD ((armsA.length + 1 : ℕ) : ℝ)
        ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cA cb k
        (sigmaArms armsA) (sigmaArms others + qSum (tailU rest))
      ≤ afterD ((armsA.length + 1 : ℕ) : ℝ)
        ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ) cA k
        (sigmaArms armsA) (sigmaArms others + qSum (tailU rest))) :
    Aobj (backboneU ((armsA, cA) :: (armsB, cb) :: rest))
      ≤ Aobj (backboneU ((armsA ++ List.replicate k 4 ++ others ++ [5], cA) :: rest)) := by
  have hlenB : armsB.length = k + others.length := by
    have h := hsplit.length_eq
    simpa [List.length_append, List.length_replicate] using h
  have hdb : ((armsB.length + (tailU rest).length + 1 : ℕ) : ℝ)
      = ((k + others.length + (tailU rest).length + 1 : ℕ) : ℝ) := by
    rw [hlenB]
  have hKeq : Kblock armsA armsB rest
      = Kblock armsA (List.replicate k 5 ++ others) rest := by
    rw [Kblock, Kblock, armProd_perm hsplit]
  rw [hdb] at hcell
  rw [Aobj_head_before armsA cA armsB others cb k rest hsplit,
    Aobj_head_after armsA cA others k rest, hKeq, hdb]
  exact mul_le_mul_of_nonneg_left hcell
    (Kblock_pos armsA (List.replicate k 5 ++ others) rest).le

end Step3
end R3Cert
