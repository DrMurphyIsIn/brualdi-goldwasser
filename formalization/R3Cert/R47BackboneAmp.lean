/-
  R4-R7 campaign, PHASE 2a4: backbone amplitudes -- the chain recursion and the root form.

  The generic positivity block for the true-degree realization (mirror of 4c's `lit` block),
  then the two instantiations of `Ztot_hubNode` (P2a3): the INTERNAL chain recursion
  `Ztot_dtSub_backbone` (full degree = children + parent) and the ROOT amplitude
  `Aobj_backbone` (degree = child count).  These are the state-level interface for the P2b
  Kelmans moves.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Backbone

namespace R3Cert
namespace Step3

open RTree

/-! ### Positivity of the true-degree realization -/

mutual
theorem Zopen_dt_pos : ∀ K : UTree, 0 < Zopen (dtSub K)
  | .node cs => by
    rw [dtSub_node, Zopen]
    exact Popen_dtCh_pos (cs.length + 1) cs
theorem Ztot_dt_pos : ∀ K : UTree, 0 < Ztot (dtSub K)
  | .node cs => by
    rw [dtSub_node, Ztot]
    have h1 := Popen_dtCh_pos (cs.length + 1) cs
    have h2 := Matched_dtCh_nonneg (cs.length + 1) cs
    linarith
theorem Popen_dtCh_pos : ∀ (d : ℕ) (ch : List UTree), 0 < Popen (dtChildren d ch)
  | d, [] => by rw [dtChildren_nil, Popen]; norm_num
  | d, K :: rest => by
    rw [dtChildren_cons, Popen_cons]
    exact mul_pos (Ztot_dt_pos K) (Popen_dtCh_pos d rest)
theorem Matched_dtCh_nonneg : ∀ (d : ℕ) (ch : List UTree), 0 ≤ Matched (dtChildren d ch)
  | d, [] => by rw [dtChildren_nil, Matched]
  | d, K :: rest => by
    rw [dtChildren_cons, Matched_cons]
    have hw : (0 : ℝ) ≤ 1 / ((d : ℝ) * (udeg K : ℝ)) := by positivity
    have h1 := Zopen_dt_pos K
    have h2 := Popen_dtCh_pos d rest
    have h3 := Ztot_dt_pos K
    have h4 := Matched_dtCh_nonneg d rest
    have hterm1 : (0 : ℝ) ≤ 1 / ((d : ℝ) * (udeg K : ℝ)) * Zopen (dtSub K)
        * Popen (dtChildren d rest) := mul_nonneg (mul_nonneg hw h1.le) h2.le
    linarith [mul_nonneg h3.le h4]
end

/-! ### Backbone degrees -/

theorem udeg_backbone (arms : List ℕ) (c : ℕ) (rest : List Hub) :
    udeg (backboneU ((arms, c) :: rest))
      = arms.length + c + (tailU rest).length + 1 := by
  rw [backboneU_eq, udeg_node]
  simp [List.length_append]
  omega

/-! ### The chain recursion (internal hub: full degree = children + parent) -/

/-- **The internal backbone recursion.** -/
theorem Ztot_dtSub_backbone (arms : List ℕ) (c : ℕ) (rest : List Hub) :
    Ztot (dtSub (backboneU ((arms, c) :: rest)))
      = (((arms.map armU).map (fun K => Ztot (dtSub K))).prod * (3 / 2) ^ c
          * ((tailU rest).map (fun K => Ztot (dtSub K))).prod)
        * (1 + ((arms.map (fun j : ℕ =>
              3 / (((arms.length + c + (tailU rest).length + 1 : ℕ) : ℝ)
                * (4 * (j : ℝ) + 3)))).sum
            + (c : ℝ) * (1 / (3 * ((arms.length + c + (tailU rest).length + 1 : ℕ) : ℝ)))
            + ((dtChildren (arms.length + c + (tailU rest).length + 1) (tailU rest)).map
                (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum)) := by
  rw [backboneU_eq, dtSub_node]
  have hlen : (arms.map armU ++ List.replicate c cherryU ++ tailU rest).length
      = arms.length + c + (tailU rest).length := by
    simp [List.length_append]
    omega
  rw [hlen]
  exact Ztot_hubNode (arms.length + c + (tailU rest).length + 1) (by omega) arms c
    (tailU rest) (fun K _ => Ztot_dt_pos K)

/-! ### The root amplitude -/

/-- **The root backbone amplitude** (true root: degree = child count; the hub must be
    nonempty). -/
theorem Aobj_backbone (arms : List ℕ) (c : ℕ) (rest : List Hub)
    (hne : 0 < arms.length + c + (tailU rest).length) :
    Aobj (backboneU ((arms, c) :: rest))
      = (((arms.map armU).map (fun K => Ztot (dtSub K))).prod * (3 / 2) ^ c
          * ((tailU rest).map (fun K => Ztot (dtSub K))).prod)
        * (1 + ((arms.map (fun j : ℕ =>
              3 / (((arms.length + c + (tailU rest).length : ℕ) : ℝ)
                * (4 * (j : ℝ) + 3)))).sum
            + (c : ℝ) * (1 / (3 * ((arms.length + c + (tailU rest).length : ℕ) : ℝ)))
            + ((dtChildren (arms.length + c + (tailU rest).length) (tailU rest)).map
                (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum)) := by
  have hA : Aobj (backboneU ((arms, c) :: rest))
      = Ztot (dtRealize (backboneU ((arms, c) :: rest))) := rfl
  rw [hA, backboneU_eq, dtRealize_node]
  have hlen : (arms.map armU ++ List.replicate c cherryU ++ tailU rest).length
      = arms.length + c + (tailU rest).length := by
    simp [List.length_append]
    omega
  rw [hlen]
  exact Ztot_hubNode (arms.length + c + (tailU rest).length) hne arms c
    (tailU rest) (fun K _ => Ztot_dt_pos K)

end Step3
end R3Cert
