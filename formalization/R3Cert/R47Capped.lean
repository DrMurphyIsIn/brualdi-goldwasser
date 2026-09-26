/-
  R4-R7 campaign, PHASE 5b: the certified-family cap invariant and the state-level
  box bounds.

  Per P5_SEAM_DESIGN.md (S4): the certificate table needs every environment neighbour
  under the 3/16 activity cap.  On the HubState encoding:
  * arms of load {4,5} contribute EXACTLY `zw 1 j` (3/19, 3/23 -- R47Dress), both
    <= 3/16;
  * a backbone tail hub with >= 5 arms has full degree >= 6, so its dressed cavity is
    under the cap by the crude bound (R47Dress `q_dressed_le_of_udeg`).

  This file machine-checks:
  * `Capped`        -- every hub carries at least 5 arms;
  * `Step.capped`   -- the topped-up merge preserves it (the absorber's arm list only
    grows; other hubs untouched);
  * `udeg_backbone_ge_six` -- a capped backbone realizes with full degree >= 6;
  * the aggregated neighbour-sum bounds the identity's boxes need:
    `sum_zw_arms_nonneg`, `sum_zw_arms_le` (<= length * 3/16 on the balanced family),
    `sum_zw_arms_ge_floor` (the one-arm floor 3/23 when a load-5 arm is present).

  HONEST BOUNDARY: `Capped` guarantees the CAP side only; merge APPLICABILITY on the
  family (enough load-5 borrow arms) is the (L)/(B) normalization layer's obligation,
  not asserted here.  Nothing here asserts per-step monotonicity.
  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Dress

namespace R3Cert
namespace Step3

open RTree

/-! ### The cap invariant -/

/-- Every hub of the state carries at least 5 arms. -/
def Capped (s : List Hub) : Prop := ∀ h ∈ s, 5 ≤ h.1.length

/-- The topped-up merge preserves the cap: the absorber's arm list grows, everything
    else is untouched. -/
theorem Step.capped {s s' : List Hub} (hst : Step s s') : Capped s → Capped s' := by
  induction hst with
  | @merge armsA cA armsB others cb rest hcb hsplit =>
    intro hc h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · have hA : 5 ≤ armsA.length := hc (armsA, cA) (by simp)
      simp only [List.length_append]
      omega
    · exact hc h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))
  | @tail hd s s' hst ih =>
    intro hc h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact hc _ (by simp)
    · exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) _ hh

/-- A capped backbone realizes with full degree at least 6 (>= 5 arms + the parent
    edge), so `q_dressed_le_of_udeg` puts its dressed cavity under the 3/16 cap. -/
theorem udeg_backbone_ge_six (arms : List ℕ) (c : ℕ) (rest : List Hub)
    (h5 : 5 ≤ arms.length) :
    6 ≤ udeg (backboneU ((arms, c) :: rest)) := by
  rw [udeg_backbone]
  omega

/-! ### Aggregated neighbour-sum bounds -/

theorem zw_nonneg (j : ℕ) : 0 ≤ zw 1 j := by
  unfold zw
  positivity

/-- Dressed arm sums are nonnegative. -/
theorem sum_zw_arms_nonneg (arms : List ℕ) :
    0 ≤ ((arms.map fun j : ℕ => zw 1 j).sum) := by
  induction arms with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons]
    have := zw_nonneg a
    linarith

/-- On the balanced family every arm activity is under the cap, so the dressed arm sum
    is at most `length * 3/16` -- the sigma-box upper bound. -/
theorem sum_zw_arms_le (arms : List ℕ) (hb : BalancedArms arms) :
    ((arms.map fun j : ℕ => zw 1 j).sum) ≤ (arms.length : ℝ) * (3 / 16) := by
  induction arms with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have ha : zw 1 a ≤ 3 / 16 := by
      rcases hb a (by simp) with rfl | rfl
      · exact zw_one_four_le
      · exact zw_one_five_le
    have hrest := ih (fun j hj => hb j (List.mem_cons_of_mem _ hj))
    push_cast
    linarith

/-- The one-arm floor: a load-5 arm in the list puts the dressed sum at or above 3/23
    (the direct-cell sigma floor). -/
theorem sum_zw_arms_ge_floor (arms : List ℕ) (h5 : 5 ∈ arms) :
    3 / 23 ≤ ((arms.map fun j : ℕ => zw 1 j).sum) := by
  induction arms with
  | nil => exact absurd h5 (by simp)
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h5 with rfl | h5
    · have := sum_zw_arms_nonneg rest
      have hz : zw 1 5 = 3 / 23 := zw_one_five
      linarith
    · have := ih h5
      have := zw_nonneg a
      linarith

end Step3
end R3Cert
