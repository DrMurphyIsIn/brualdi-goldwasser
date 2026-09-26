/-
  R47 ARM-PERMUTATION INVARIANCE of the single-hub objective.

  The matching partition functions are already known permutation-invariant at the realized
  `RTree` level (`Ztot_node_perm`, R47Perm).  This file lifts that up the realization stack
  to the rooted-tree objective `Aobj`:

    * `Aobj_node_perm`        -- `Aobj (UTree.node cs)` is invariant under permuting `cs`.
      (`dtRealize` is an element-wise map with root degree `cs.length`, which is itself
      permutation-invariant, so a child permutation lifts through `dtRealize` to a realized
      child permutation, and `Ztot_node_perm` closes it.)
    * `Aobj_backbone_arm_perm`-- reordering a single hub's ARMS leaves `Aobj` unchanged.

  This is the crux that unblocks generalizing the first-two-arms transfer machinery
  (`BalanceStep` / `Aobj_balance_le`, which act on the first two arms only) to an ARBITRARY
  pair of arms: bring the pair to the front by a permutation, transfer, permute back.  The
  arbitrary-pair transfer and the `Hreach` PROGRESS lemma are the remaining pieces (not in
  this file).

  Self-contained; genuine proof (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47Perm
import R3Cert.R47HubState

namespace R3Cert
namespace Step3

open RTree

/-- `dtChildren` is a plain element-wise map (it weights each child by
    `1/(d * udeg)` and realizes it via `dtSub`). -/
theorem dtChildren_eq_map (d : ℕ) (cs : List UTree) :
    dtChildren d cs = cs.map (fun K => (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K)) := by
  induction cs with
  | nil => rw [dtChildren_nil, List.map_nil]
  | cons K rest ih => rw [dtChildren_cons, List.map_cons, ih]

/-- **`Aobj` is invariant under permuting a node's children.**  The root realization
    `dtRealize (node cs) = RTree.node (dtChildren cs.length cs)` maps children element-wise
    with the permutation-invariant degree `cs.length`, so a child permutation lifts to a
    realized-child permutation and `Ztot_node_perm` finishes. -/
theorem Aobj_node_perm {cs cs' : List UTree} (h : cs.Perm cs') :
    Aobj (UTree.node cs) = Aobj (UTree.node cs') := by
  have hlen : cs.length = cs'.length := h.length_eq
  simp only [Aobj, dtRealize_node]
  rw [dtChildren_eq_map, dtChildren_eq_map, hlen]
  exact Ztot_node_perm (h.map _)

/-- **Arm-permutation invariance of the single-hub objective.**  Reordering a hub's arms
    leaves `Aobj (backboneU [(arms, c)])` unchanged.  Generalizes the first-two-arms
    transfer machinery to arbitrary arm pairs. -/
theorem Aobj_backbone_arm_perm {arms arms' : List ℕ} (c : ℕ) (h : arms.Perm arms') :
    Aobj (backboneU [(arms, c)]) = Aobj (backboneU [(arms', c)]) := by
  have e : ∀ a : List ℕ,
      backboneU [(a, c)]
        = UTree.node (a.map armU ++ List.replicate c cherryU ++ []) := fun a => rfl
  rw [e arms, e arms']
  exact Aobj_node_perm (((h.map armU).append_right _).append_right _)

end Step3
end R3Cert
