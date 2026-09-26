/-
  R4-R7 campaign, PHASE 7: DEGREE-CHANGING child-replacement monotonicity (tree->hub, Phase 1).

  The equal-degree workhorse `R47R6SpineMono.node_Ztot_child_mono` requires `udeg T = udeg T'`.
  A structural STRAIGHTENING move changes a child's degree (absorbing a branch changes its child
  count), so it needs the degree-CHANGING generalization.  The snoc decomposition
  (`Ztot_node_snoc`) is linear with nonnegative coefficients in the tail child's `(Ztot, Zopen)`:

      Ztot(node(dtChildren d (pre++[T]))) = C₁·Ztot(dtSub T) + Popen·(1/(d·udeg T))·Zopen(dtSub T),
      C₁ = Popen·(1 + Σ_env) ≥ 0,  Popen ≥ 0.

  Only the SECOND coefficient depends on `udeg T`.  So the degree-changing lemma is the equal-degree
  one with the second-term inequality (the "cavity-balancing" condition) taken as a hypothesis in
  its already-weighted form -- clean and division-free.

  What is PROVED here (no `sorry`, axiom-clean):
    * `node_Ztot_child_mono_deg` -- degree-changing child-`Ztot` monotonicity;
    * `Aobj_tail_child_replace_le_deg` -- its lift to `Aobj` at the root (child count unchanged).

  This is the Lean infrastructure the size-preserving straightening move (`StraightProgress_sized`)
  needs.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6SpineMono
import R3Cert.R47ArmPerm

namespace R3Cert
namespace Step3

open RTree

/-- **Degree-changing child-`Ztot` monotonicity.**  Replacing the tail child `T` by `T'` with
    not-smaller `Ztot(dtSub)` and not-smaller WEIGHTED `Zopen(dtSub)` (`(1/(d·udeg))·Zopen`, the
    cavity-balancing condition that absorbs a possible degree change) does not decrease the node's
    `Ztot` -- no equal-degree hypothesis. -/
theorem node_Ztot_child_mono_deg (pre : List UTree) (T T' : UTree) (d : ℕ)
    (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T'))
    (hweighted : (1 / ((d : ℝ) * (udeg T : ℝ))) * Zopen (dtSub T)
               ≤ (1 / ((d : ℝ) * (udeg T' : ℝ))) * Zopen (dtSub T')) :
    Ztot (RTree.node (dtChildren d (pre ++ [T])))
      ≤ Ztot (RTree.node (dtChildren d (pre ++ [T']))) := by
  rw [Ztot_node_snoc, Ztot_node_snoc]
  have hPopen : 0 ≤ Popen (dtChildren d pre) := by
    rw [Popen_dtChildren]; apply List.prod_nonneg; intro x hx
    obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le
  have hSum : 0 ≤ ((dtChildren d pre).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum :=
    tail_env_nonneg d pre
  have hC1 : 0 ≤ Popen (dtChildren d pre)
      * (1 + ((dtChildren d pre).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum) :=
    mul_nonneg hPopen (by linarith [hSum])
  refine add_le_add (mul_le_mul_of_nonneg_left hzt hC1) ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left hweighted hPopen

/-- **Degree-changing tail child-replacement is `Aobj`-monotone at the root.**  Replacing the last
    root child by one with not-smaller `Ztot(dtSub)` and weighted `Zopen(dtSub)` does not decrease
    `Aobj` (the root child COUNT is unchanged, so the root degree is common; only the replaced
    child's own degree may change). -/
theorem Aobj_tail_child_replace_le_deg (pre : List UTree) (T T' : UTree)
    (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T'))
    (hweighted : (1 / (((pre.length + 1 : ℕ) : ℝ) * (udeg T : ℝ))) * Zopen (dtSub T)
               ≤ (1 / (((pre.length + 1 : ℕ) : ℝ) * (udeg T' : ℝ))) * Zopen (dtSub T')) :
    Aobj (UTree.node (pre ++ [T])) ≤ Aobj (UTree.node (pre ++ [T'])) := by
  simp only [Aobj, dtRealize_node]
  have hlenT : (pre ++ [T]).length = pre.length + 1 := by simp
  have hlenT' : (pre ++ [T']).length = pre.length + 1 := by simp
  rw [hlenT, hlenT']
  exact node_Ztot_child_mono_deg pre T T' (pre.length + 1) hzt hweighted

end Step3
end R3Cert
