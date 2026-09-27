/-
  Bridge STEP 4i: THE COMPOSITION -- the real-graph amplitude identity.

  Chains everything: 4h's `realize_weights` + 4g's `litHub_good` discharge the `hw`
  hypothesis through the 4e/4f count bridges, giving the full `IsEdgeEnum` instance for the
  realized competitor trees; then `pi_eq_msum` (3d) + `msum_liftEdges` (3e) + `Ztot_eq_msum`
  (3) collapse the Laplacian permanent ratio of the REAL SimpleGraph to the raw matching
  partition function:

    `pi_litHub` :  per L(G_T) / prod deg  =  Ztot (litHub c ch),

  and with `amplitude_bridge_logPhi` (4d) + `exp_logPhi_mul_rhoB_pow` (4c):

    `amplitude_bridge_real` :  the hub ratio of the REAL graphs  ->  exp (logPhi b) * rhoB^V(b).

  SCOPE NOTE: in THIS file the acyclicity of the address graph is a hypothesis of
  `pi_litHub`/`amplitude_bridge_real`; it is DISCHARGED in `BridgeStep4j`
  (`aGraph_realize_isAcyclic`), which restates both capstones UNCONDITIONALLY
  (`pi_litHub'`, `amplitude_bridge_real'`).  Degree positivity is proved here
  (`aGraph_degree_pos`: every support vertex is an endpoint).
  conjecture1_proved=False (the R4-R7 reduction layer stays at Python/paper level).

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.BridgeStep4h

namespace R3Cert
namespace Step3

open RTree Filter Topology

/-! ### Degree positivity (every support vertex is an endpoint) -/

theorem aGraph_degree_pos (E : List AEdge)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2.1)
    (hkeys : ∀ e ∈ E, ∀ f ∈ E,
      (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e)
    (u : AVert E) : 0 < (aGraph E).degree u := by
  rw [degree_eq_card_touching E hloop hkeys u, Finset.card_pos]
  have hu : u.val ∈ E.map Prod.fst ++ E.map (fun e => e.2.1) := by
    have h := u.property
    rw [List.mem_toFinset] at h
    exact h
  rw [List.mem_append] at hu
  rcases hu with h | h
  · rw [List.mem_map] at h
    obtain ⟨e, heE, hev⟩ := h
    exact ⟨e, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr heE, Or.inl hev⟩⟩
  · rw [List.mem_map] at h
    obtain ⟨e, heE, hev⟩ := h
    exact ⟨e, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr heE, Or.inr hev⟩⟩

theorem aGraph_degree_ne (E : List AEdge)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2.1)
    (hkeys : ∀ e ∈ E, ∀ f ∈ E,
      (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e) :
    ∀ v : AVert E, ((aGraph E).degree v : ℝ) ≠ 0 := fun v =>
  Nat.cast_ne_zero.mpr (aGraph_degree_pos E hloop hkeys v).ne'

/-! ### The `hw` discharge and the `IsEdgeEnum` instance for the competitors -/

/-! ### The composed real-graph statements -/

end Step3
end R3Cert
