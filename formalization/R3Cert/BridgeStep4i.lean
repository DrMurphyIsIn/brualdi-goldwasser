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

theorem childCount_litHub (c : ℕ) (ch : List Branch) :
    childCount (litHub c ch) = c + ch.length := by
  rw [litHub, childCount, List.length_append, List.length_replicate, litChildren_length]

/-- **`hw` for the literal hub realizations**: every lifted weight is the reciprocal degree
    product of the address graph. -/
theorem litHub_hw (c : ℕ) (ch : List Branch) :
    ∀ q ∈ liftEdges (realize (litHub c ch)), q.2.2
      = 1 / (((aGraph (realize (litHub c ch))).degree q.1 : ℝ)
          * ((aGraph (realize (litHub c ch))).degree q.2.1 : ℝ)) := by
  intro q hq
  obtain ⟨e, heE, h1, h2, h3⟩ := of_mem_liftEdges hq
  have hdeg1 : (aGraph (realize (litHub c ch))).degree q.1
      = (realize (litHub c ch)).countP (touchB e.1) := by
    rw [degree_eq_card_touching _ (realize_hloop _) (realize_keys _),
      card_touching_eq_countP _ (realize_nodup _), h1]
  have hdeg2 : (aGraph (realize (litHub c ch))).degree q.2.1
      = (realize (litHub c ch)).countP (touchB e.2.1) := by
    rw [degree_eq_card_touching _ (realize_hloop _) (realize_keys _),
      card_touching_eq_countP _ (realize_nodup _), h2]
  rw [h3, hdeg1, hdeg2]
  exact realize_weights (litHub c ch) (c + ch.length) (litHub_good c ch)
    (childCount_litHub c ch) e heE

/-- The realized competitor trees are `IsEdgeEnum`s of their address graphs. -/
theorem litHub_isEdgeEnum (c : ℕ) (ch : List Branch) :
    IsEdgeEnum (aGraph (realize (litHub c ch))) (liftEdges (realize (litHub c ch))) :=
  isEdgeEnum_liftEdges _ (realize_nodup _) (realize_hloop _) (realize_keys _) (litHub_hw c ch)

/-! ### The composed real-graph statements -/

/-- **THE REAL-GRAPH AMPLITUDE IDENTITY**: the Laplacian permanent ratio of the realized
    competitor graph IS the raw matching partition function of the literal hub. -/
theorem pi_litHub (c : ℕ) (ch : List Branch)
    (hac : (aGraph (realize (litHub c ch))).IsAcyclic) :
    (lapl (aGraph (realize (litHub c ch)))).permanent
        / (∏ v, ((aGraph (realize (litHub c ch))).degree v : ℝ))
      = Ztot (litHub c ch) := by
  rw [pi_eq_msum _ hac (aGraph_degree_ne _ (realize_hloop _) (realize_keys _))
      (litHub_isEdgeEnum c ch),
    msum_liftEdges, ← Ztot_eq_msum]

/-- **THE AMPLITUDE BRIDGE ON THE REAL GRAPHS**: the hub ratio of Laplacian permanent ratios
    converges to `exp (logPhi b) * rhoB^(Vb b)` -- the DEC amplitude of the gadget branch.
    Acyclicity of the address graphs is the one remaining structural hypothesis. -/
theorem amplitude_bridge_real (cH : ℕ) (arm b : Branch)
    (hacg : ∀ p : ℕ,
      (aGraph (realize (litHub cH (List.replicate p arm ++ [b])))).IsAcyclic)
    (hacb : ∀ p : ℕ,
      (aGraph (realize (litHub cH (List.replicate p arm)))).IsAcyclic) :
    Tendsto (fun p : ℕ =>
        ((lapl (aGraph (realize (litHub cH (List.replicate p arm ++ [b]))))).permanent
          / (∏ v, ((aGraph (realize (litHub cH
              (List.replicate p arm ++ [b])))).degree v : ℝ)))
        / ((lapl (aGraph (realize (litHub cH (List.replicate p arm))))).permanent
          / (∏ v, ((aGraph (realize (litHub cH (List.replicate p arm)))).degree v : ℝ))))
      atTop (𝓝 (Real.exp (logPhi b) * rhoB ^ (Vb b))) := by
  refine Tendsto.congr (fun p => ?_) (amplitude_bridge_logPhi cH arm b)
  rw [pi_litHub _ _ (hacg p), pi_litHub _ _ (hacb p)]

end Step3
end R3Cert
