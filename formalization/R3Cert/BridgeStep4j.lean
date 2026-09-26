/-
  Bridge STEP 4j: ACYCLICITY of the address graph -- and the UNCONDITIONAL capstones.

  Every edge of `aGraph (realize t)` joins an address to a child address (`realize_shape`:
  the child is the parent with one index consed on).  A cycle would have a maximal-length
  address `u`; rotating the cycle to base it at `u`, both cycle-neighbors of `u` (its `snd`
  and `penultimate`, distinct by `IsCycle.snd_ne_penultimate`) lie weakly below `u`, so both
  edges descend from `u` -- but a descending edge determines the OTHER endpoint (`u.val`'s
  tail), so the two neighbors coincide.  Contradiction.

  With acyclicity discharged, the 4i statements become UNCONDITIONAL:

  * `pi_litHub'`             -- `per L(G_T) / prod deg = Ztot (litHub c ch)`;
  * `amplitude_bridge_real'` -- the hub ratio of the REAL Laplacian permanent ratios
                                converges to `exp (logPhi b) * rhoB^(Vb b)`.

  Together with the capstone `phi_le_one : logPhi b ≤ 0` (CI-green), the machine-checked
  chain now runs from Phi ≤ 1 in the Branch cavity model to the finite `per L / prod deg`
  objects of the Brualdi--Goldwasser program.  What remains is independent review (and the
  R4-R7 reduction layer, which stays at Python/paper level as documented).

  Genuine proofs (no `sorry`).  conjecture1_proved=False (review pending).
-/
import Mathlib
import R3Cert.BridgeStep4i

namespace R3Cert
namespace Step3

open RTree Filter Topology

/-- `snd` of a walk lies in its support. -/
theorem walk_snd_mem_support {V : Type} {G : SimpleGraph V} {a b : V} :
    ∀ p : G.Walk a b, p.snd ∈ p.support
  | SimpleGraph.Walk.nil => by
    rw [SimpleGraph.Walk.support_nil]
    exact List.mem_singleton.mpr rfl
  | SimpleGraph.Walk.cons h q => by
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.snd_cons]
    exact List.mem_cons.mpr (Or.inr q.start_mem_support)

/-- **The address graph of a realized tree is acyclic.** -/
theorem aGraph_realize_isAcyclic (t : RTree) : (aGraph (realize t)).IsAcyclic := by
  intro v c hc
  -- a maximal-length address on the cycle
  obtain ⟨u, humem, humax⟩ := Finset.exists_max_image c.support.toFinset
    (fun w => w.val.length) ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hu : u ∈ c.support := List.mem_toFinset.mp humem
  have hc' : (c.rotate u hu).IsCycle := hc.rotate hu
  have hnil : ¬(c.rotate u hu).Nil := hc'.not_nil
  -- the maximality transfers to the rotated support
  have hmax' : ∀ w ∈ (c.rotate u hu).support, w.val.length ≤ u.val.length := by
    intro w hw
    rw [SimpleGraph.Walk.support_eq_cons] at hw
    rcases List.mem_cons.mp hw with rfl | hwt
    · exact le_refl _
    · have hwc : w ∈ c.support.tail :=
        (SimpleGraph.Walk.support_rotate c u hu).mem_iff.mp hwt
      have hsub : w ∈ c.support := by
        rw [SimpleGraph.Walk.support_eq_cons]
        exact List.mem_cons.mpr (Or.inr hwc)
      exact humax w (List.mem_toFinset.mpr hsub)
  -- a weakly-lower neighbor of the maximum is its (unique) parent
  have hdown : ∀ w : AVert (realize t), (aGraph (realize t)).Adj u w →
      w.val.length ≤ u.val.length → ∃ j, u.val = j :: w.val := by
    intro w hadj hle
    rw [aGraph_adj] at hadj
    obtain ⟨-, e, heE, hor⟩ := hadj
    obtain ⟨j, hj⟩ := realize_shape t e heE
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      rw [h1] at hj
      rw [h2] at hj
      have := congrArg List.length hj
      simp only [List.length_cons] at this
      omega
    · rw [h1] at hj
      rw [h2] at hj
      exact ⟨j, hj⟩
  -- both cycle-neighbors of the maximum descend, hence coincide
  have hadj1 : (aGraph (realize t)).Adj u (c.rotate u hu).snd :=
    (c.rotate u hu).adj_snd hnil
  have hadj2 : (aGraph (realize t)).Adj (c.rotate u hu).penultimate u :=
    (c.rotate u hu).adj_penultimate hnil
  have hsnd_mem : (c.rotate u hu).snd ∈ (c.rotate u hu).support :=
    walk_snd_mem_support (c.rotate u hu)
  have hpen_mem : (c.rotate u hu).penultimate ∈ (c.rotate u hu).support :=
    (List.dropLast_sublist _).subset
      ((c.rotate u hu).penultimate_mem_dropLast_support hnil)
  obtain ⟨j1, hj1⟩ := hdown _ hadj1 (hmax' _ hsnd_mem)
  obtain ⟨j2, hj2⟩ := hdown _ hadj2.symm (hmax' _ hpen_mem)
  have heq : (c.rotate u hu).snd = (c.rotate u hu).penultimate := by
    apply Subtype.ext
    have h12 : (j1 :: (c.rotate u hu).snd.val) = j2 :: (c.rotate u hu).penultimate.val := by
      rw [← hj1, ← hj2]
    simp only [List.cons.injEq] at h12
    exact h12.2
  exact hc'.snd_ne_penultimate heq

/-! ### The unconditional capstones -/

/-- **THE REAL-GRAPH AMPLITUDE IDENTITY, unconditional.** -/
theorem pi_litHub' (c : ℕ) (ch : List Branch) :
    (lapl (aGraph (realize (litHub c ch)))).permanent
        / (∏ v, ((aGraph (realize (litHub c ch))).degree v : ℝ))
      = Ztot (litHub c ch) :=
  pi_litHub c ch (aGraph_realize_isAcyclic _)

/-- **THE AMPLITUDE BRIDGE ON THE REAL GRAPHS, unconditional**: the hub ratio of the real
    Laplacian permanent ratios converges to the DEC amplitude of the gadget branch. -/
theorem amplitude_bridge_real' (cH : ℕ) (arm b : Branch) :
    Tendsto (fun p : ℕ =>
        ((lapl (aGraph (realize (litHub cH (List.replicate p arm ++ [b]))))).permanent
          / (∏ v, ((aGraph (realize (litHub cH
              (List.replicate p arm ++ [b])))).degree v : ℝ)))
        / ((lapl (aGraph (realize (litHub cH (List.replicate p arm))))).permanent
          / (∏ v, ((aGraph (realize (litHub cH (List.replicate p arm)))).degree v : ℝ))))
      atTop (𝓝 (Real.exp (logPhi b) * rhoB ^ (Vb b))) :=
  amplitude_bridge_real cH arm b (fun _ => aGraph_realize_isAcyclic _)
    (fun _ => aGraph_realize_isAcyclic _)

end Step3
end R3Cert
