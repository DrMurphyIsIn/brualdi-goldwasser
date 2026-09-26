/-
  Bridge STEP 4e (part 1): the DEGREE-COUNT lemma -- the interface between the `aGraph`
  degrees and the raw edge list.

  `isEdgeEnum_liftEdges`'s remaining hypothesis `hw` needs the `SimpleGraph.degree` of each
  vertex of the realized competitor tree.  This file proves the generic counting identity:

    `degree_eq_card_touching` --
      `(aGraph E).degree u = #(E.toFinset.filter (fun e => e.1 = u.val ∨ e.2.1 = u.val))`

  i.e. the graph degree is the number of edges touching the address, provided the list has no
  loops (`hloop`) and unordered keys are unique (`hkeys`) -- both already discharged for
  realized trees by `BridgeStep3f`.  Proof: `Finset.card_bij` from touching edges to
  neighbors, sending an edge to its other endpoint; injectivity is key-uniqueness,
  surjectivity unpacks `HasKey`.  No choice functions -- the bijection is the explicit
  `dite` on the edge orientation.

  Remaining for item (iii): the construction-degree computation for `litHub` realizations
  (touching count at each address = the built-in `d`), then the final composition.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep3f

namespace R3Cert
namespace Step3

/-- **The degree of an address vertex is the number of touching edges.** -/
theorem degree_eq_card_touching (E : List AEdge)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2.1)
    (hkeys : ∀ e ∈ E, ∀ f ∈ E,
      (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e)
    (u : AVert E) :
    (aGraph E).degree u
      = (E.toFinset.filter (fun e => e.1 = u.val ∨ e.2.1 = u.val)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine (Finset.card_bij
    (fun e he => if h : e.1 = u.val
      then (⟨e.2.1, snd_mem_vertsOf (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)⟩ :
        AVert E)
      else ⟨e.1, fst_mem_vertsOf (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)⟩)
    ?_ ?_ ?_).symm
  · -- maps into the neighbor set
    intro e he
    have heE : e ∈ E := List.mem_toFinset.mp (Finset.mem_filter.mp he).1
    have htouch := (Finset.mem_filter.mp he).2
    rw [SimpleGraph.mem_neighborFinset, aGraph_adj]
    by_cases h : e.1 = u.val
    · rw [dif_pos h]
      refine ⟨?_, ⟨e, heE, Or.inl ⟨h, rfl⟩⟩⟩
      intro hcontra
      apply hloop e heE
      rw [h]
      exact congrArg Subtype.val hcontra
    · have h2 : e.2.1 = u.val := htouch.resolve_left h
      rw [dif_neg h]
      refine ⟨?_, ⟨e, heE, Or.inr ⟨rfl, h2⟩⟩⟩
      intro hcontra
      exact h (congrArg Subtype.val hcontra).symm
  · -- injective: the key determines the edge
    intro e he f hf heq
    have heE : e ∈ E := List.mem_toFinset.mp (Finset.mem_filter.mp he).1
    have hfE : f ∈ E := List.mem_toFinset.mp (Finset.mem_filter.mp hf).1
    by_cases h1 : e.1 = u.val <;> by_cases h2 : f.1 = u.val
    · rw [dif_pos h1, dif_pos h2] at heq
      have hval : e.2.1 = f.2.1 := congrArg Subtype.val heq
      exact (hkeys e heE f hfE (Or.inl ⟨h2.trans h1.symm, hval.symm⟩)).symm
    · have hf2 : f.2.1 = u.val := ((Finset.mem_filter.mp hf).2).resolve_left h2
      rw [dif_pos h1, dif_neg h2] at heq
      have hval : e.2.1 = f.1 := congrArg Subtype.val heq
      exact (hkeys e heE f hfE (Or.inr ⟨hval.symm, hf2.trans h1.symm⟩)).symm
    · have he2 : e.2.1 = u.val := ((Finset.mem_filter.mp he).2).resolve_left h1
      rw [dif_neg h1, dif_pos h2] at heq
      have hval : e.1 = f.2.1 := congrArg Subtype.val heq
      exact hkeys f hfE e heE (Or.inr ⟨hval, he2.trans h2.symm⟩)
    · have he2 : e.2.1 = u.val := ((Finset.mem_filter.mp he).2).resolve_left h1
      have hf2 : f.2.1 = u.val := ((Finset.mem_filter.mp hf).2).resolve_left h2
      rw [dif_neg h1, dif_neg h2] at heq
      have hval : e.1 = f.1 := congrArg Subtype.val heq
      exact (hkeys e heE f hfE (Or.inl ⟨hval.symm, hf2.trans he2.symm⟩)).symm
  · -- surjective: every neighbor comes from a touching edge
    intro v hv
    have hadj := ((aGraph E).mem_neighborFinset u v).mp hv
    have hne : u.val ≠ v.val := fun hval => hadj.ne (Subtype.ext hval)
    rw [aGraph_adj] at hadj
    obtain ⟨-, ec, hecE, hor⟩ := hadj
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨ec, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hecE, Or.inl h1⟩, ?_⟩
      rw [dif_pos h1]
      exact Subtype.ext h2
    · refine ⟨ec, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hecE, Or.inr h2⟩, ?_⟩
      have hne1 : ¬ ec.1 = u.val := fun hh => hne ((hh.symm.trans h1))
      rw [dif_neg hne1]
      exact Subtype.ext h1

end Step3
end R3Cert
