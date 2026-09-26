/-
  The crux of H1: an acyclic graph forces every edge-supported permutation to be an involution.

  If σ maps each vertex to itself or a neighbour and G is acyclic, then σ is an involution.  Proof: if not,
  some x has σ(σx) ≠ x; its σ-orbit has minimal period p ≥ 3; iterating σ builds a closed walk
  x → σx → ⋯ → σ^p x = x whose tail (σx → ⋯ → x) is a path (orbit vertices distinct,
  `iterate_injOn_Iio_minimalPeriod`) and whose length is p ≥ 3, so it is a cycle
  (`isCycle_iff_isPath_tail_and_le_length`), contradicting `IsAcyclic`.
-/
import Mathlib

namespace R3Cert

open Equiv Function SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (σ : Perm V) (x : V)

/-- Walk along the forward σ-orbit of `x`, of length `len` (built by `concat`, base fixed at `x`). -/
def owalk (hb : ∀ n : ℕ, G.Adj (σ^[n] x) (σ (σ^[n] x))) : (len : ℕ) → G.Walk x (σ^[len] x)
  | 0 => Walk.nil
  | len + 1 => (owalk hb len).concat (by rw [Function.iterate_succ_apply']; exact hb len)

lemma owalk_length (hb : ∀ n : ℕ, G.Adj (σ^[n] x) (σ (σ^[n] x))) (len : ℕ) :
    (owalk G σ x hb len).length = len := by
  induction len with
  | zero => rfl
  | succ n ih => rw [owalk, Walk.length_concat, ih]

lemma owalk_support (hb : ∀ n : ℕ, G.Adj (σ^[n] x) (σ (σ^[n] x))) (len : ℕ) :
    (owalk G σ x hb len).support = (List.range (len + 1)).map (fun i => σ^[i] x) := by
  induction len with
  | zero => simp [owalk]
  | succ n ih =>
    have hr : (List.range (n + 1 + 1)).map (fun i => σ^[i] x)
        = (List.range (n + 1)).map (fun i => σ^[i] x) ++ [σ^[n + 1] x] := by
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [owalk, Walk.support_concat, ih, hr]

end R3Cert

namespace R3Cert
open Equiv Function SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- σ maps non-fixed points to non-fixed points, so every step along the orbit of a non-fixed point is an
    edge (via edge-support). -/
lemma orbit_nonfixed {σ : Perm V} {x : V} (hx : σ x ≠ x) (n : ℕ) : σ (σ^[n] x) ≠ σ^[n] x := by
  intro hfix
  apply hx
  have h1 : σ^[n] (σ x) = σ^[n] x := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hfix]
  exact (σ.injective.iterate n) h1

/-- **The crux.** On an acyclic graph, an edge-supported permutation is an involution. -/
theorem acyclic_edgeSupported_involutive {G : SimpleGraph V} {σ : Perm V}
    (hG : G.IsAcyclic) (hE : ∀ v, σ v = v ∨ G.Adj v (σ v)) : Function.Involutive σ := by
  intro x
  by_contra hxx
  have hx : σ x ≠ x := by intro h; apply hxx; rw [h, h]
  have hσx : σ (σ x) ≠ σ x := fun h => hx (σ.injective h)
  have hstep : ∀ v : V, σ v ≠ v → G.Adj v (σ v) := fun v hv => (hE v).resolve_left hv
  have hb0 : G.Adj x (σ x) := hstep x hx
  have hbσ : ∀ n : ℕ, G.Adj (σ^[n] (σ x)) (σ (σ^[n] (σ x))) := fun n => hstep _ (orbit_nonfixed hσx n)
  have hxper : x ∈ Function.periodicPts σ := σ.injective.mem_periodicPts x
  set p := Function.minimalPeriod σ x with hp
  have hp0 : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hxper
  have hend : σ^[p] x = x := Function.iterate_minimalPeriod
  have hp1 : p ≠ 1 := by
    intro h
    have h2 : σ^[1] x = x := h ▸ hend
    rw [Function.iterate_one] at h2; exact hx h2
  have hp2 : p ≠ 2 := by
    intro h
    have h2 : σ^[2] x = x := h ▸ hend
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply] at h2
    simp only [Function.iterate_one] at h2; exact hxx h2
  have hp3 : 3 ≤ p := by omega
  have hend' : σ^[p - 1] (σ x) = x := by
    have h1 : σ^[p - 1] (σ x) = σ^[p] x := by
      rw [← Function.iterate_succ_apply]; congr 1; omega
    rw [h1, hend]
  -- copy preserves IsPath (support is unchanged)
  have hcopy : ∀ {a b a' b' : V} (w : G.Walk a b) (hu : a = a') (hv : b = b'),
      w.IsPath → (w.copy hu hv).IsPath := by
    intro a b a' b' w hu hv hw
    rw [SimpleGraph.Walk.isPath_def, Walk.support_copy]
    rwa [SimpleGraph.Walk.isPath_def] at hw
  -- tail walk σx → x of length p-1, and the closed walk W : x → x of length p
  let tail : G.Walk (σ x) x := (owalk G σ (σ x) hbσ (p - 1)).copy rfl hend'
  let W : G.Walk x x := Walk.cons hb0 tail
  refine hG W ?_
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, ?_⟩
  · have hper : Function.minimalPeriod σ (σ x) = p := Function.minimalPeriod_apply hxper
    have hinj : Set.InjOn (fun i => σ^[i] (σ x)) (Set.Iio p) := by
      rw [← hper]; exact Function.iterate_injOn_Iio_minimalPeriod
    have htp : tail.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      have hsupp : tail.support = (List.range p).map (fun i => σ^[i] (σ x)) := by
        show ((owalk G σ (σ x) hbσ (p - 1)).copy rfl hend').support = _
        rw [Walk.support_copy, owalk_support, Nat.sub_add_cancel hp0]
      rw [hsupp]
      exact List.Nodup.map_on
        (fun i hi j hj hij => hinj (Set.mem_Iio.mpr (List.mem_range.mp hi))
          (Set.mem_Iio.mpr (List.mem_range.mp hj)) hij)
        List.nodup_range
    show (Walk.cons hb0 tail).tail.IsPath
    rw [Walk.tail_cons hb0 tail]
    exact hcopy tail _ _ htp
  · show 3 ≤ W.length
    have htl : tail.length = p - 1 := by
      show ((owalk G σ (σ x) hbσ (p - 1)).copy rfl hend').length = p - 1
      rw [Walk.length_copy, owalk_length]
    have hW : W.length = p := by
      show (Walk.cons hb0 tail).length = p
      rw [Walk.length_cons, htl]; omega
    omega

end R3Cert
