/-
  Bridge STEP 3b: the SEMANTICS of `msum` — it is the sum over all matchings.

  `Step3.msum` was proven equal to `RTree.Ztot` (BridgeStep3, CI-green) through its include/exclude
  recursion.  This file gives `msum` its combinatorial meaning: `msum E = Σ_{M} Π_{e ∈ M} w_e`, the
  sum over ALL vertex-disjoint sub-lists (matchings) `M` of the edge list `E`.  This is the glue
  toward `Matching.lean`'s H2a involution sum (each edge-supported involution of an acyclic graph is
  exactly such a matching).

  * `subm E` — direct enumeration of the matchings of `E`, by the SAME include/exclude recursion;
  * `msum_eq_sum_subm` — `msum E = Σ_{M ∈ subm E} wprod M` (structural, mirrors the recursion);
  * `mem_subm` — `M ∈ subm E ↔ M <+ E ∧ matchQ M` (the characterization: matchings = vertex-disjoint
    sublists).

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.BridgeStep3

namespace R3Cert
namespace Step3

variable {V : Type} [DecidableEq V]

/-- `f` is compatible with (vertex-disjoint from) `e`. -/
def compatQ (e f : V × V × ℝ) : Bool := ! conflict e.1 e.2.1 f

/-- `M` is pairwise vertex-disjoint (a matching), as a Bool. -/
def matchQ : List (V × V × ℝ) → Bool
  | [] => true
  | e :: M => M.all (compatQ e) && matchQ M

/-- The weight product of a matching. -/
def wprod (M : List (V × V × ℝ)) : ℝ := (M.map (fun e => e.2.2)).prod

@[simp] theorem wprod_nil : wprod ([] : List (V × V × ℝ)) = 1 := rfl

theorem wprod_cons (e : V × V × ℝ) (M : List (V × V × ℝ)) :
    wprod (e :: M) = e.2.2 * wprod M := by
  simp [wprod]

/-- **Direct enumeration of the matchings of `E`** by include/exclude of the head edge. -/
def subm : List (V × V × ℝ) → List (List (V × V × ℝ))
  | [] => [[]]
  | e :: rest => subm rest ++ (subm (rest.filter (compatQ e))).map (e :: ·)
termination_by E => E.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

@[simp] theorem subm_nil : subm ([] : List (V × V × ℝ)) = [[]] := by rw [subm]

theorem subm_cons (e : V × V × ℝ) (rest : List (V × V × ℝ)) :
    subm (e :: rest) = subm rest ++ (subm (rest.filter (compatQ e))).map (e :: ·) := by
  rw [subm]

/-- **`msum` is the total weight of the matching enumeration.** -/
theorem msum_eq_sum_subm : ∀ E : List (V × V × ℝ), msum E = ((subm E).map wprod).sum
  | [] => by simp
  | e :: rest => by
    rw [msum_cons, subm_cons,
      show (fun f => ! conflict e.1 e.2.1 f) = compatQ e from rfl,
      List.map_append, List.sum_append,
      msum_eq_sum_subm rest, msum_eq_sum_subm (rest.filter (compatQ e))]
    congr 1
    rw [List.map_map]
    have hcomp : (wprod ∘ (e :: ·)) = fun M => e.2.2 * wprod M := by
      funext M; exact wprod_cons e M
    rw [hcomp, ← List.sum_map_mul_left]
termination_by E => E.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

/-- **The characterization: the matchings of `E` are exactly its vertex-disjoint sublists.** -/
theorem mem_subm : ∀ (E M : List (V × V × ℝ)), M ∈ subm E ↔ M.Sublist E ∧ matchQ M = true
  | [], M => by
    simp only [subm_nil, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨List.Sublist.refl _, rfl⟩
    · rintro ⟨hs, _⟩; exact List.sublist_nil.mp hs
  | e :: rest, M => by
    rw [subm_cons, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨hs, hq⟩ := (mem_subm rest M).mp h
        exact ⟨hs.trans (List.sublist_cons_self e rest), hq⟩
      · obtain ⟨M', hM', rfl⟩ := List.mem_map.mp h
        obtain ⟨hs, hq⟩ := (mem_subm (rest.filter (compatQ e)) M').mp hM'
        refine ⟨List.cons_sublist_cons.mpr (hs.trans List.filter_sublist), ?_⟩
        rw [matchQ]
        simp only [Bool.and_eq_true]
        refine ⟨List.all_eq_true.mpr ?_, hq⟩
        intro f hf
        exact List.of_mem_filter (hs.subset hf)
    · rintro ⟨hs, hq⟩
      rcases List.sublist_cons_iff.mp hs with h | ⟨M', rfl, hM'⟩
      · exact Or.inl ((mem_subm rest M).mpr ⟨h, hq⟩)
      · rw [matchQ] at hq
        simp only [Bool.and_eq_true] at hq
        obtain ⟨hall, hq'⟩ := hq
        refine Or.inr (List.mem_map.mpr ⟨M', (mem_subm _ M').mpr ⟨?_, hq'⟩, rfl⟩)
        have hMf : M'.filter (compatQ e) = M' :=
          List.filter_eq_self.mpr (List.all_eq_true.mp hall)
        exact hMf ▸ (hM'.filter (compatQ e))
termination_by E _ => E.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

end Step3
end R3Cert
