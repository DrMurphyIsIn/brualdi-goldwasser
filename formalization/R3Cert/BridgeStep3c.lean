/-
  Bridge STEP 3c: `msum` as a `Finset` sum — the shape needed to meet `Matching.lean`'s H2a.

  H2a's right side is a `Finset.sum` over edge-supported involutions; `msum` is a `List`-level
  recursion.  This file crosses that shape gap:

  * `subm_nodup` — for a duplicate-free edge list the matching enumeration has no duplicates
    (each matching counted exactly once);
  * `msum_eq_finset_sum` — `msum E = ∑_{M ∈ (subm E).toFinset} wprod M`.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.BridgeStep3b

namespace R3Cert
namespace Step3

variable {V : Type} [DecidableEq V]

/-- Members of `subm E` are sublists of `E`. -/
theorem subm_sublist {E M : List (V × V × ℝ)} (h : M ∈ subm E) : M.Sublist E :=
  ((mem_subm E M).mp h).1

/-- **The matching enumeration of a duplicate-free edge list is duplicate-free.** -/
theorem subm_nodup : ∀ E : List (V × V × ℝ), E.Nodup → (subm E).Nodup
  | [], _ => by simp
  | e :: rest, hE => by
    obtain ⟨heNot, hrest⟩ := List.nodup_cons.mp hE
    rw [subm_cons]
    refine List.Nodup.append (subm_nodup rest hrest) ?_ ?_
    · exact ((subm_nodup (rest.filter (compatQ e)) (hrest.filter _)).map
        (fun M M' h => by simpa using h))
    · intro M hM1 hM2
      obtain ⟨M', _, rfl⟩ := List.mem_map.mp hM2
      have hsub : (e :: M').Sublist rest := subm_sublist hM1
      exact heNot (hsub.subset (by simp : e ∈ e :: M'))
termination_by E _ => E.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

/-- **`msum` as a `Finset` sum over the (duplicate-free) matching enumeration.** -/
theorem msum_eq_finset_sum (E : List (V × V × ℝ)) (hE : E.Nodup) :
    msum E = ∑ M ∈ (subm E).toFinset, wprod M := by
  rw [msum_eq_sum_subm]
  exact (List.sum_toFinset _ (subm_nodup E hE)).symm

end Step3
end R3Cert
