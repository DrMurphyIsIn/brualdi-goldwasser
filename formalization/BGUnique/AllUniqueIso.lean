import Mathlib
import BGUnique.AllUnique
import BGUnique.RerootIsoComplete

/-!
The maximizers, up to isomorphism of unrooted trees (`UIso`: an isomorphism of the trees' graphs,
`SimpleGraph.Iso`).  `RerootRel` is exactly `UIso` (`rerootRel_iff_uiso`), so the exact
characterization transfers.
-/

namespace R3Cert
namespace AllUniqueIso

open R3Cert.Step3 R3Cert.RerootIso R3Cert.AllUnique

/-- `UIso` is an equivalence relation. -/
theorem uiso_equivalence : Equivalence UIso :=
  ⟨uiso_refl, fun h => uiso_of_rerootRel (RerootEquiv.symm (rerootRel_of_uiso h)), uiso_trans⟩

/-- **Exact characterization of the maximizers, every `n ≥ 4`, up to isomorphism.**  A tree on `n`
    vertices maximizes `Aobj` (the Laplacian ratio) iff it is isomorphic to `bgMax n`, or `n = 21` and
    it is isomorphic to the subdivided star `C^10`. -/
theorem bg_maximizers_exact_iso (n : ℕ) (h4 : 4 ≤ n) (t : UTree) (ht : usize t = n) :
    (∀ t' : UTree, usize t' = n → Aobj t' ≤ Aobj t) ↔
      (UIso t (BGMaximizerAll.bgMax n) ∨ (n = 21 ∧ UIso t S21)) := by
  rw [bg_maximizers_exact n h4 t ht, rerootRel_iff_uiso, rerootRel_iff_uiso]

/-- **Uniqueness up to isomorphism, every `n ≥ 4`, `n ≠ 21`.** -/
theorem bg_maximizer_unique_all_iso (t : UTree) (h4 : 4 ≤ usize t) (h21 : usize t ≠ 21)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    UIso t (BGMaximizerAll.bgMax (usize t)) :=
  uiso_of_rerootRel (bg_maximizer_unique_all t h4 h21 hmax)

/-- **The maximizers on 21 vertices, up to isomorphism**: `T(3,3,3) = bgMax 21` or `C^10`. -/
theorem bg_maximizers_21_iso (t : UTree) (h : usize t = 21)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    UIso t (BGMaximizerAll.bgMax 21) ∨ UIso t S21 :=
  (bg_maximizers_21 t h hmax).imp uiso_of_rerootRel uiso_of_rerootRel

/-- `T(3,3,3)` and `C^10` are not isomorphic. -/
theorem bgMax21_not_uiso_S21 : ¬ UIso (BGMaximizerAll.bgMax 21) S21 :=
  fun h => bgMax21_not_S21.1 (rerootRel_of_uiso h)

end AllUniqueIso
end R3Cert
