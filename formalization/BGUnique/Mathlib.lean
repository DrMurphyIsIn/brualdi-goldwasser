/-
  BGUnique.Mathlib -- the maximizers of the Brualdi-Goldwasser ratio, in Mathlib's own vocabulary.

  For a finite tree G (Mathlib `SimpleGraph`, `IsTree`) on n >= 4 vertices, the Laplacian ratio
      per (G.lapMatrix) / prod_v deg(v)
  is as large as possible among all trees on n vertices exactly when G is isomorphic to the realization
  of the explicit maximizer `bgMax n`, or, for n = 21 only, to the realization of `S21` (the subdivided
  star with 10 legs of length 2).  For n = 21 both trees attain the maximum and they are not isomorphic.
-/
import Mathlib
import R3Cert.BGStatement
import BGUnique.RerootIsoBridgeMain

namespace R3Cert
namespace BGUnique

open R3Cert.Step3 R3Cert.TreePaths R3Cert.TreeBridge R3Cert.BGStatement R3Cert.RerootIso R3Cert.AllUnique

/-- The realization of a `UTree` as a Mathlib graph (the graph behind `pi_utree`). -/
noncomputable abbrev real (t : UTree) : SimpleGraph (AVert (Step3.realize (dtRealize t))) :=
  aGraph (Step3.realize (dtRealize t))

/-- The Laplacian ratio of a finite graph, in Mathlib's vocabulary. -/
noncomputable def lapRatio {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical exact (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ))

theorem lapRatio_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    lapRatio G = (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) := by
  unfold lapRatio; congr 1 <;> congr 1 <;> try (ext; congr)
  all_goals (apply Subsingleton.elim)

/-- `G` maximizes the ratio among all finite trees with `n` vertices. -/
def IsBGMax (n : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W), H.IsTree → Fintype.card W = n → lapRatio H ≤ lapRatio G

theorem lapRatio_iso {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    lapRatio G = lapRatio H := by
  classical
  rw [lapRatio_eq, lapRatio_eq, lapMatrix_eq_lapl, lapMatrix_eq_lapl]; exact ratio_iso G H e

theorem lapRatio_real (t : UTree) : lapRatio (real t) = Aobj t := by
  classical
  rw [lapRatio_eq, lapMatrix_eq_lapl]
  convert pi_utree t

theorem real_isTree (t : UTree) (h2 : 2 ≤ usize t) : (real t).IsTree :=
  ⟨(addrGraphIso t h2).connected_iff.mp (addrGraph_connected t), aGraph_realize_isAcyclic _⟩

/-- Every tree on at least two vertices is isomorphic to the realization of a `UTree` of the same size. -/
theorem iso_real_of_tree {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) (h2 : 2 ≤ Fintype.card V) :
    ∃ t : UTree, usize t = Fintype.card V ∧ Nonempty (G ≃g real t) := by
  obtain ⟨t, ht, ⟨φ⟩⟩ := tree_iso G hG
  exact ⟨t, ht, ⟨φ.trans (addrGraphIso t (ht ▸ h2))⟩⟩

/-- On `UTree`s, maximizing `Aobj` is maximizing the Mathlib ratio of the realization. -/
theorem isBGMax_real_iff (n : ℕ) (h4 : 4 ≤ n) (t : UTree) (ht : usize t = n) :
    IsBGMax n (real t) ↔ ∀ t' : UTree, usize t' = n → Aobj t' ≤ Aobj t := by
  classical
  constructor
  · intro hmax t' ht'
    have h := hmax _ (real t') (real_isTree t' (by omega)) (by rw [card_verts_realize t' (by omega), ht'])
    rwa [lapRatio_real, lapRatio_real] at h
  · intro hmax W _ H hH hW
    obtain ⟨t', ht', ⟨φ⟩⟩ := iso_real_of_tree H hH (by omega)
    rw [lapRatio_iso H (real t') φ, lapRatio_real, lapRatio_real]
    exact hmax t' (ht'.trans hW)

theorem isBGMax_iso (n : ℕ) {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (G' : SimpleGraph W)
    (e : G ≃g G') :
    IsBGMax n G ↔ IsBGMax n G' := by
  unfold IsBGMax; rw [lapRatio_iso G G' e]

/-- **The maximizers, exactly, in Mathlib's vocabulary.**  A finite tree `G` on `n ≥ 4` vertices maximizes
    `per (G.lapMatrix) / ∏ deg` among all finite trees on `n` vertices if and only if it is isomorphic to the
    realization of `bgMax n`, or `n = 21` and it is isomorphic to the realization of `S21`. -/
theorem bg_maximizers_mathlib (n : ℕ) (h4 : 4 ≤ n) {V : Type} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (hV : Fintype.card V = n) :
    IsBGMax n G ↔
      Nonempty (G ≃g real (BGMaximizerAll.bgMax n)) ∨ (n = 21 ∧ Nonempty (G ≃g real S21)) := by
  classical
  obtain ⟨t, ht, ⟨φ⟩⟩ := iso_real_of_tree G hG (by omega)
  have htn : usize t = n := ht.trans hV
  have hsz := (BGMaximizerAll.bg_maximizer_all n h4).1
  rw [isBGMax_iso n G (real t) φ, isBGMax_real_iff n h4 t htn, bg_maximizers_exact n h4 t htn]
  constructor
  · rintro (h | ⟨h21, h⟩)
    · obtain ⟨ψ⟩ := (uiso_iff_aGraph t _ (by omega) (by omega)).mp ((rerootRel_iff_uiso _ _).mp h)
      exact Or.inl ⟨φ.trans ψ⟩
    · obtain ⟨ψ⟩ := (uiso_iff_aGraph t S21 (by omega) (by rw [usize_S21]; omega)).mp ((rerootRel_iff_uiso _ _).mp h)
      exact Or.inr ⟨h21, ⟨φ.trans ψ⟩⟩
  · rintro (ψ | ⟨h21, ψ⟩)
    swap
    · obtain ⟨ψ⟩ := ψ
      exact Or.inr ⟨h21, (rerootRel_iff_uiso _ _).mpr
        ((uiso_iff_aGraph t S21 (by omega) (by rw [usize_S21]; omega)).mpr ⟨φ.symm.trans ψ⟩)⟩
    · obtain ⟨ψ⟩ := ψ
      exact Or.inl ((rerootRel_iff_uiso _ _).mpr ((uiso_iff_aGraph t _ (by omega) (by omega)).mpr ⟨φ.symm.trans ψ⟩))

/-- **Uniqueness, n ≠ 21.**  Every maximizing tree on `n ≥ 4`, `n ≠ 21` vertices is isomorphic to the realization
    of `bgMax n`. -/
theorem bg_maximizer_unique_mathlib (n : ℕ) (h4 : 4 ≤ n) (h21 : n ≠ 21) {V : Type} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (hV : Fintype.card V = n) (hmax : IsBGMax n G) :
    Nonempty (G ≃g real (BGMaximizerAll.bgMax n)) := by
  rcases (bg_maximizers_mathlib n h4 G hG hV).mp hmax with h | ⟨h, _⟩
  · exact h
  · exact absurd h h21

/-- **n = 21: two non-isomorphic maximizers.**  Both realizations are trees on 21 vertices that maximize the
    ratio, and they are not isomorphic. -/
theorem bg_maximizers_21_mathlib :
    IsBGMax 21 (real (BGMaximizerAll.bgMax 21)) ∧ IsBGMax 21 (real S21) ∧
      IsEmpty (real (BGMaximizerAll.bgMax 21) ≃g real S21) := by
  classical
  have hsz := (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).1
  refine ⟨?_, ?_, ?_⟩
  · rw [isBGMax_real_iff 21 (by norm_num) _ hsz]
    exact (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).2
  · rw [isBGMax_real_iff 21 (by norm_num) _ usize_S21, Aobj_S21]
    exact (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).2
  · refine ⟨fun ψ => bgMax21_not_S21.1 ((rerootRel_iff_uiso _ _).mpr ?_)⟩
    exact (uiso_iff_aGraph _ S21 (by omega) (by rw [usize_S21]; omega)).mpr ⟨ψ⟩

end BGUnique
end R3Cert
