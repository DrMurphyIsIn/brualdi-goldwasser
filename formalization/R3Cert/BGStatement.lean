/-
  R3Cert.BGStatement -- the Brualdi-Goldwasser theorem in Mathlib's own vocabulary.

  `BGMaximizerAll.bg_maximizer_all` is stated for the formalization's rooted trees (`UTree`) and their
  matching sum (`Aobj`).  This file restates it for an arbitrary finite tree `G : SimpleGraph V` in
  Mathlib's sense (`G.IsTree`), with Mathlib's Laplacian `G.lapMatrix ℝ`, Mathlib's `Matrix.permanent`
  and Mathlib's `G.degree`:

    * `bg_maximum_le`: every tree on `n ≥ 4` vertices has `per L / ∏ deg ≤ F (bgChildren n)`;
    * `bg_maximum_attained`: some tree on `Fin n` attains it;

  so `F (bgChildren n)` is exactly the maximum.  `F` (in `BGSpiderOpt`) is the closed-form value of the
  spider whose centre carries the children `bgChildren n` (cherries and arms).

  Ingredients: `TreePaths.tree_iso` (every tree is a `UTree`), `TreeBridge.addrGraphIso` (its path graph
  is the realized graph), `pi_utree` (the realized graph's ratio is `Aobj`), and `ratio_iso` below (the
  ratio is invariant under graph isomorphism).
  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGMaximizerAll
import R3Cert.TreeBridge
import R3Cert.BGAnswer

namespace R3Cert
namespace BGStatement

open Step3 TreePaths TreeBridge BGSpiderOpt BGSpiderRule BGSpiderTable

/-! ### The Laplacian ratio is an isomorphism invariant -/

theorem permanent_submatrix_equiv {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (M : Matrix W W ℝ) (e : V ≃ W) : (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ (fun σ => ?_)
  simp only [Matrix.submatrix_apply]
  refine Fintype.prod_equiv e _ _ (fun i => ?_)
  simp [Equiv.permCongr_apply]

theorem lapMatrix_eq_lapl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.lapMatrix ℝ = lapl G := by
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, lapl]
  by_cases h : i = j
  · subst h; simp
  · by_cases ha : G.Adj i j <;> simp [h, ha]

/-- Isomorphic graphs have the same Laplacian ratio. -/
theorem ratio_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] (e : G ≃g H) :
    (lapl G).permanent / (∏ v, (G.degree v : ℝ)) = (lapl H).permanent / (∏ w, (H.degree w : ℝ)) := by
  have hL : lapl G = (lapl H).submatrix e e := by
    ext i j
    simp only [lapl, Matrix.submatrix_apply, e.injective.eq_iff, e.map_adj_iff]
    split_ifs with h
    · subst h; simp [e.degree_eq]
    · rfl
    · rfl
  have hD : ∏ v, (G.degree v : ℝ) = ∏ w, (H.degree w : ℝ) :=
    Fintype.prod_equiv e.toEquiv _ _ (fun v => by simp [e.degree_eq])
  rw [hL, show (lapl H).submatrix e e = (lapl H).submatrix e.toEquiv e.toEquiv from rfl,
    permanent_submatrix_equiv, hD]

/-! ### Trees -/

/-- Every tree with at least two vertices has the ratio of a `UTree` of the same size. -/
theorem ratio_tree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (h2 : 2 ≤ Fintype.card V) :
    ∃ t : UTree, usize t = Fintype.card V ∧
      (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) = Aobj t := by
  obtain ⟨t, ht, ⟨φ⟩⟩ := tree_iso G hG
  refine ⟨t, ht, ?_⟩
  rw [lapMatrix_eq_lapl, ratio_iso G _ (φ.trans (addrGraphIso t (ht ▸ h2))), pi_utree]

theorem bgMax_eq (n : ℕ) : BGMaximizerAll.bgMax n = spiderU (bgChildren n) := by
  unfold BGMaximizerAll.bgMax bgChildren; split_ifs <;> rfl

/-- **Brualdi-Goldwasser, upper bound.** Every tree `G` on `n ≥ 4` vertices satisfies
    `per L(G) / ∏ deg ≤ F (bgChildren n)`. -/
theorem bg_maximum_le (n : ℕ) (h4 : 4 ≤ n) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (hV : Fintype.card V = n) :
    (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) ≤ (F (bgChildren n) : ℝ) := by
  obtain ⟨t, ht, hEq⟩ := ratio_tree G hG (by omega)
  rw [hEq, ← Aobj_spiderU, ← bgMax_eq]
  exact (BGMaximizerAll.bg_maximizer_all n h4).2 t (ht.trans hV)

/-! ### Attainment -/

theorem addrGraph_connected (t : UTree) : (addrGraph t).Connected := by
  have root : ∀ q : List ℕ, ∀ hq : q ∈ paths t,
      (addrGraph t).Reachable ⟨[], nil_mem_paths t⟩ ⟨q, hq⟩ := by
    intro q
    induction q using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton q j ih =>
      intro hq
      have hq' : q ∈ paths t := mem_paths_of_append t q [j] hq
      exact (ih hq').trans (SimpleGraph.Adj.reachable (Or.inl ⟨j, rfl⟩))
  haveI : Nonempty (VP t) := ⟨⟨[], nil_mem_paths t⟩⟩
  exact SimpleGraph.Connected.mk (fun x y => ((root x.1 x.2).symm.trans (root y.1 y.2)))

theorem card_verts_realize (t : UTree) (ht : 2 ≤ usize t) :
    Fintype.card (AVert (Step3.realize (dtRealize t))) = usize t := by
  rw [Fintype.card_coe]
  have : (vertsOf (Step3.realize (dtRealize t))).toFinset = (paths t).toFinset.image List.reverse := by
    ext a
    rw [mem_verts_realize t ht, Finset.mem_image]
    constructor
    · intro h; exact ⟨a.reverse, List.mem_toFinset.mpr h, List.reverse_reverse a⟩
    · rintro ⟨q, hq, rfl⟩; simpa using List.mem_toFinset.mp hq
  rw [this, Finset.card_image_of_injective _ List.reverse_injective,
    List.toFinset_card_of_nodup (nodup_paths t), length_paths]

/-- **Brualdi-Goldwasser, attainment.** Some tree on `Fin n` has ratio exactly `F (bgChildren n)`. -/
theorem bg_maximum_attained (n : ℕ) (h4 : 4 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.IsTree ∧
      (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) = (F (bgChildren n) : ℝ) := by
  obtain ⟨hsize, _⟩ := BGMaximizerAll.bg_maximizer_all n h4
  set t := BGMaximizerAll.bgMax n with htdef
  have h2 : 2 ≤ usize t := by omega
  set E := Step3.realize (dtRealize t)
  have hcard : Fintype.card (AVert E) = n := by rw [card_verts_realize t h2, hsize]
  let f : Fin n ≃ AVert E := (Fintype.equivFinOfCardEq hcard).symm
  let G : SimpleGraph (Fin n) := (aGraph E).comap f
  let ι : G ≃g aGraph E := SimpleGraph.Iso.comap f (aGraph E)
  classical
  refine ⟨G, inferInstance, ?_, ?_⟩
  · rw [ι.isTree_iff]
    refine ⟨?_, aGraph_realize_isAcyclic _⟩
    exact (addrGraphIso t h2).connected_iff.mp (addrGraph_connected t)
  · rw [lapMatrix_eq_lapl, ratio_iso G (aGraph E) ι, pi_utree, htdef, bgMax_eq, Aobj_spiderU]

end BGStatement
end R3Cert
