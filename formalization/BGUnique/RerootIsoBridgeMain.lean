import Mathlib
import BGUnique.RerootIsoBridge
import BGUnique.AllUniqueIso

/-!
`G t` is a tree on `usize t` vertices, and (for `usize t ≥ 2`) it is the realized graph
`aGraph (realize (dtRealize t))` whose Laplacian permanent ratio is `Aobj t` (`pi_utree`).  So `UIso`
is isomorphism of the very graphs on which the Brualdi-Goldwasser ratio is computed, and the
maximizer characterization holds verbatim for those graphs.
-/

namespace R3Cert
namespace RerootIso

open R3Cert.Step3

theorem valid_node_nil {p : List ℕ} (h : Valid (UTree.node []) p) : p = [] := by
  cases p with
  | nil => rfl
  | cons i q => obtain ⟨hi, -⟩ := valid_cons.mp h; simp at hi

theorem G_nil_eq_bot : G (UTree.node []) = ⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  intro h
  have hu := valid_node_nil u.2
  have hv := valid_node_nil v.2
  change ladj u.1 v.1 at h
  rw [hu, hv] at h
  exact ladj_irrefl _ h

/-- **`G t` is acyclic.** -/
theorem G_isAcyclic (t : UTree) : (G t).IsAcyclic := by
  obtain ⟨cs⟩ := t
  by_cases hne : cs = []
  · subst hne; rw [G_nil_eq_bot]; exact SimpleGraph.isAcyclic_bot
  · exact (gIsoA cs hne).isAcyclic_iff.mpr (aGraph_realize_isAcyclic _)

/-- **`G t` is a tree.** -/
theorem G_isTree (t : UTree) : (G t).IsTree := ⟨G_connected t, G_isAcyclic t⟩

theorem ne_nil_of_usize {cs : List UTree} (h : 2 ≤ usize (UTree.node cs)) : cs ≠ [] := by
  rintro rfl; rw [usize_node, usizeList_nil] at h; omega

/-- **`G t` is the realized graph**, for `usize t ≥ 2`. -/
theorem G_iso_aGraph (t : UTree) (h : 2 ≤ usize t) :
    Nonempty (G t ≃g aGraph (Step3.realize (dtRealize t))) := by
  obtain ⟨cs⟩ := t
  exact ⟨gIsoA cs (ne_nil_of_usize h)⟩

/-- **`UIso` is isomorphism of the realized graphs**, for trees with at least two vertices. -/
theorem uiso_iff_aGraph (t t' : UTree) (h : 2 ≤ usize t) (h' : 2 ≤ usize t') :
    UIso t t' ↔
      Nonempty (aGraph (Step3.realize (dtRealize t)) ≃g aGraph (Step3.realize (dtRealize t'))) := by
  obtain ⟨φ⟩ := G_iso_aGraph t h
  obtain ⟨φ'⟩ := G_iso_aGraph t' h'
  constructor
  · rintro ⟨f⟩; exact ⟨(φ.symm.trans f).trans φ'⟩
  · rintro ⟨g⟩; exact ⟨(φ.trans g).trans φ'.symm⟩

end RerootIso

namespace AllUniqueIso

open R3Cert.Step3 R3Cert.RerootIso R3Cert.AllUnique

/-- The Brualdi-Goldwasser ratio `per(L) / ∏ deg` of the realized graph of `t`. -/
noncomputable def bgRatio (t : UTree) : ℝ :=
  (lapl (aGraph (Step3.realize (dtRealize t)))).permanent
    / (∏ v, ((aGraph (Step3.realize (dtRealize t))).degree v : ℝ))

theorem bgRatio_eq (t : UTree) : bgRatio t = Aobj t := pi_utree t

/-- **Exact characterization of the maximizers, every `n ≥ 4`, stated on the realized graphs.**  A tree
    on `n` vertices maximizes the ratio `per(L)/∏ deg` of its graph iff its graph is isomorphic
    (`SimpleGraph.Iso`) to the graph of `bgMax n`, or `n = 21` and its graph is isomorphic to the graph of
    the subdivided star `C^10`. -/
theorem bg_maximizers_exact_aGraph (n : ℕ) (h4 : 4 ≤ n) (t : UTree) (ht : usize t = n) :
    (∀ t' : UTree, usize t' = n → bgRatio t' ≤ bgRatio t) ↔
      (Nonempty (aGraph (Step3.realize (dtRealize t))
          ≃g aGraph (Step3.realize (dtRealize (BGMaximizerAll.bgMax n)))) ∨
        (n = 21 ∧ Nonempty (aGraph (Step3.realize (dtRealize t)) ≃g aGraph (Step3.realize (dtRealize S21))))) := by
  have hb : usize (BGMaximizerAll.bgMax n) = n := (BGMaximizerAll.bg_maximizer_all n h4).1
  simp only [bgRatio_eq]
  rw [bg_maximizers_exact_iso n h4 t ht, uiso_iff_aGraph _ _ (by omega) (by omega),
    uiso_iff_aGraph _ _ (by omega) (by rw [usize_S21]; omega)]

end AllUniqueIso
end R3Cert
