import Mathlib
import R3Cert.BGMaximizer150
import R3Cert.BGSpiderRule
import BGUnique.SpiderUnique

namespace BGMax

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL

/-- Spider reduction with the rerooting kept. -/
theorem maximizer_is_spider_reroot (t : UTree) (hn : 150 ≤ usize t)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    ∃ cs : List UTree, RerootRel t (UTree.node cs) ∧ (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧
      usize (UTree.node cs) = usize t ∧ Aobj (UTree.node cs) = Aobj t := by
  obtain ⟨t', hrr, hmr⟩ := exists_maxRooted t
  have hA := hrr.aobj
  have hS := hrr.usize
  obtain ⟨cs'⟩ := t'
  by_cases hna : ∃ c ∈ cs'.map fromU, ¬ IsAtom c
  · exfalso
    have hk2 : 2 ≤ (cs'.map fromU).length := by
      rw [List.length_map]; exact two_le_length_of_maxRooted hmr (by omega)
    have hcap : ∀ c ∈ cs'.map fromU, maxCh c + 1 ≤ (cs'.map fromU).length := by
      intro c hc
      rw [List.mem_map] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      rw [maxCh_fromU, List.length_map]; exact hmr x hx
    have hN : 149 ≤ bsizeList (cs'.map fromU) := by
      have := usize_eq_bsizeList cs'; omega
    obtain ⟨sp, hsz, hlt⟩ := R3Cert.BGSCL.spider_dominates_of_maxDegreeRoot_150 _ hk2 hcap hN hna
    set u := UTree.node (sp.map toU)
    have hu : usize u = usize t := by
      rw [usize_eq_bsizeList, map_fromU_toU, hsz, hS, usize_eq_bsizeList]
    have hAu : Aobj u = piRoot sp := by rw [Aobj_eq_piRoot, map_fromU_toU]
    have := hmax u hu
    rw [hAu, hA, Aobj_eq_piRoot] at this
    linarith
  · push Not at hna
    exact ⟨cs', hrr, fun c hc => atom_of_fromU (hna _ (List.mem_map_of_mem hc)), hS.symm, hA.symm⟩


end BGMax

namespace R3Cert
namespace SpiderStrict

open R3Cert.RTree R3Cert.Step3 BGSpiderOpt BGSpiderRule BGMax

/-- Uniqueness up to rerooting, n ≥ 492: every maximizer of `Aobj` on its size is a rerooting of a spider
    whose child list is a rearrangement of the rule winner `W n`. -/
theorem maximizer_unique_large (t : UTree) (hn : 492 ≤ usize t)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    ∃ l : List Child, RerootRel t (spiderU l) ∧ l.Perm (W (usize t)) := by
  obtain ⟨cs, hrr, hat, hsz, hA⟩ := maximizer_is_spider_reroot t (by omega) hmax
  obtain ⟨l, rfl⟩ := exists_child_list cs hat
  have hsp : spiderU l = UTree.node (l.map childU) := rfl
  have hnv : nv l = usize t := by rw [← usize_spiderU, hsp, hsz]
  refine ⟨l, by rw [hsp]; exact hrr, ?_⟩
  rw [← hnv]
  apply spider_unique_large l (by omega)
  have hW := hmax (spiderU (W (usize t))) (by rw [usize_spiderU, nv_W _ hn])
  rw [Aobj_spiderU, ← hA, ← hsp, Aobj_spiderU, ← hnv] at hW
  exact_mod_cast hW

end SpiderStrict
end R3Cert
