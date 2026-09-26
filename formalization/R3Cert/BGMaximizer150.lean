/-
  R3Cert.BGMaximizer150 -- every Brualdi-Goldwasser maximizer on n >= 150 vertices is a spider.

  From `BGSpiderMidFinal.spider_dominates_of_maxDegreeRoot_150` (a max-degree rooting with a
  non-atom child and >= 149 further vertices is STRICTLY beaten by a branch list of the same size)
  plus the bridge and rerooting of `BGMaximizer`: if `t` maximizes `Aobj` among trees of its size,
  then some rerooting of `t` (same `Aobj`, same size) has only atom children -- cherries and arms
  (`armU j`, `armU 0` = leaf) -- i.e. `t` is a spider.
  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGMaximizer
import R3Cert.BGSpiderMidFinal

namespace BGMax

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL

mutual
theorem fromU_toU : ∀ b : Branch, fromU (toU b) = b
  | .node cs => by rw [toU, fromU, fromUL_toUL cs]
theorem fromUL_toUL : ∀ l : List Branch, fromUL (toUL l) = l
  | [] => by simp [toUL, fromUL]
  | c :: t => by rw [toUL, fromUL, fromU_toU c, fromUL_toUL t]
end

theorem map_fromU_toU (l : List Branch) : (l.map toU).map fromU = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left (fun b _ => fromU_toU b)

/-- **Every maximizer on `n ≥ 150` vertices is a spider.** -/
theorem maximizer_is_spider_150 (t : UTree) (hn : 150 ≤ usize t)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    ∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧
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
    exact ⟨cs', fun c hc => atom_of_fromU (hna _ (List.mem_map_of_mem hc)), hS.symm, hA.symm⟩

end BGMax
