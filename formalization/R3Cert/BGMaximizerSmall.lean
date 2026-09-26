/-
  R3Cert.BGMaximizerSmall -- the Brualdi-Goldwasser maximizer for every 7 <= n <= 149 (Lean).

  Take an `Aobj`-maximizing tree `x` on `n` vertices (`exists_max_tree`) and reroot it at a vertex of
  maximum degree (`exists_maxRooted`).  If some child is not an atom, `x` is strictly beaten by a tree
  of the same size -- a contradiction:
    * root degree ≤ 23: the envelope certificate `G149.envcertK`;
    * root degree ≥ 24, n ≥ 91: `spider_dominates_highDegree_uncond`;
    * root degree ≥ 24, 25 ≤ n ≤ 90: `highDegree_small` (against the table spider).
  So `x` is a spider, and the kernel sweep `spider_opt_table` bounds it by the table spider `tab n`.
  Result (`bg_maximizer_small`).  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGEnvCert.G149.MainK
import R3Cert.BGHighDegreeSmall
import R3Cert.BGMaximizerMid
import R3Cert.BGMaximizer150

namespace R3Cert
namespace BGMaximizerSmall

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL R3Cert.BGSpiderOpt R3Cert.BGSpiderRule
  R3Cert.BGSpiderTable BGMax

/-- A tree strictly better than `x` built from a branch list of the same size. -/
theorem not_max_of_better {x : UTree} (hmax : ∀ t, usize t = usize x → Aobj t ≤ Aobj x)
    (cs : List UTree) (hA : Aobj x = Aobj (UTree.node cs)) (hS : usize x = usize (UTree.node cs))
    (sp : List BGSCL.Branch) (hsz : bsizeList sp = bsizeList (cs.map fromU))
    (hlt : piRoot (cs.map fromU) < piRoot sp) : False := by
  have hu : usize (UTree.node (sp.map toU)) = usize x := by
    rw [usize_eq_bsizeList, map_fromU_toU, hsz, hS, usize_eq_bsizeList]
  have h := hmax _ hu
  rw [Aobj_eq_piRoot, map_fromU_toU, hA, Aobj_eq_piRoot] at h
  linarith

/-- **Every maximizer on `7 ≤ n ≤ 149` vertices is a spider.** -/
theorem maximizer_is_spider_small (x : UTree) (h7 : 7 ≤ usize x) (h149 : usize x ≤ 149)
    (hmax : ∀ t : UTree, usize t = usize x → Aobj t ≤ Aobj x) :
    ∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧
      usize (UTree.node cs) = usize x ∧ Aobj (UTree.node cs) = Aobj x := by
  obtain ⟨t', hrr, hmr⟩ := exists_maxRooted x
  have hA := hrr.aobj
  have hS := hrr.usize
  obtain ⟨cs'⟩ := t'
  have hN := usize_eq_bsizeList cs'
  by_cases hna : ∃ c ∈ cs'.map fromU, ¬ IsAtom c
  · exfalso
    have hk2 : 2 ≤ (cs'.map fromU).length := by
      rw [List.length_map]; exact two_le_length_of_maxRooted hmr (by omega)
    have hcap : ∀ c ∈ cs'.map fromU, maxCh c + 1 ≤ (cs'.map fromU).length := by
      intro c hc
      rw [List.mem_map] at hc
      obtain ⟨y, hy, rfl⟩ := hc
      rw [maxCh_fromU, List.length_map]; exact hmr y hy
    rcases le_or_gt (cs'.map fromU).length 23 with hk | hk
    · obtain ⟨_, hsz, hlt⟩ := R3Cert.EnvCert.G149.envcertK _ hk2 hk hcap (by omega) (by omega) hna
      exact not_max_of_better hmax cs' hA hS _ hsz hlt
    · rcases le_or_gt 91 (usize x) with hbig | hsmall
      · obtain ⟨a, q, _, hsz, hlt⟩ := spider_dominates_highDegree_uncond _ (by omega) hna (by omega)
        exact not_max_of_better hmax cs' hA hS _ hsz hlt
      · have hkn : (cs'.map fromU).length ≤ bsizeList (cs'.map fromU) :=
          R3Cert.EnvCert.length_le_bsizeList _
        have hlt := BGHighDegreeSmall.highDegree_small _ (by omega) hna (usize x) (by omega)
          (by omega) (by omega)
        obtain ⟨hnv, _⟩ := spider_opt_table (usize x) (by omega) (by omega)
        have h := hmax (spiderU (tab (usize x))) (by rw [usize_spiderU, hnv])
        rw [Aobj_spiderU, hA, Aobj_eq_piRoot] at h
        linarith
  · push Not at hna
    exact ⟨cs', fun c hc => atom_of_fromU (hna _ (List.mem_map_of_mem hc)), hS.symm, hA.symm⟩

/-- **The Brualdi-Goldwasser maximizer for `7 ≤ n ≤ 149`.** -/
theorem bg_maximizer_small (n : ℕ) (h7 : 7 ≤ n) (h149 : n ≤ 149) :
    usize (spiderU (tab n)) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (spiderU (tab n)) := by
  obtain ⟨hnv, hopt⟩ := spider_opt_table n (by omega) (by omega)
  refine ⟨by rw [usize_spiderU, hnv], fun t ht => ?_⟩
  obtain ⟨x, hx, hxmax⟩ := BGMaximizerMid.exists_max_tree n (by omega)
  obtain ⟨cs, hat, hsz, hA⟩ := maximizer_is_spider_small x (by omega) (by omega)
    (fun t' ht' => hxmax t' (by omega))
  obtain ⟨l, rfl⟩ := exists_child_list cs hat
  have hl : nv l = n := by
    have := usize_spiderU l; rw [spiderU] at this; omega
  calc Aobj t ≤ Aobj x := hxmax t ht
    _ = Aobj (UTree.node (l.map childU)) := hA.symm
    _ = (F l : ℝ) := Aobj_spiderU l
    _ ≤ (F (tab n) : ℝ) := by exact_mod_cast hopt l hl
    _ = Aobj (spiderU (tab n)) := (Aobj_spiderU _).symm

end BGMaximizerSmall
end R3Cert
