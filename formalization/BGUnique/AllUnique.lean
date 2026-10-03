import Mathlib
import R3Cert.BGMaximizerSmall
import R3Cert.BGMaximizerAll
import BGUnique.MidUnique
import BGUnique.SmallTies
import BGUnique.TinyUnique

namespace R3Cert
namespace AllUnique

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL R3Cert.BGSpiderOpt R3Cert.BGSpiderRule R3Cert.BGSpiderTable BGMax
open R3Cert.RerootEquiv R3Cert.SpiderStrict

/-! ### `7 ≤ n ≤ 149`: the spider reduction, keeping the rerooting -/

theorem maximizer_is_spider_reroot_small (x : UTree) (h7 : 7 ≤ usize x) (h149 : usize x ≤ 149)
    (hmax : ∀ t : UTree, usize t = usize x → Aobj t ≤ Aobj x) :
    ∃ cs : List UTree, RerootRel x (UTree.node cs) ∧ (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧
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
      exact BGMaximizerSmall.not_max_of_better hmax cs' hA hS _ hsz hlt
    · rcases le_or_gt 91 (usize x) with hbig | hsmall
      · obtain ⟨a, q, _, hsz, hlt⟩ := spider_dominates_highDegree_uncond _ (by omega) hna (by omega)
        exact BGMaximizerSmall.not_max_of_better hmax cs' hA hS _ hsz hlt
      · have hkn : (cs'.map fromU).length ≤ bsizeList (cs'.map fromU) :=
          R3Cert.EnvCert.length_le_bsizeList _
        have hlt := BGHighDegreeSmall.highDegree_small _ (by omega) hna (usize x) (by omega)
          (by omega) (by omega)
        obtain ⟨hnv, _⟩ := spider_opt_table (usize x) (by omega) (by omega)
        have h := hmax (spiderU (tab (usize x))) (by rw [usize_spiderU, hnv])
        rw [Aobj_spiderU, hA, Aobj_eq_piRoot] at h
        linarith
  · push Not at hna
    exact ⟨cs', hrr, fun c hc => atom_of_fromU (hna _ (List.mem_map_of_mem hc)), hS.symm, hA.symm⟩

/-- `7 ≤ n ≤ 149`: every maximizer is a rerooting of the table spider, or (only at 21) of the
    all-cherry spider. -/
theorem small_unique (t : UTree) (h7 : 7 ≤ usize t) (h149 : usize t ≤ 149)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) : TieGoal (usize t) t := by
  obtain ⟨cs, hrr, hat, hsz, hA⟩ := maximizer_is_spider_reroot_small t h7 h149 hmax
  obtain ⟨l, rfl⟩ := exists_child_list cs hat
  have hsp : spiderU l = UTree.node (l.map childU) := rfl
  have hnv : nv l = usize t := by rw [← usize_spiderU, hsp, hsz]
  obtain ⟨hnvT, _⟩ := spider_opt_table (usize t) (by omega) (by omega)
  have hge : F (tab (usize t)) ≤ F l := by
    have hW := hmax (spiderU (tab (usize t))) (by rw [usize_spiderU, hnvT])
    rw [Aobj_spiderU, ← hA, ← hsp, Aobj_spiderU] at hW
    exact_mod_cast hW
  rw [← hsp] at hrr
  exact tieGoal_closed _ _ _ hrr (spider_small_tie (usize t) h7 h149 l hnv hge)

/-! ### The two maximizers on 21 vertices -/

/-- The subdivided star on 21 vertices: ten pendant 2-paths (`C^10`). -/
def S21 : UTree := spiderU (List.replicate 10 Child.cherry)

/-- `bgMax 21` is `T(3,3,3)`: rooted at its middle vertex, three cherries and two arms carrying three
    cherries each (`C^3 A_3^2`). -/
theorem bgMax21_eq :
    BGMaximizerAll.bgMax 21 = spiderU (List.replicate 3 Child.cherry ++ List.replicate 2 (Child.arm 3)) := by
  unfold BGMaximizerAll.bgMax
  rw [if_pos (by norm_num)]
  congr 1

theorem lvR_bgMax21 : RerootEquiv.lvR (BGMaximizerAll.bgMax 21) = 9 := by
  rw [bgMax21_eq]; decide +kernel

theorem lvR_S21 : RerootEquiv.lvR S21 = 10 := by
  unfold S21; decide +kernel

/-- `T(3,3,3)` and `C^10` are different trees: no rerooting relates them (they have 9 and 10 leaves). -/
theorem bgMax21_not_S21 : ¬ RerootRel (BGMaximizerAll.bgMax 21) S21 ∧ ¬ RerootRel S21 (BGMaximizerAll.bgMax 21) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := lvR_rel h; rw [lvR_bgMax21, lvR_S21] at this; omega
  · have := lvR_rel h; rw [lvR_bgMax21, lvR_S21] at this; omega

theorem Aobj_S21 : Aobj S21 = Aobj (BGMaximizerAll.bgMax 21) := by
  rw [bgMax21_eq]
  unfold S21
  rw [Aobj_spiderU, Aobj_spiderU]
  have e1 : List.replicate 10 Child.cherry = canon 10 0 0 0 := by simp [canon]
  have e2 : List.replicate 3 Child.cherry ++ List.replicate 2 (Child.arm 3) = canon 3 3 2 0 := by simp [canon]
  rw [e1, e2, F_canon_eq _ _ _ _ (by norm_num), F_canon_eq _ _ _ _ (by norm_num)]
  norm_num [fnum, fden]

theorem usize_S21 : usize S21 = 21 := by
  unfold S21; rw [usize_spiderU]; decide

/-! ### Uniqueness for every `n ≥ 4` -/

theorem bgMax_spider_le491 (n : ℕ) (h : n ≤ 491) : BGMaximizerAll.bgMax n = spiderU (tab n) := by
  unfold BGMaximizerAll.bgMax; rw [if_pos h]

/-- **Uniqueness of the Brualdi-Goldwasser maximizer, every `n ≥ 4`, `n ≠ 21`.**  Every tree maximizing
    `Aobj` (the Laplacian ratio) among trees of its size is a rerooting (with children reordered) of the
    maximizer `bgMax n`; that is, the maximizer is unique up to isomorphism. -/
theorem bg_maximizer_unique_all (t : UTree) (h4 : 4 ≤ usize t) (h21 : usize t ≠ 21)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    RerootRel t (BGMaximizerAll.bgMax (usize t)) := by
  by_cases h6 : usize t ≤ 6
  · rw [bgMax_spider_le491 _ (by omega)]
    exact TinyUnique.tiny_unique (usize t) h4 h6 t rfl hmax
  by_cases h149 : usize t ≤ 149
  · rw [bgMax_spider_le491 _ (by omega)]
    rcases small_unique t (by omega) h149 hmax with h | ⟨e, _⟩
    · exact h
    · exact absurd e h21
  · obtain ⟨l, hrr, hp⟩ := bg_maximizer_unique t (by omega) hmax
    rw [bgMax_eq]
    exact hrr.trans (spiderU_perm hp)

/-- **The maximizers on 21 vertices**: every maximizer is a rerooting of `T(3,3,3) = bgMax 21` or of the
    subdivided star `C^10`. -/
theorem bg_maximizers_21 (t : UTree) (h : usize t = 21)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    RerootRel t (BGMaximizerAll.bgMax 21) ∨ RerootRel t S21 := by
  rcases small_unique t (by omega) (by omega) hmax with h' | ⟨_, h'⟩
  · left; rw [h] at h'; rw [bgMax_spider_le491 21 (by norm_num)]; exact h'
  · right; exact h'

/-- **Exact characterization of the maximizers, every `n ≥ 4`.**  A tree on `n` vertices maximizes `Aobj`
    (the Laplacian ratio) iff it is a rerooting of `bgMax n`, or `n = 21` and it is a rerooting of the
    subdivided star `C^10`.  Rerooting is an equivalence relation (`RerootEquiv.equivalence`), and at
    `n = 21` the two classes are distinct (`bgMax21_not_S21`). -/
theorem bg_maximizers_exact (n : ℕ) (h4 : 4 ≤ n) (t : UTree) (ht : usize t = n) :
    (∀ t' : UTree, usize t' = n → Aobj t' ≤ Aobj t) ↔
      (RerootRel t (BGMaximizerAll.bgMax n) ∨ (n = 21 ∧ RerootRel t S21)) := by
  constructor
  · intro hmax
    subst ht
    by_cases h21 : usize t = 21
    · rcases bg_maximizers_21 t h21 hmax with h | h
      · left; rw [h21]; exact h
      · exact Or.inr ⟨h21, h⟩
    · exact Or.inl (bg_maximizer_unique_all t h4 h21 hmax)
  · obtain ⟨_, hopt⟩ := BGMaximizerAll.bg_maximizer_all n h4
    rintro (h | ⟨rfl, h⟩) t' ht'
    · rw [h.aobj]; exact hopt t' ht'
    · rw [h.aobj, Aobj_S21]; exact hopt t' ht'

end AllUnique
end R3Cert
