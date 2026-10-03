import Mathlib
import R3Cert.BGSpiderTableAll
import R3Cert.BGMaximizerAll
import BGUnique.SweepAll
import BGUnique.TreeUnique

namespace R3Cert
namespace SpiderStrict

open R3Cert.RTree R3Cert.Step3 BGSpiderOpt BGSpiderRule BGSpiderTable BGMax

/-- Uniqueness in the spider family, 150 ≤ n ≤ 491. -/
theorem spider_unique_mid (l : List Child) (h150 : 150 ≤ nv l) (hN : nv l ≤ 491)
    (hge : F (tab (nv l)) ≤ F l) : l.Perm (tab (nv l)) :=
  spider_unique_of_check _ (by omega) (checkN_all _ (by omega) hN) (checkNS_mid _ h150 hN) l rfl hge

/-- Strict optimality in the spider family, 150 ≤ n ≤ 491. -/
theorem spider_strict_mid (l : List Child) (h150 : 150 ≤ nv l) (hN : nv l ≤ 491)
    (hne : ¬ l.Perm (tab (nv l))) : F l < F (tab (nv l)) := by
  have hopt := (spider_opt_of_checkN _ (by omega) (checkN_all _ (by omega) hN)).2 l rfl
  exact lt_of_le_of_ne hopt (fun h => hne (spider_unique_mid l h150 hN h.ge))

/-- Uniqueness up to rerooting, 150 ≤ n ≤ 491. -/
theorem maximizer_unique_mid (t : UTree) (h150 : 150 ≤ usize t) (hN : usize t ≤ 491)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    ∃ l : List Child, RerootRel t (spiderU l) ∧ l.Perm (tab (usize t)) := by
  obtain ⟨cs, hrr, hat, hsz, hA⟩ := maximizer_is_spider_reroot t (by omega) hmax
  obtain ⟨l, rfl⟩ := exists_child_list cs hat
  have hsp : spiderU l = UTree.node (l.map childU) := rfl
  have hnv : nv l = usize t := by rw [← usize_spiderU, hsp, hsz]
  refine ⟨l, by rw [hsp]; exact hrr, ?_⟩
  rw [← hnv]
  apply spider_unique_mid l (by omega) (by omega)
  have hT := (spider_opt_of_checkN (usize t) (by omega) (checkN_all _ (by omega) hN)).1
  have hW := hmax (spiderU (tab (usize t))) (by rw [usize_spiderU, hT])
  rw [Aobj_spiderU, ← hA, ← hsp, Aobj_spiderU, ← hnv] at hW
  exact_mod_cast hW

/-- The winner's child list: the table spider for n ≤ 491, the rule spider above. -/
def bgWin (n : ℕ) : List Child := if n ≤ 491 then tab n else W n

theorem bgMax_eq (n : ℕ) : BGMaximizerAll.bgMax n = spiderU (bgWin n) := by
  unfold BGMaximizerAll.bgMax bgWin; split_ifs <;> rfl

/-- **Uniqueness of the maximizer, n ≥ 150.**  Every tree maximizing `Aobj` (the Laplacian ratio)
    among trees of its size is a rerooting of a spider whose child list is a rearrangement of the
    winner's; that is, the maximizer `bgMax n` is unique up to rerooting. -/
theorem bg_maximizer_unique (t : UTree) (h150 : 150 ≤ usize t)
    (hmax : ∀ t' : UTree, usize t' = usize t → Aobj t' ≤ Aobj t) :
    ∃ l : List Child, RerootRel t (spiderU l) ∧ l.Perm (bgWin (usize t)) := by
  unfold bgWin
  split_ifs with h
  · exact maximizer_unique_mid t h150 h hmax
  · exact maximizer_unique_large t (by omega) hmax

end SpiderStrict
end R3Cert
