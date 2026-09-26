/-
  R3Cert.BGMaximizerMid -- the Brualdi-Goldwasser maximizer for every 150 <= n <= 491 (Lean).

  * `forests m`: every list of rooted trees with total size m (finite enumeration), hence an
    `Aobj`-maximizing tree exists at every size (`exists_max_tree`).
  * A maximizer on n >= 150 vertices reroots to a spider (`BGMax.maximizer_is_spider_150`), whose value
    is `F` of its child list (`BGSpiderRule.Aobj_spiderU`), which is at most `F (tab n)` by the kernel
    sweep (`BGSpiderTable.spider_opt_table`).
  Result (`bg_maximizer_mid`): for 150 <= n <= 491, the table spider `tab n` has n vertices and
  maximizes per(L)/prod deg over all trees on n vertices.
  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGMaximizer150
import R3Cert.BGSpiderTableAll
import R3Cert.BGGrowthRate

namespace R3Cert
namespace BGMaximizerMid

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSpiderOpt R3Cert.BGSpiderRule R3Cert.BGSpiderTable

/-- All lists of rooted trees whose sizes sum to `m`. -/
def forests : ℕ → List (List UTree)
  | 0 => [[]]
  | m + 1 =>
    (List.range (m + 1)).attach.flatMap fun ⟨i, hi⟩ =>
      (forests i).flatMap fun f => (forests (m - i)).map fun g => UTree.node f :: g
  termination_by m => m
  decreasing_by all_goals (simp at hi; omega)

theorem mem_forests : ∀ (N : ℕ) (l : List UTree), usizeList l ≤ N → l ∈ forests (usizeList l) := by
  intro N
  induction N with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [forests, usizeList]
    | cons t r => cases t with | node f => rw [usizeList_cons, usize_node] at hl; omega
  | succ N ih =>
    intro l hl
    cases l with
    | nil => simp [forests, usizeList]
    | cons t r =>
      cases t with
      | node f =>
        have hs : usizeList (UTree.node f :: r) = (usizeList f + usizeList r) + 1 := by
          rw [usizeList_cons, usize_node]; ring
        rw [usizeList_cons, usize_node] at hl
        have hf := ih f (by omega)
        have hr := ih r (by omega)
        rw [hs, forests]
        simp only [List.mem_flatMap, List.mem_attach, true_and, List.mem_map, Subtype.exists,
          List.mem_range]
        refine ⟨usizeList f, by omega, f, hf, r, ?_, rfl⟩
        rwa [show usizeList f + usizeList r - usizeList f = usizeList r by omega]

theorem exists_max_real {α : Type*} (f : α → ℝ) : ∀ (S : List α), S ≠ [] → ∃ x ∈ S, ∀ y ∈ S, f y ≤ f x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun y hy => by simp at hy; rw [hy]⟩
  | a :: b :: t, _ => by
    obtain ⟨x, hx, hmax⟩ := exists_max_real f (b :: t) (by simp)
    rcases le_total (f a) (f x) with h | h
    · refine ⟨x, List.mem_cons_of_mem _ hx, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h
      · exact hmax y hy'
    · refine ⟨a, by simp, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact le_refl _
      · exact le_trans (hmax y hy') h

/-- **An `Aobj`-maximizing tree exists at every size `n ≥ 1`.** -/
theorem exists_max_tree (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : UTree, usize x = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj x := by
  have hmem : ∀ t : UTree, usize t = n → t ∈ (forests (n - 1)).map UTree.node := by
    intro t ht
    cases t with
    | node f =>
      rw [usize_node] at ht
      have := mem_forests _ f le_rfl
      rw [show usizeList f = n - 1 by omega] at this
      exact List.mem_map_of_mem this
  have hne : (forests (n - 1)).map UTree.node ≠ [] := by
    have := hmem (UTree.node (List.replicate (n - 1) (UTree.node [])))
      (by rw [usize_node, usizeList_replicate, usize_node]; simp [usizeList]; omega)
    exact List.ne_nil_of_mem this
  obtain ⟨x, hx, hmax⟩ := exists_max_real Aobj _ hne
  have hxs : usize x = n := by
    rw [List.mem_map] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    rw [usize_node]
    have hsum : ∀ (m : ℕ) (g : List UTree), g ∈ forests m → usizeList g = m := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ihm =>
        intro g hg
        cases m with
        | zero => simp [forests] at hg; subst hg; simp [usizeList]
        | succ m =>
          rw [forests] at hg
          simp only [List.mem_flatMap, List.mem_attach, true_and, List.mem_map, Subtype.exists,
            List.mem_range] at hg
          obtain ⟨i, hi, f', hf', g', hg', rfl⟩ := hg
          rw [usizeList_cons, usize_node, ihm i (by omega) f' hf', ihm (m - i) (by omega) g' hg']
          omega
    rw [hsum _ f hf]; omega
  exact ⟨x, hxs, fun t ht => hmax t (hmem t ht)⟩

/-- **The Brualdi-Goldwasser maximizer for `150 ≤ n ≤ 491`.**  The table spider `tab n` has `n`
    vertices, and every tree on `n` vertices has `Aobj t ≤ Aobj (spiderU (tab n))`. -/
theorem bg_maximizer_mid (n : ℕ) (h150 : 150 ≤ n) (hN : n ≤ 491) :
    usize (spiderU (tab n)) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (spiderU (tab n)) := by
  obtain ⟨hnv, hopt⟩ := spider_opt_table n (by omega) hN
  refine ⟨by rw [usize_spiderU, hnv], fun t ht => ?_⟩
  obtain ⟨x, hx, hxmax⟩ := exists_max_tree n (by omega)
  obtain ⟨cs, hat, hsz, hA⟩ := BGMax.maximizer_is_spider_150 x (by omega)
    (fun t' ht' => hxmax t' (by omega))
  obtain ⟨l, rfl⟩ := exists_child_list cs hat
  have hl : nv l = n := by
    have := usize_spiderU l; rw [spiderU] at this; omega
  calc Aobj t ≤ Aobj x := hxmax t ht
    _ = Aobj (UTree.node (l.map childU)) := hA.symm
    _ = (F l : ℝ) := Aobj_spiderU l
    _ ≤ (F (tab n) : ℝ) := by exact_mod_cast hopt l hl
    _ = Aobj (spiderU (tab n)) := (Aobj_spiderU _).symm

end BGMaximizerMid
end R3Cert
