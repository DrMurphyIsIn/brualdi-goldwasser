/-
LeanCherry.Graph -- counting lemmas for the parent-child edge sets (toward the SimpleGraph statement).
  outC E v = #{edges with parent v},  inC E v = #{edges with child v}.
-/
import LeanCherry.BridgeMain

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

noncomputable section

def outC (E : Finset (List ℕ × List ℕ)) (v : List ℕ) : ℕ := (E.filter (fun e => e.1 = v)).card
def inC (E : Finset (List ℕ × List ℕ)) (v : List ℕ) : ℕ := (E.filter (fun e => e.2 = v)).card

lemma root_notin (j : ℕ) (c : Br) (L : List Br) :
    ([], [j]) ∉ (edges c).map (sh j) ∪ fanE (j + 1) L := by
  rw [mem_union]; rintro (h | h)
  · obtain ⟨e, _, he⟩ := mem_map.mp h; rw [sh_apply] at he; exact List.cons_ne_nil _ _ (congrArg Prod.fst he)
  · rcases fanE_verts (j + 1) L _ h [j] (by simp [ev]) with h' | ⟨k, u, hk, h'⟩
    · exact List.cons_ne_nil _ _ h'
    · have := (List.cons.inj h').1; omega

lemma disjoint_sh_fan_edges (j : ℕ) (c : Br) (L : List Br) :
    Disjoint ((edges c).map (sh j)) (fanE (j + 1) L) := by
  rw [Finset.disjoint_left]
  intro e he hf
  have := disj_sh_fan j (edges c) L e he e hf
  exact (ev_nonempty e).ne_empty (disjoint_self.mp this)

lemma edge_len : ∀ (j : ℕ) (L : List Br), ∀ e ∈ fanE j L, e.2.length = e.1.length + 1
  | _, [], e, he => by simp [fanE] at he
  | j, c :: L, e, he => by
      simp only [fanE, mem_insert, mem_union, mem_map] at he
      rcases he with rfl | ⟨e', he', rfl⟩ | he
      · rfl
      · cases c with
        | node gs =>
          have := edge_len 0 gs e' (by rw [← edges_node]; exact he')
          simp [sh_apply, this]
      · exact edge_len (j + 1) L e he

lemma edges_len (b : Br) : ∀ e ∈ edges b, e.2.length = e.1.length + 1 := by
  cases b with | node cs => rw [edges_node]; exact edge_len 0 cs

/-- out-degree at the root of a fan -/
lemma fan_out_nil : ∀ (j : ℕ) (L : List Br), outC (fanE j L) [] = L.length
  | _, [] => by simp [outC, fanE]
  | j, c :: L => by
      unfold outC
      rw [fanE, filter_insert, if_pos rfl, filter_union]
      have hA : ((edges c).map (sh j)).filter (fun e => e.1 = []) = ∅ := by
        apply filter_false_of_mem; intro e he h
        obtain ⟨e', _, rfl⟩ := mem_map.mp he; rw [sh_apply] at h; exact List.cons_ne_nil _ _ h
      rw [hA, empty_union, card_insert_of_notMem]
      · have := fan_out_nil (j + 1) L; unfold outC at this; rw [this]; simp
      · intro h; exact root_notin j c L (mem_union_right _ (mem_filter.mp h).1)

lemma fan_in_nil : ∀ (j : ℕ) (L : List Br), inC (fanE j L) [] = 0
  | _, [] => by simp [inC, fanE]
  | j, c :: L => by
      unfold inC
      rw [fanE, filter_insert, if_neg (by simp), filter_union]
      have hA : ((edges c).map (sh j)).filter (fun e => e.2 = []) = ∅ := by
        apply filter_false_of_mem; intro e he h
        obtain ⟨e', _, rfl⟩ := mem_map.mp he; rw [sh_apply] at h; exact List.cons_ne_nil _ _ h
      rw [hA, empty_union]
      have := fan_in_nil (j + 1) L; unfold inC at this; exact this

lemma edges_in_nil (c : Br) : inC (edges c) [] = 0 := by
  cases c with | node gs => rw [edges_node]; exact fan_in_nil 0 gs

lemma card_filter_map_sh (j k : ℕ) (u : List ℕ) (E : Finset (List ℕ × List ℕ)) (fst : Bool) :
    ((E.map (sh j)).filter (fun e => (if fst then e.1 else e.2) = k :: u)).card
      = if k = j then (E.filter (fun e => (if fst then e.1 else e.2) = u)).card else 0 := by
  rw [filter_map, card_map]
  by_cases hk : k = j
  · subst hk; rw [if_pos rfl]; congr 1; apply filter_congr; intro e _
    cases fst <;> simp [sh_apply]
  · rw [if_neg hk]; rw [card_eq_zero]; apply filter_false_of_mem; intro e _ h
    cases fst <;> simp [sh_apply] at h <;> exact hk h.1.symm

/-- out-degree of a non-root vertex of a fan -/
lemma fan_out_cons : ∀ (j : ℕ) (L : List Br) (k : ℕ) (u : List ℕ),
    outC (fanE j L) (k :: u) = if j ≤ k then (match L[k - j]? with
      | some c => outC (edges c) u
      | none => 0) else 0
  | j, [], k, u => by simp [outC, fanE]
  | j, c :: L, k, u => by
      unfold outC
      rw [fanE, filter_insert, if_neg (by simp), filter_union,
        card_union_of_disjoint (disjoint_filter_filter (disjoint_sh_fan_edges j c L))]
      have hA := card_filter_map_sh j k u (edges c) true
      simp only [if_true] at hA
      rw [hA]
      have hB := fan_out_cons (j + 1) L k u
      unfold outC at hB
      rw [hB]
      rcases lt_trichotomy k j with h | rfl | h
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_pos rfl, if_neg (by omega), if_pos le_rfl, Nat.sub_self]; simp [outC]
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), zero_add]
        have : k - j = (k - (j + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]

/-- in-degree of a non-root vertex of a fan -/
lemma fan_in_cons : ∀ (j : ℕ) (L : List Br) (k : ℕ) (u : List ℕ),
    inC (fanE j L) (k :: u) = if j ≤ k then (match L[k - j]? with
      | some c => (if u = [] then 1 else inC (edges c) u)
      | none => 0) else 0
  | j, [], k, u => by simp [inC, fanE]
  | j, c :: L, k, u => by
      unfold inC
      rw [fanE, filter_insert, filter_union]
      have hA := card_filter_map_sh j k u (edges c) false
      simp only [Bool.false_eq_true, if_false] at hA
      have hB := fan_in_cons (j + 1) L k u
      unfold inC at hB
      have hdisj := disjoint_filter_filter (p := fun e : List ℕ × List ℕ => e.2 = k :: u)
        (q := fun e : List ℕ × List ℕ => e.2 = k :: u) (disjoint_sh_fan_edges j c L)
      by_cases hku : k = j ∧ u = []
      · obtain ⟨rfl, rfl⟩ := hku
        rw [if_pos rfl, card_insert_of_notMem, card_union_of_disjoint hdisj, hA, hB, if_pos rfl,
          if_neg (by omega), if_pos le_rfl, Nat.sub_self]
        · have := edges_in_nil c; unfold inC at this
          simp only [List.getElem?_cons_zero, if_true]; omega
        · intro h; exact root_notin k c L (by
            rcases mem_union.mp h with h | h
            · exact mem_union_left _ (mem_filter.mp h).1
            · exact mem_union_right _ (mem_filter.mp h).1)
      · have hne : ¬ ((([] : List ℕ), [j]).2 = k :: u) := by
          intro h; simp only [List.cons.injEq] at h; exact hku ⟨h.1.symm, h.2.symm⟩
        rw [if_neg hne, card_union_of_disjoint hdisj, hA, hB]
        rcases lt_trichotomy k j with h | rfl | h
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · have hu : u ≠ [] := fun h => hku ⟨rfl, h⟩
          rw [if_pos rfl, if_neg (by omega), if_pos le_rfl, Nat.sub_self]; simp [inC, hu]
        · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), zero_add]
          have : k - j = (k - (j + 1)) + 1 := by omega
          rw [this, List.getElem?_cons_succ]

/-- out- and in-degrees of a planted branch, via the subtree lookup -/
theorem out_in_formula : ∀ (v : List ℕ) (b : Br),
    outC (edges b) v = (match subt b v with | some c => nch c | none => 0) ∧
    inC (edges b) v = (if v = [] then 0 else if (subt b v).isSome then 1 else 0)
  | [], .node cs => by
      rw [edges_node, fan_out_nil, fan_in_nil]; simp [subt, nch, kids]
  | k :: u, .node cs => by
      rw [edges_node, fan_out_cons, fan_in_cons]
      simp only [Nat.zero_le, if_true, Nat.sub_zero, reduceCtorEq, if_false]
      rcases hk : cs[k]? with _ | c
      · simp [subt, hk]
      · have IH := out_in_formula u c
        rw [subt_cons hk]
        refine ⟨IH.1, ?_⟩
        by_cases hu : u = []
        · subst hu; simp [subt]
        · show (if u = [] then 1 else inC (edges c) u) = _
          rw [if_neg hu, IH.2, if_neg hu]

end

end Br

end LeanCherry
