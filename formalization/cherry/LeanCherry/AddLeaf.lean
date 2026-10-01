/-
LeanCherry.AddLeaf -- attaching a new leaf at an address (for the leaf-deletion induction in TreeBridge).
  addLeaf b a : the branch b with a new last child (a leaf) under the vertex at address a.
If subt b a = some c (k := nch c), the new vertex is a ++ [k], and
  edges (addLeaf b a) = insert (a, a ++ [k]) (edges b),  size (addLeaf b a) = size b + 1,
  old addresses stay valid, the new address is valid in addLeaf b a and invalid in b.
-/
import LeanCherry.Whole

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

mutual
def addLeaf : Br → List ℕ → Br
  | .node cs, [] => .node (cs ++ [.node []])
  | .node cs, i :: p => .node (modL cs i p)
def modL : List Br → ℕ → List ℕ → List Br
  | [], _, _ => []
  | c :: cs, 0, p => addLeaf c p :: cs
  | c :: cs, i + 1, p => c :: modL cs i p
end

lemma modL_get : ∀ (L : List Br) (i j : ℕ) (p : List ℕ),
    (modL L i p)[j]? = if j = i then (L[j]?).map (fun c => addLeaf c p) else L[j]?
  | [], i, j, p => by simp [modL]
  | c :: L, 0, 0, p => by simp [modL]
  | c :: L, 0, j + 1, p => by simp [modL]
  | c :: L, i + 1, 0, p => by simp [modL]
  | c :: L, i + 1, j + 1, p => by
      simp only [modL, List.getElem?_cons_succ]
      rw [modL_get L i j p]; simp

lemma modL_length : ∀ (L : List Br) (i : ℕ) (p : List ℕ), (modL L i p).length = L.length
  | [], _, _ => rfl
  | c :: L, 0, p => by simp [modL]
  | c :: L, i + 1, p => by simp [modL, modL_length L i p]

/-! ### subtree facts -/

lemma subt_nil (b : Br) : subt b [] = some b := by cases b; rfl

/-- the new address is valid in addLeaf b a -/
theorem subt_addLeaf_new : ∀ (a : List ℕ) (b c : Br), subt b a = some c →
    subt (addLeaf b a) (a ++ [nch c]) = some (.node [])
  | [], .node cs, c, h => by
      simp only [subt_nil, Option.some.injEq] at h; subst h
      simp [addLeaf, subt, nch, kids]
  | i :: p, .node cs, c, h => by
      rcases hi : cs[i]? with _ | d
      · simp [subt, hi] at h
      · rw [subt_cons hi] at h
        have hm : (modL cs i p)[i]? = some (addLeaf d p) := by rw [modL_get, if_pos rfl, hi]; rfl
        simp only [addLeaf, List.cons_append]
        rw [subt_cons hm]
        exact subt_addLeaf_new p d c h

/-- the new address is invalid in b -/
theorem subt_new_none : ∀ (a : List ℕ) (b c : Br), subt b a = some c → subt b (a ++ [nch c]) = none
  | [], .node cs, c, h => by
      simp only [subt_nil, Option.some.injEq] at h; subst h
      simp [subt, nch, kids]
  | i :: p, .node cs, c, h => by
      rcases hi : cs[i]? with _ | d
      · simp [subt, hi] at h
      · rw [subt_cons hi] at h
        simp only [List.cons_append]
        rw [subt_cons hi]
        exact subt_new_none p d c h

/-- old addresses stay valid -/
theorem subt_addLeaf_old : ∀ (x a : List ℕ) (b : Br), (subt b x).isSome → (subt (addLeaf b a) x).isSome
  | [], a, b, _ => by rw [subt_nil]; rfl
  | j :: q, [], .node cs, h => by
      rcases hj : cs[j]? with _ | e
      · simp [subt, hj] at h
      · rw [subt_cons hj] at h
        have : (cs ++ [.node []])[j]? = some e := by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]; exact hj
        simp only [addLeaf]; rw [subt_cons this]; exact h
  | j :: q, i :: p, .node cs, h => by
      rcases hj : cs[j]? with _ | e
      · simp [subt, hj] at h
      · rw [subt_cons hj] at h
        simp only [addLeaf]
        by_cases hji : j = i
        · subst hji
          have hm : (modL cs j p)[j]? = some (addLeaf e p) := by rw [modL_get, if_pos rfl, hj]; rfl
          rw [subt_cons hm]; exact subt_addLeaf_old q p e h
        · have hm : (modL cs i p)[j]? = some e := by rw [modL_get, if_neg hji, hj]
          rw [subt_cons hm]; exact h

/-! ### edges -/

lemma edges_leaf : edges (.node []) = ∅ := by rw [edges_node]; rfl

lemma fanE_append_leaf : ∀ (j : ℕ) (L : List Br),
    fanE j (L ++ [.node []]) = insert ([], [j + L.length]) (fanE j L)
  | j, [] => by simp [fanE, edges_leaf]
  | j, c :: L => by
      simp only [List.cons_append, fanE]
      rw [fanE_append_leaf (j + 1) L]
      ext x; simp only [mem_insert, mem_union, List.length_cons]
      rw [show j + 1 + L.length = j + (L.length + 1) by omega]
      tauto

lemma fanE_modL : ∀ (j : ℕ) (L : List Br) (i : ℕ) (p : List ℕ) (d : Br) (e : List ℕ × List ℕ),
    L[i]? = some d → edges (addLeaf d p) = insert e (edges d) →
    fanE j (modL L i p) = insert (sh (j + i) e) (fanE j L)
  | _, [], i, p, d, e, h, _ => by simp at h
  | j, c :: L, 0, p, d, e, h, he => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp only [modL, fanE, he, map_insert, Nat.add_zero]
      ext x; simp only [mem_insert, mem_union]; tauto
  | j, c :: L, i + 1, p, d, e, h, he => by
      simp only [List.getElem?_cons_succ] at h
      simp only [modL, fanE]
      rw [fanE_modL (j + 1) L i p d e h he, show j + 1 + i = j + (i + 1) by omega]
      ext x; simp only [mem_insert, mem_union]; tauto

/-- the edges of addLeaf -/
theorem edges_addLeaf : ∀ (a : List ℕ) (b c : Br), subt b a = some c →
    edges (addLeaf b a) = insert (a, a ++ [nch c]) (edges b)
  | [], .node cs, c, h => by
      simp only [subt_nil, Option.some.injEq] at h; subst h
      simp only [addLeaf, edges_node, fanE_append_leaf, Nat.zero_add, nch, kids, List.nil_append]
  | i :: p, .node cs, c, h => by
      rcases hi : cs[i]? with _ | d
      · simp [subt, hi] at h
      · rw [subt_cons hi] at h
        simp only [addLeaf, edges_node]
        rw [fanE_modL 0 cs i p d (p, p ++ [nch c]) hi (edges_addLeaf p d c h)]
        simp [sh_apply]

/-! ### size -/

lemma sizeL_append_leaf : ∀ L : List Br, sizeL (L ++ [.node []]) = sizeL L + 1
  | [] => by simp [sizeL, size]
  | c :: L => by simp only [List.cons_append, sizeL]; rw [sizeL_append_leaf L]; omega

mutual
theorem size_addLeaf : ∀ (a : List ℕ) (b c : Br), subt b a = some c → size (addLeaf b a) = size b + 1
  | [], .node cs, _, _ => by simp only [addLeaf, size]; rw [sizeL_append_leaf]
  | i :: p, .node cs, c, h => by
      rcases hi : cs[i]? with _ | d
      · simp [subt, hi] at h
      · rw [subt_cons hi] at h
        simp only [addLeaf, size]; rw [sizeL_modL cs i p d c hi h]
theorem sizeL_modL : ∀ (L : List Br) (i : ℕ) (p : List ℕ) (d c : Br), L[i]? = some d → subt d p = some c →
    sizeL (modL L i p) = sizeL L + 1
  | [], _, _, _, _, h, _ => by simp at h
  | e :: L, 0, p, d, c, h, hc => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp only [modL, sizeL]; rw [size_addLeaf p e c hc]; omega
  | e :: L, i + 1, p, d, c, h, hc => by
      simp only [List.getElem?_cons_succ] at h
      simp only [modL, sizeL]; rw [sizeL_modL L i p d c h hc]; omega
end

end Br

end LeanCherry
