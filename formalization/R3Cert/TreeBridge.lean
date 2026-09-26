/-
  R3Cert.TreeBridge -- the path graph of a `UTree` is the realized graph of the formalization.

  `Step3.realize (dtRealize t)` lists the edges of `t` with vertices named by ADDRESSES: the path of
  child indices from the root, written in reverse.  `keyIn_node` identifies its edges exactly:
  an edge joins `q.reverse` to `(q ++ [j]).reverse` for every path `q ++ [j]` of `t`.  Hence
  `addrGraph_iso_aGraph`: for a tree with at least two vertices, reversing paths is a graph isomorphism
  from `TreePaths.addrGraph t` onto `aGraph (Step3.realize (dtRealize t))`.
  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.TreePaths
import R3Cert.R47Tree

namespace R3Cert
namespace TreeBridge

open Step3 TreePaths

/-- `E` contains an edge from `u` to `v` (in this orientation). -/
def KeyIn (E : List AEdge) (u v : List ℕ) : Prop := ∃ e ∈ E, e.1 = u ∧ e.2.1 = v

theorem keyIn_append (E F : List AEdge) (u v : List ℕ) :
    KeyIn (E ++ F) u v ↔ KeyIn E u v ∨ KeyIn F u v := by
  simp only [KeyIn, List.mem_append]
  constructor
  · rintro ⟨e, he | he, h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, Or.inl he, h⟩
    · exact ⟨e, Or.inr he, h⟩

/-- The root's own edges. -/
theorem keyIn_root (b : List ℕ) (d : ℕ) : ∀ (i : ℕ) (cs : List UTree) (u v : List ℕ),
    KeyIn (rRoot b i (dtChildren d cs)) u v ↔ u = b ∧ ∃ k < cs.length, v = (i + k) :: b
  | i, [], u, v => by simp [KeyIn, dtChildren_nil, rRoot_nil]
  | i, K :: rest, u, v => by
    rw [dtChildren_cons, rRoot]
    have ih := keyIn_root b d (i + 1) rest u v
    unfold KeyIn at ih ⊢
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [ih]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, k, hk, h2⟩)
      · exact ⟨h1.symm, 0, by simp, by simpa using h2.symm⟩
      · exact ⟨h1, k + 1, by simp; omega, by rw [h2]; congr 1; omega⟩
    · rintro ⟨h1, k, hk, h2⟩
      cases k with
      | zero => exact Or.inl ⟨h1.symm, by simpa using h2.symm⟩
      | succ k => exact Or.inr ⟨h1, k, by simp at hk; omega, by rw [h2]; congr 1; omega⟩

mutual
/-- The edges of the realization of `t` rooted at address `b`. -/
theorem keyIn_node : ∀ (t : UTree) (b : List ℕ) (d : ℕ) (u v : List ℕ),
    KeyIn (rEdges b (RTree.node (dtChildren d (match t with | .node cs => cs)))) u v ↔
      ∃ q j, q ++ [j] ∈ paths t ∧ u = q.reverse ++ b ∧ v = j :: (q.reverse ++ b)
  | .node cs, b, d, u, v => by
    simp only
    rw [rEdges, keyIn_append, keyIn_root, keyIn_ch cs b 0 d u v]
    constructor
    · rintro (⟨rfl, k, hk, rfl⟩ | ⟨k, hk, q, j, hq, rfl, rfl⟩)
      · refine ⟨[], k, ?_, by simp, by simp⟩
        rw [List.nil_append, cons_mem_paths]; exact ⟨hk, nil_mem_paths _⟩
      · refine ⟨k :: q, j, ?_, by simp, by simp⟩
        rw [List.cons_append, cons_mem_paths]; exact ⟨hk, by simpa using hq⟩
    · rintro ⟨q, j, hq, rfl, rfl⟩
      cases q with
      | nil =>
        rw [List.nil_append, cons_mem_paths] at hq
        obtain ⟨hj, _⟩ := hq
        exact Or.inl ⟨by simp, j, hj, by simp⟩
      | cons k q' =>
        rw [List.cons_append, cons_mem_paths] at hq
        obtain ⟨hk, hq'⟩ := hq
        exact Or.inr ⟨k, hk, q', j, hq', by simp, by simp⟩
/-- The edges below the root's children `cs`, numbered from `i`. -/
theorem keyIn_ch : ∀ (cs : List UTree) (b : List ℕ) (i d : ℕ) (u v : List ℕ),
    KeyIn (rSub b i (dtChildren d cs)) u v ↔
      ∃ k, ∃ hk : k < cs.length, ∃ q j, q ++ [j] ∈ paths (cs[k]'hk) ∧
        u = q.reverse ++ ((i + k) :: b) ∧ v = j :: (q.reverse ++ ((i + k) :: b))
  | [], b, i, d, u, v => by simp [KeyIn, dtChildren_nil, rSub_nil]
  | K :: rest, b, i, d, u, v => by
    rw [dtChildren_cons, rSub, keyIn_append]
    have hK : dtSub K = RTree.node (dtChildren (udeg K) (match K with | .node cs => cs)) := by
      cases K with | node kcs => rw [dtSub_node, udeg_node]
    rw [hK, keyIn_node K (i :: b) (udeg K) u v, keyIn_ch rest b (i + 1) d u v]
    have e : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
    constructor
    · rintro (⟨q, j, hq, rfl, rfl⟩ | ⟨k, hk, q, j, hq, rfl, rfl⟩)
      · exact ⟨0, by simp, q, j, by simpa using hq, by simp, by simp⟩
      · exact ⟨k + 1, by simp; omega, q, j, by simpa using hq, by rw [e], by rw [e]⟩
    · rintro ⟨k, hk, q, j, hq, rfl, rfl⟩
      cases k with
      | zero => exact Or.inl ⟨q, j, by simpa using hq, by simp, by simp⟩
      | succ k =>
        exact Or.inr ⟨k, by simp at hk; omega, q, j, by simpa using hq, by rw [e], by rw [e]⟩
end

/-- The edges of the realized tree. -/
theorem keyIn_realize (t : UTree) (u v : List ℕ) :
    KeyIn (Step3.realize (dtRealize t)) u v ↔
      ∃ q j, q ++ [j] ∈ paths t ∧ u = q.reverse ∧ v = j :: q.reverse := by
  cases t with
  | node cs =>
    rw [Step3.realize, dtRealize_node]
    have := keyIn_node (.node cs) [] cs.length u v
    simpa using this

theorem hasKey_iff (E : List AEdge) (u v : List ℕ) : HasKey E u v ↔ KeyIn E u v ∨ KeyIn E v u := by
  simp only [HasKey, KeyIn]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨e, he, h1, h2⟩
    · exact Or.inr ⟨e, he, h1, h2⟩
  · rintro (⟨e, he, h1, h2⟩ | ⟨e, he, h1, h2⟩)
    · exact ⟨e, he, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨e, he, Or.inr ⟨h1, h2⟩⟩

theorem mem_vertsOf_iff (E : List AEdge) (a : List ℕ) :
    a ∈ (vertsOf E).toFinset ↔ (∃ v, KeyIn E a v) ∨ (∃ u, KeyIn E u a) := by
  simp only [List.mem_toFinset, vertsOf, List.mem_append, List.mem_map, KeyIn]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact Or.inl ⟨e.2.1, e, he, rfl, rfl⟩
    · exact Or.inr ⟨e.1, e, he, rfl, rfl⟩
  · rintro (⟨v, e, he, rfl, _⟩ | ⟨u, e, he, _, rfl⟩)
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩

/-- The vertices of the realized tree are the reversed paths (at least two vertices). -/
theorem mem_verts_realize (t : UTree) (ht : 2 ≤ usize t) (a : List ℕ) :
    a ∈ (vertsOf (Step3.realize (dtRealize t))).toFinset ↔ a.reverse ∈ paths t := by
  rw [mem_vertsOf_iff]
  simp only [keyIn_realize]
  constructor
  · rintro (⟨v, q, j, hq, rfl, rfl⟩ | ⟨u, q, j, hq, rfl, rfl⟩)
    · rw [List.reverse_reverse]; exact mem_paths_of_append t q [j] hq
    · simpa using hq
  · intro h
    rcases List.eq_nil_or_concat a.reverse with h0 | ⟨q, j, hqj⟩
    · -- the root: it has a child since the tree has at least two vertices
      have ha : a = [] := List.reverse_eq_nil_iff.mp h0
      subst ha
      cases t with
      | node cs =>
        have hcs : 0 < cs.length := by
          cases cs with
          | nil => rw [usize_node, usizeList_nil] at ht; omega
          | cons K rest => simp
        refine Or.inl ⟨[0], [], 0, ?_, rfl, rfl⟩
        rw [List.nil_append, cons_mem_paths]; exact ⟨hcs, nil_mem_paths _⟩
    · have hq' : q ++ [j] ∈ paths t := by rw [← List.concat_eq_append, ← hqj]; exact h
      refine Or.inr ⟨q.reverse, q, j, hq', rfl, ?_⟩
      have := congrArg List.reverse hqj
      simpa using this

/-- **Reversing paths is an isomorphism from the path graph onto the realized graph.** -/
noncomputable def addrGraphIso (t : UTree) (ht : 2 ≤ usize t) :
    addrGraph t ≃g aGraph (Step3.realize (dtRealize t)) where
  toFun x := ⟨x.1.reverse, (mem_verts_realize t ht _).mpr (by simpa using x.2)⟩
  invFun a := ⟨a.1.reverse, (mem_verts_realize t ht _).mp a.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)
  map_rel_iff' := by
    intro x y
    simp only [Equiv.coe_fn_mk, aGraph_adj, hasKey_iff, keyIn_realize]
    show _ ↔ PathAdj x.1 y.1
    constructor
    · rintro ⟨_, ⟨q, j, _, h1, h2⟩ | ⟨q, j, _, h1, h2⟩⟩
      · left; refine ⟨j, ?_⟩
        have e1 := congrArg List.reverse h1; have e2 := congrArg List.reverse h2
        simp at e1 e2; rw [e2, e1]
      · right; refine ⟨j, ?_⟩
        have e1 := congrArg List.reverse h1; have e2 := congrArg List.reverse h2
        simp at e1 e2; rw [e2, e1]
    · intro h
      refine ⟨?_, ?_⟩
      · intro he
        have := congrArg List.reverse (congrArg Subtype.val he)
        simp only [List.reverse_reverse] at this
        exact pathAdj_irrefl x.1 (this ▸ h)
      · rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨x.1, j, hj ▸ y.2, by simp, by rw [hj]; simp⟩
        · exact Or.inr ⟨y.1, j, hj ▸ x.2, by simp, by rw [hj]; simp⟩

end TreeBridge
end R3Cert
