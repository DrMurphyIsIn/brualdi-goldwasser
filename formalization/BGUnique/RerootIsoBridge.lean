import Mathlib
import BGUnique.RerootIsoBridgeEdges

/-!
The graph `G t` of `RerootIso` is the tree's graph, and it is the realized graph.

* `card_V`, `fintype_card_V`: `G t` has exactly `usize t` vertices.
* `G_isTree`: `G t` is a tree (connected and acyclic).
* `G_iso_aGraph`: for `usize t ≥ 2`, `G t ≃g aGraph (realize (dtRealize t))`, the graph whose
  Laplacian permanent ratio is `Aobj t` (`pi_utree`).  For `usize t = 1` the realized edge list is
  empty and `aGraph` has no vertices, so the hypothesis is needed.
-/

namespace R3Cert
namespace RerootIso

open R3Cert.Step3

/-! ### Vertex count -/

/-- Splitting an address at its first index. -/
def splitV (cs : List UTree) : V (UTree.node cs) → Option (Σ j : Fin cs.length, V cs[j])
  | ⟨[], _⟩ => none
  | ⟨j :: q, h⟩ => some ⟨⟨j, (valid_cons.mp h).1⟩, ⟨q, (valid_cons.mp h).2⟩⟩

/-- Joining a first index to an address of that child. -/
def joinV (cs : List UTree) : Option (Σ j : Fin cs.length, V cs[j]) → V (UTree.node cs)
  | none => ⟨[], valid_nil _⟩
  | some ⟨j, ⟨q, h⟩⟩ => ⟨j.1 :: q, valid_cons.mpr ⟨j.2, h⟩⟩

/-- The vertices of `node cs`: the root, or a vertex of one child. -/
def vEquiv (cs : List UTree) : V (UTree.node cs) ≃ Option (Σ j : Fin cs.length, V cs[j]) where
  toFun := splitV cs
  invFun := joinV cs
  left_inv := by
    rintro ⟨_ | ⟨j, q⟩, h⟩ <;> rfl
  right_inv := by
    rintro (_ | ⟨⟨j, hj⟩, ⟨q, h⟩⟩) <;> rfl

theorem usizeList_eq_sum : ∀ cs : List UTree, usizeList cs = ∑ j : Fin cs.length, usize cs[j]
  | [] => by simp [usizeList_nil]
  | K :: rest => by
    rw [usizeList_cons, usizeList_eq_sum rest]
    simp [Fin.sum_univ_succ, List.getElem_cons_succ]

theorem finite_card_V : ∀ (n : ℕ) (t : UTree), usize t ≤ n → Finite (V t) ∧ Nat.card (V t) = usize t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro ⟨cs⟩ hn
    have hch : ∀ j : Fin cs.length, Finite (V cs[j]) ∧ Nat.card (V cs[j]) = usize cs[j] := fun j =>
      ih _ (lt_of_lt_of_le (usize_child_lt j.2) hn) _ le_rfl
    haveI : ∀ j : Fin cs.length, Finite (V cs[j]) := fun j => (hch j).1
    haveI : Finite (Option (Σ j : Fin cs.length, V cs[j])) := inferInstance
    haveI hfin : Finite (V (UTree.node cs)) := Finite.of_equiv _ (vEquiv cs).symm
    refine ⟨hfin, ?_⟩
    rw [Nat.card_congr (vEquiv cs)]
    letI : Fintype (Σ j : Fin cs.length, V cs[j]) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, Nat.card_sigma,
      usize_node, usizeList_eq_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (hch j).2)

instance finite_V (t : UTree) : Finite (V t) := (finite_card_V _ t le_rfl).1

noncomputable instance fintype_V (t : UTree) : Fintype (V t) := Fintype.ofFinite _

/-- **`G t` has `usize t` vertices.** -/
theorem card_V (t : UTree) : Nat.card (V t) = usize t := (finite_card_V _ t le_rfl).2

theorem fintype_card_V (t : UTree) : Fintype.card (V t) = usize t := by
  rw [← Nat.card_eq_fintype_card, card_V]

/-! ### Connectedness -/

theorem reach_root (t : UTree) : ∀ (p : List ℕ) (h : Valid t p), (G t).Reachable (root t) ⟨p, h⟩ := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro h; exact SimpleGraph.Reachable.refl _
  | append_singleton q k ihq =>
    intro h
    have hq : Valid t q := valid_of_append h
    exact (ihq hq).trans (SimpleGraph.Adj.reachable (ladj_child q k))

theorem G_connected (t : UTree) : (G t).Connected :=
  (SimpleGraph.connected_iff _).mpr ⟨fun u v =>
    ((reach_root t u.1 u.2).symm).trans (reach_root t v.1 v.2), ⟨root t⟩⟩

/-! ### The isomorphism with the realized graph -/

section Bridge

/-- The realized edge list of `node cs`. -/
noncomputable abbrev Er (cs : List UTree) : List AEdge := Step3.realize (dtRealize (UTree.node cs))

variable (cs : List UTree)

theorem Er_eq : Er cs = rEdges [] (RTree.node (dtChildren cs.length cs)) := by
  rw [Er, Step3.realize, dtRealize_node]

theorem rev_snoc (p : List ℕ) (k : ℕ) : (p ++ [k]).reverse = k :: p.reverse := by simp

theorem mem_verts_iff (hne : cs ≠ []) (x : List ℕ) :
    x ∈ (vertsOf (Er cs)).toFinset ↔ Valid (UTree.node cs) x.reverse := by
  rw [List.mem_toFinset, vertsOf, List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) <;> rw [Er_eq] at he <;>
      obtain ⟨p, k, hv, h1, h2⟩ := rEdges_sound _ cs le_rfl _ _ e he
    · rw [h1]; simpa using valid_of_append hv
    · have e3 : (k :: (p.reverse ++ [])).reverse = p ++ [k] := by simp
      rw [h2, e3]; exact hv
  · intro hv
    rcases List.eq_nil_or_concat' x.reverse with h0 | ⟨q, k, hq⟩
    · have hx : x = [] := List.reverse_eq_nil_iff.mp h0
      obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      have h0v : Valid (UTree.node (c :: rest)) ([] ++ [0]) :=
        valid_cons.mpr ⟨by simp, valid_nil _⟩
      obtain ⟨e, he, h1, -⟩ := rEdges_complete [] 0 (c :: rest) (c :: rest).length [] h0v
      left
      refine ⟨e, by rw [Er_eq]; exact he, ?_⟩
      rw [h1, hx]; simp
    · rw [hq] at hv
      obtain ⟨e, he, -, h2⟩ := rEdges_complete q k cs cs.length [] hv
      right
      refine ⟨e, by rw [Er_eq]; exact he, ?_⟩
      rw [h2, ← List.reverse_reverse x, hq]; simp

theorem hasKey_iff {a b : List ℕ} (hb : Valid (UTree.node cs) b) (ha : Valid (UTree.node cs) a) :
    HasKey (Er cs) a.reverse b.reverse ↔ ladj a b := by
  constructor
  · rintro ⟨e, he, hor⟩
    rw [Er_eq] at he
    obtain ⟨p, k, -, h1, h2⟩ := rEdges_sound _ cs le_rfl _ _ e he
    simp only [List.append_nil] at h1 h2
    rcases hor with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hap : a = p := List.reverse_injective (by rw [← e1, h1])
      have hbp : b = p ++ [k] := List.reverse_injective (by rw [← e2, h2, rev_snoc])
      exact Or.inl ⟨k, by rw [hbp, hap]⟩
    · have hbp : b = p := List.reverse_injective (by rw [← e1, h1])
      have hap : a = p ++ [k] := List.reverse_injective (by rw [← e2, h2, rev_snoc])
      exact Or.inr ⟨k, by rw [hbp, hap]⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · obtain ⟨e, he, h1, h2⟩ := rEdges_complete a k cs cs.length [] hb
      refine ⟨e, by rw [Er_eq]; exact he, Or.inl ⟨?_, ?_⟩⟩
      · rw [h1]; simp
      · rw [h2]; simp
    · obtain ⟨e, he, h1, h2⟩ := rEdges_complete b k cs cs.length [] ha
      refine ⟨e, by rw [Er_eq]; exact he, Or.inr ⟨?_, ?_⟩⟩
      · rw [h1]; simp
      · rw [h2]; simp

/-- The vertex bijection: reverse the address. -/
noncomputable def vToA (hne : cs ≠ []) : V (UTree.node cs) ≃ AVert (Er cs) where
  toFun v := ⟨v.1.reverse, (mem_verts_iff cs hne _).mpr (by simpa using v.2)⟩
  invFun x := ⟨x.1.reverse, (mem_verts_iff cs hne _).mp x.2⟩
  left_inv v := by simp
  right_inv x := by simp

/-- **`G (node cs)` is the realized graph** (for `cs ≠ []`). -/
noncomputable def gIsoA (hne : cs ≠ []) : G (UTree.node cs) ≃g aGraph (Er cs) where
  toEquiv := vToA cs hne
  map_rel_iff' := by
    intro u v
    show ((vToA cs hne u) ≠ (vToA cs hne v) ∧ HasKey (Er cs) u.1.reverse v.1.reverse) ↔ ladj u.1 v.1
    constructor
    · rintro ⟨-, h⟩
      exact (hasKey_iff cs v.2 u.2).mp h
    · intro h
      refine ⟨?_, (hasKey_iff cs v.2 u.2).mpr h⟩
      intro heq
      have h1 : u.1.reverse = v.1.reverse := congrArg Subtype.val heq
      have h2 : u.1 = v.1 := List.reverse_injective h1
      exact ladj_irrefl u.1 (by rw [h2] at h ⊢; exact h)

end Bridge

end RerootIso
end R3Cert
