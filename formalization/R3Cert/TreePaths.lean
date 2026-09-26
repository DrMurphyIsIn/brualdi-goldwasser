/-
  R3Cert.TreePaths -- every finite tree, in Mathlib's sense, is a `UTree`.

  A rooted tree `t : UTree` has a vertex for every path of child indices from the root (`paths t`).
  `addrGraph t` is the graph on those paths in which a path is adjacent to its one-step extensions.
  `tree_iso` shows that every `G : SimpleGraph V` with `G.IsTree` on a finite type `V` is isomorphic to
  `addrGraph t` for some `t` with `usize t = card V`.  The proof removes a leaf (Mathlib's
  `IsTree.exists_vert_degree_one_of_nontrivial`, `Connected.induce_compl_singleton_of_degree_eq_one`),
  applies induction, and re-attaches the leaf as a new last child (`addLeaf`), which leaves every other
  vertex's path unchanged.
  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.R47StepSize

namespace R3Cert
namespace TreePaths

open Step3

/-! ### Paths -/

mutual
/-- The vertices of `t`: paths of child indices from the root. -/
def paths : UTree → List (List ℕ)
  | .node cs => [] :: pathsCh 0 cs
/-- Paths into the children `cs`, numbered from `i`. -/
def pathsCh : ℕ → List UTree → List (List ℕ)
  | _, [] => []
  | i, K :: rest => (paths K).map (i :: ·) ++ pathsCh (i + 1) rest
end

theorem paths_node (cs : List UTree) : paths (.node cs) = [] :: pathsCh 0 cs := by rw [paths]

theorem nil_mem_paths (t : UTree) : [] ∈ paths t := by
  cases t with | node cs => rw [paths_node]; exact List.mem_cons_self

theorem not_nil_mem_pathsCh : ∀ (i : ℕ) (cs : List UTree), [] ∉ pathsCh i cs
  | _, [] => by simp [pathsCh]
  | i, K :: rest => by
    rw [pathsCh]; simp only [List.mem_append, List.mem_map]
    rintro (⟨q, _, h⟩ | h)
    · exact List.cons_ne_nil _ _ h
    · exact not_nil_mem_pathsCh (i + 1) rest h

theorem cons_mem_pathsCh : ∀ (i : ℕ) (cs : List UTree) (j : ℕ) (q : List ℕ),
    j :: q ∈ pathsCh i cs ↔ i ≤ j ∧ ∃ h : j - i < cs.length, q ∈ paths (cs[j - i]'h)
  | i, [], j, q => by simp [pathsCh]
  | i, K :: rest, j, q => by
    rw [pathsCh, List.mem_append, cons_mem_pathsCh (i + 1) rest j q]
    simp only [List.mem_map, List.cons.injEq]
    constructor
    · rintro (⟨q', hq', rfl, rfl⟩ | ⟨hle, hlt, hq⟩)
      · exact ⟨le_rfl, by simp, by simpa using hq'⟩
      · refine ⟨by omega, by simp; omega, ?_⟩
        have e : j - i = (j - (i + 1)) + 1 := by omega
        simp only [e, List.getElem_cons_succ]; exact hq
    · rintro ⟨hle, hlt, hq⟩
      by_cases hji : j = i
      · subst hji; exact Or.inl ⟨q, by simpa using hq, rfl, rfl⟩
      · refine Or.inr ⟨by omega, by simp at hlt; omega, ?_⟩
        have e : j - i = (j - (i + 1)) + 1 := by omega
        simp only [e, List.getElem_cons_succ] at hq; exact hq

theorem cons_mem_paths (cs : List UTree) (j : ℕ) (q : List ℕ) :
    j :: q ∈ paths (.node cs) ↔ ∃ h : j < cs.length, q ∈ paths (cs[j]'h) := by
  rw [paths_node, List.mem_cons, cons_mem_pathsCh]
  simp only [List.cons_ne_nil, false_or, zero_le, true_and, Nat.sub_zero]

/-- Paths are closed under taking prefixes. -/
theorem mem_paths_of_append : ∀ (t : UTree) (q r : List ℕ), q ++ r ∈ paths t → q ∈ paths t
  | t, [], _, _ => nil_mem_paths t
  | .node cs, j :: q, r, h => by
    rw [List.cons_append, cons_mem_paths] at h
    obtain ⟨hj, hq⟩ := h
    exact (cons_mem_paths cs j q).mpr ⟨hj, mem_paths_of_append _ q r hq⟩

/-! ### Counting -/

mutual
theorem length_paths : ∀ t : UTree, (paths t).length = usize t
  | .node cs => by rw [paths_node, List.length_cons, length_pathsCh 0 cs, usize_node]; omega
theorem length_pathsCh : ∀ (i : ℕ) (cs : List UTree), (pathsCh i cs).length = usizeList cs
  | _, [] => by rw [pathsCh, usizeList_nil]; rfl
  | i, K :: rest => by
    rw [pathsCh, List.length_append, List.length_map, length_paths K, length_pathsCh (i + 1) rest,
      usizeList_cons]
end

theorem head_ge_of_mem_pathsCh (i : ℕ) (cs : List UTree) (q : List ℕ) (h : q ∈ pathsCh i cs) :
    ∃ j q', q = j :: q' ∧ i ≤ j := by
  cases q with
  | nil => exact absurd h (not_nil_mem_pathsCh i cs)
  | cons j q' => exact ⟨j, q', rfl, ((cons_mem_pathsCh i cs j q').mp h).1⟩

mutual
theorem nodup_paths : ∀ t : UTree, (paths t).Nodup
  | .node cs => by
    rw [paths_node]
    exact List.nodup_cons.mpr ⟨not_nil_mem_pathsCh 0 cs, nodup_pathsCh 0 cs⟩
theorem nodup_pathsCh : ∀ (i : ℕ) (cs : List UTree), (pathsCh i cs).Nodup
  | _, [] => by rw [pathsCh]; exact List.nodup_nil
  | i, K :: rest => by
    rw [pathsCh]
    refine List.Nodup.append ((nodup_paths K).map (fun a b h => List.cons_injective h))
      (nodup_pathsCh (i + 1) rest) ?_
    intro q hq hq'
    obtain ⟨q0, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨j, _, he, hj⟩ := head_ge_of_mem_pathsCh (i + 1) rest _ hq'
    injection he with h1; omega
end

/-! ### Adding a leaf -/

/-- Number of children at the root. -/
def nch : UTree → ℕ
  | .node cs => cs.length

/-- The subtree at a path (a leaf if the path is not valid). -/
def sub : UTree → List ℕ → UTree
  | t, [] => t
  | .node cs, i :: p => if h : i < cs.length then sub (cs[i]'h) p else .node []

/-- Attach a new leaf as the last child of the vertex at path `p`. -/
def addLeaf : UTree → List ℕ → UTree
  | .node cs, [] => .node (cs ++ [.node []])
  | .node cs, i :: p => .node (cs.modify i (fun K => addLeaf K p))

theorem paths_leaf : paths (.node []) = [[]] := by rw [paths_node, pathsCh]

theorem mem_paths_leaf (q : List ℕ) : q ∈ paths (.node []) ↔ q = [] := by
  rw [paths_leaf]; simp

/-- The paths of `addLeaf t p`: the old ones and one new path. -/
theorem mem_paths_addLeaf : ∀ (t : UTree) (p : List ℕ), p ∈ paths t → ∀ q : List ℕ,
    (q ∈ paths (addLeaf t p) ↔ q ∈ paths t ∨ q = p ++ [nch (sub t p)])
  | .node cs, [], _, q => by
    rw [addLeaf, sub, nch]
    cases q with
    | nil => simp [nil_mem_paths]
    | cons j q' =>
      rw [cons_mem_paths, cons_mem_paths]
      simp only [List.length_append, List.length_singleton, List.nil_append, List.cons.injEq]
      constructor
      · rintro ⟨hj, hq⟩
        by_cases hlt : j < cs.length
        · left; refine ⟨hlt, ?_⟩; rwa [List.getElem_append_left hlt] at hq
        · right
          have hje : j = cs.length := by omega
          subst hje
          rw [List.getElem_append_right (le_refl _)] at hq
          simp only [Nat.sub_self, List.getElem_cons_zero] at hq
          exact ⟨rfl, (mem_paths_leaf q').mp hq⟩
      · rintro (⟨hj, hq⟩ | ⟨rfl, rfl⟩)
        · exact ⟨by omega, by rwa [List.getElem_append_left hj]⟩
        · refine ⟨by omega, ?_⟩
          rw [List.getElem_append_right (le_refl _)]
          simp [mem_paths_leaf]
  | .node cs, i :: p, hp, q => by
    obtain ⟨hi, hp'⟩ := (cons_mem_paths cs i p).mp hp
    rw [addLeaf]
    have hsub : sub (.node cs) (i :: p) = sub (cs[i]'hi) p := by rw [sub, dif_pos hi]
    rw [hsub]
    cases q with
    | nil => simp [nil_mem_paths]
    | cons j q' =>
      rw [cons_mem_paths, cons_mem_paths]
      simp only [List.length_modify, List.cons_append, List.cons.injEq]
      by_cases hji : j = i
      · subst hji
        have ih := mem_paths_addLeaf (cs[j]'hi) p hp' q'
        simp only [List.getElem_modify, true_and]
        constructor
        · rintro ⟨_, hq⟩; rcases ih.mp hq with h | h
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr h
        · rintro (⟨_, hq⟩ | hq)
          · exact ⟨hi, ih.mpr (Or.inl hq)⟩
          · exact ⟨hi, ih.mpr (Or.inr hq)⟩
      · simp only [hji, false_and, or_false]
        constructor
        · rintro ⟨hj, hq⟩
          refine ⟨hj, ?_⟩
          rwa [List.getElem_modify, if_neg (Ne.symm hji)] at hq
        · rintro ⟨hj, hq⟩
          refine ⟨hj, ?_⟩
          rwa [List.getElem_modify, if_neg (Ne.symm hji)]

/-- The new path is fresh. -/
theorem fresh_not_mem : ∀ (t : UTree) (p : List ℕ), p ++ [nch (sub t p)] ∉ paths t
  | .node cs, [] => by
    rw [sub, nch, List.nil_append, cons_mem_paths]; rintro ⟨h, _⟩; omega
  | .node cs, i :: p => by
    rw [List.cons_append, cons_mem_paths]
    rintro ⟨hi, hq⟩
    rw [sub, dif_pos hi] at hq
    exact fresh_not_mem _ p hq

theorem usizeList_modify (f : UTree → UTree) :
    ∀ (cs : List UTree) (i : ℕ) (hi : i < cs.length), usize (f (cs[i]'hi)) = usize (cs[i]'hi) + 1 →
      usizeList (cs.modify i f) = usizeList cs + 1
  | [], i, hi, _ => absurd hi (by simp)
  | K :: rest, 0, _, h => by
    simp only [List.modify_zero_cons, usizeList_cons]
    simp only [List.getElem_cons_zero] at h; omega
  | K :: rest, i + 1, hi, h => by
    simp only [List.modify_succ_cons, usizeList_cons]
    simp only [List.getElem_cons_succ] at h
    have := usizeList_modify f rest i (by simpa using hi) h; omega

theorem usize_addLeaf : ∀ (t : UTree) (p : List ℕ), p ∈ paths t → usize (addLeaf t p) = usize t + 1
  | .node cs, [], _ => by
    rw [addLeaf, usize_node, usize_node, usizeList_append, usizeList_cons, usizeList_nil, usize_node,
      usizeList_nil]; omega
  | .node cs, i :: p, hp => by
    obtain ⟨hi, hp'⟩ := (cons_mem_paths cs i p).mp hp
    rw [addLeaf, usize_node, usize_node,
      usizeList_modify (fun K => addLeaf K p) cs i hi (usize_addLeaf _ p hp')]
    omega

/-! ### The path graph -/

/-- The vertex type of `t`. -/
abbrev VP (t : UTree) := {q : List ℕ // q ∈ paths t}

/-- Adjacent paths: one extends the other by one step. -/
def PathAdj (a b : List ℕ) : Prop := (∃ j, b = a ++ [j]) ∨ (∃ j, a = b ++ [j])

theorem pathAdj_irrefl (a : List ℕ) : ¬ PathAdj a a := by
  rintro (⟨j, h⟩ | ⟨j, h⟩) <;> have := congrArg List.length h <;> simp at this

/-- The graph of a rooted tree on its paths. -/
def addrGraph (t : UTree) : SimpleGraph (VP t) where
  Adj x y := PathAdj x.1 y.1
  symm := ⟨fun a b h => by unfold PathAdj at h ⊢; exact h.symm⟩
  loopless := ⟨fun x h => pathAdj_irrefl x.1 h⟩

/-! ### Every tree is a `UTree` -/

theorem tree_iso_aux : ∀ (m : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V), G.IsTree →
    Fintype.card V = m → ∃ t : UTree, usize t = m ∧ Nonempty (G ≃g addrGraph t) := by
  intro m
  induction m with
  | zero =>
    intro V _ G hG hc
    haveI := hG.1.nonempty
    exact absurd hc Fintype.card_ne_zero
  | succ m ih =>
    intro V _ G hG hc
    classical
    by_cases hm : m = 0
    · -- one vertex
      subst hm
      refine ⟨.node [], by rw [usize_node, usizeList_nil], ?_⟩
      have hV : Fintype.card V = 1 := hc
      obtain ⟨v0, hv0⟩ := Fintype.card_eq_one_iff.mp hV
      let e : V ≃ VP (.node []) :=
        { toFun := fun _ => ⟨[], nil_mem_paths _⟩
          invFun := fun _ => v0
          left_inv := fun v => (hv0 v).symm
          right_inv := fun x => Subtype.ext ((mem_paths_leaf x.1).mp x.2).symm }
      refine ⟨⟨e, ?_⟩⟩
      intro a b
      rw [hv0 a, hv0 b]
      simp only [G.irrefl, iff_false]
      exact (addrGraph (.node [])).loopless.irrefl _
    · -- remove a leaf
      have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨l, hl⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨p0, hadj, huniq⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hl
      set G' := G.induce ({l}ᶜ : Set V) with hG'
      have hconn : G'.Connected := hG.1.induce_compl_singleton_of_degree_eq_one hl
      have hacyc : G'.IsAcyclic := hG.2.induce _
      have hcard : Fintype.card ({l}ᶜ : Set V) = m := by
        simp only [Fintype.card_compl_set, Set.card_singleton]; omega
      obtain ⟨t', ht', ⟨φ⟩⟩ := ih G' ⟨hconn, hacyc⟩ hcard
      have hp0 : p0 ∈ ({l}ᶜ : Set V) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact G.ne_of_adj hadj |>.symm
      set a := (φ ⟨p0, hp0⟩).1 with ha
      have haMem : a ∈ paths t' := (φ ⟨p0, hp0⟩).2
      set new := a ++ [nch (sub t' a)] with hnew
      have hfresh : new ∉ paths t' := fresh_not_mem t' a
      have hmem := mem_paths_addLeaf t' a haMem
      let ψ : V → VP (addLeaf t' a) := fun v =>
        if h : v = l then ⟨new, (hmem new).mpr (Or.inr rfl)⟩
        else ⟨(φ ⟨v, h⟩).1, (hmem _).mpr (Or.inl (φ ⟨v, h⟩).2)⟩
      have hψl : (ψ l).1 = new := by simp [ψ]
      have hψv : ∀ v (h : v ≠ l), (ψ v).1 = (φ ⟨v, h⟩).1 := by intro v h; simp [ψ, h]
      have hne : ∀ v (h : v ≠ l), (φ ⟨v, h⟩).1 ≠ new := by
        intro v h he; exact hfresh (he ▸ (φ ⟨v, h⟩).2)
      have hinj : Function.Injective ψ := by
        intro v w hvw
        have hvw' := congrArg Subtype.val hvw
        by_cases hv : v = l <;> by_cases hw : w = l
        · rw [hv, hw]
        · rw [hv, hψl, hψv w hw] at hvw'; exact absurd hvw'.symm (hne w hw)
        · rw [hw, hψl, hψv v hv] at hvw'; exact absurd hvw' (hne v hv)
        · rw [hψv v hv, hψv w hw] at hvw'
          have := φ.injective (Subtype.ext hvw')
          simpa using this
      have hsurj : Function.Surjective ψ := by
        rintro ⟨q, hq⟩
        rcases (hmem q).mp hq with h | h
        · obtain ⟨⟨w, hw⟩, hwq⟩ := φ.surjective ⟨q, h⟩
          have hwl : w ≠ l := by simpa using hw
          refine ⟨w, Subtype.ext ?_⟩
          rw [hψv w hwl]; exact congrArg Subtype.val hwq
        · exact ⟨l, Subtype.ext (by show (ψ l).1 = q; rw [hψl, h])⟩
      refine ⟨addLeaf t' a, by rw [usize_addLeaf t' a haMem, ht'], ⟨⟨Equiv.ofBijective ψ ⟨hinj, hsurj⟩, ?_⟩⟩⟩
      intro v w
      show PathAdj (ψ v).1 (ψ w).1 ↔ G.Adj v w
      -- adjacency to the new leaf
      have leafAdj : ∀ u (hu : u ≠ l), PathAdj new (φ ⟨u, hu⟩).1 ↔ u = p0 := by
        intro u hu
        constructor
        · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
          · exact absurd (mem_paths_of_append t' new [j] (hj ▸ (φ ⟨u, hu⟩).2)) hfresh
          · rw [hnew] at hj
            have h2 := List.append_inj_left' hj rfl
            have := φ.injective (Subtype.ext h2.symm)
            simpa using this
        · rintro rfl; exact Or.inr ⟨nch (sub t' a), rfl⟩
      by_cases hv : v = l <;> by_cases hw : w = l
      · subst hv; subst hw; rw [hψl]; simp only [G.irrefl, iff_false]; exact pathAdj_irrefl _
      · subst hv
        rw [hψl, hψv w hw, leafAdj w hw]
        constructor
        · rintro rfl; exact hadj
        · intro h; exact huniq w h
      · subst hw
        rw [hψl, hψv v hv]
        constructor
        · intro h; rw [(leafAdj v hv).mp h.symm]; exact hadj.symm
        · intro h; exact ((leafAdj v hv).mpr (huniq v h.symm)).symm
      · rw [hψv v hv, hψv w hw]
        have := φ.map_rel_iff (a := ⟨v, hv⟩) (b := ⟨w, hw⟩)
        exact this

/-- **Every finite tree is the path graph of a `UTree` of the same size.** -/
theorem tree_iso {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    ∃ t : UTree, usize t = Fintype.card V ∧ Nonempty (G ≃g addrGraph t) :=
  tree_iso_aux _ G hG rfl

end TreePaths
end R3Cert
