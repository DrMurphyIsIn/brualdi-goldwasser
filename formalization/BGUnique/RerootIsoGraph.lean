import Mathlib
import BGUnique.RerootEquiv

/-!
The graph of a rooted tree, and soundness of rerooting.

A vertex of `t : UTree` is an *address*: the list of child indices on the path from the root
(`[]` is the root).  `G t` is the simple graph on the valid addresses whose edges join each address
to its children (`p` and `p ++ [k]`).  `UIso t t'` is isomorphism of these graphs as unrooted
simple graphs (`SimpleGraph.Iso`).  The two `RerootRel` moves are graph isomorphisms
(`uiso_of_rerootRel`).
-/

namespace R3Cert
namespace RerootIso

open R3Cert.Step3

/-! ### Addresses and the graph -/

/-- The children of a node. -/
def kids : UTree → List UTree
  | .node cs => cs

@[simp] theorem kids_node (cs : List UTree) : kids (UTree.node cs) = cs := rfl

/-- The subtree at an address, if the address exists. -/
def sub : UTree → List ℕ → Option UTree
  | t, [] => some t
  | t, i :: p => ((kids t)[i]?).bind (fun c => sub c p)

/-- `p` is the address of a vertex of `t`. -/
abbrev Valid (t : UTree) (p : List ℕ) : Prop := (sub t p).isSome = true

/-- The vertices of `t`. -/
abbrev V (t : UTree) : Type := {p : List ℕ // Valid t p}

/-- Two addresses are adjacent when one is a child of the other. -/
def ladj (a b : List ℕ) : Prop := (∃ k, b = a ++ [k]) ∨ (∃ k, a = b ++ [k])

theorem ladj_irrefl (a : List ℕ) : ¬ ladj a a := by
  rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> have := congrArg List.length hk <;> simp at this

/-- The (unrooted) graph of `t`: valid addresses, joined parent to child. -/
def G (t : UTree) : SimpleGraph (V t) where
  Adj a b := ladj a.1 b.1
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun a h => ladj_irrefl a.1 h⟩

/-- Isomorphism as unrooted trees: an isomorphism of the graphs. -/
def UIso (t t' : UTree) : Prop := Nonempty (G t ≃g G t')

/-- The root of `t`. -/
def root (t : UTree) : V t := ⟨[], rfl⟩

/-! ### Address lemmas -/

theorem ladj_child (a : List ℕ) (k : ℕ) : ladj a (a ++ [k]) := Or.inl ⟨k, rfl⟩

theorem ladj_cons_cons {i j : ℕ} {a b : List ℕ} : ladj (i :: a) (j :: b) ↔ i = j ∧ ladj a b := by
  unfold ladj
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · simp only [List.cons_append, List.cons.injEq] at hk; exact ⟨hk.1.symm, Or.inl ⟨k, hk.2⟩⟩
    · simp only [List.cons_append, List.cons.injEq] at hk; exact ⟨hk.1, Or.inr ⟨k, hk.2⟩⟩
  · rintro ⟨rfl, (⟨k, hk⟩ | ⟨k, hk⟩)⟩
    · exact Or.inl ⟨k, by simp [hk]⟩
    · exact Or.inr ⟨k, by simp [hk]⟩

theorem ladj_nil_left {b : List ℕ} : ladj [] b ↔ ∃ k, b = [k] := by
  unfold ladj
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨k, by simpa using hk⟩
    · exact absurd hk (by simp)
  · rintro ⟨k, rfl⟩; exact Or.inl ⟨k, rfl⟩

/-- A map that sends every child edge to an edge (on valid addresses) preserves adjacency. -/
theorem ladj_map {P : List ℕ → Prop} {f : List ℕ → List ℕ}
    (hf : ∀ a k, P (a ++ [k]) → ladj (f a) (f (a ++ [k]))) {a b : List ℕ} (ha : P a) (hb : P b)
    (h : ladj a b) : ladj (f a) (f b) := by
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact hf a k hb
  · exact Or.symm (hf b k ha)

theorem sub_cons (cs : List UTree) (i : ℕ) (p : List ℕ) :
    sub (UTree.node cs) (i :: p) = (cs[i]?).bind (fun c => sub c p) := rfl

theorem valid_nil (t : UTree) : Valid t [] := rfl

theorem valid_cons {cs : List UTree} {i : ℕ} {p : List ℕ} :
    Valid (UTree.node cs) (i :: p) ↔ ∃ h : i < cs.length, Valid cs[i] p := by
  unfold Valid
  rw [sub_cons]
  by_cases h : i < cs.length
  · simp [h]
  · simp [h]

theorem sub_append (t : UTree) (p q : List ℕ) : sub t (p ++ q) = (sub t p).bind (fun s => sub s q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i p ih =>
    obtain ⟨cs⟩ := t
    simp only [List.cons_append, sub_cons]
    cases cs[i]? with
    | none => rfl
    | some c => simp [ih]

theorem valid_of_append {t : UTree} {p q : List ℕ} (h : Valid t (p ++ q)) : Valid t p := by
  unfold Valid at *
  rw [sub_append] at h
  cases hs : sub t p with
  | none => rw [hs] at h; simp at h
  | some s => rfl

/-! ### Isomorphisms from address maps -/

/-- A graph isomorphism from mutually inverse address maps that preserve child edges. -/
def isoOfMaps {t t' : UTree} (f g : List ℕ → List ℕ)
    (hf : ∀ p, Valid t p → Valid t' (f p)) (hg : ∀ p, Valid t' p → Valid t (g p))
    (hgf : ∀ p, Valid t p → g (f p) = p) (hfg : ∀ p, Valid t' p → f (g p) = p)
    (hfa : ∀ a k, Valid t (a ++ [k]) → ladj (f a) (f (a ++ [k])))
    (hga : ∀ a k, Valid t' (a ++ [k]) → ladj (g a) (g (a ++ [k]))) :
    G t ≃g G t' where
  toFun p := ⟨f p.1, hf _ p.2⟩
  invFun p := ⟨g p.1, hg _ p.2⟩
  left_inv p := Subtype.ext (hgf _ p.2)
  right_inv p := Subtype.ext (hfg _ p.2)
  map_rel_iff' {a b} := by
    show ladj (f a.1) (f b.1) ↔ ladj a.1 b.1
    constructor
    · intro h
      have := ladj_map hga (hf _ a.2) (hf _ b.2) h
      rwa [hgf _ a.2, hgf _ b.2] at this
    · exact ladj_map hfa a.2 b.2

theorem isoOfMaps_apply {t t' : UTree} (f g : List ℕ → List ℕ) (hf hg hgf hfg hfa hga) (v : V t) :
    ((isoOfMaps (t := t) (t' := t') f g hf hg hgf hfg hfa hga) v).1 = f v.1 := rfl

/-! ### Reordering children -/

/-- Relabel the first index. -/
def permF (σ : ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | j :: q => σ j :: q

theorem permF_child (σ : ℕ → ℕ) (a : List ℕ) (k : ℕ) : ladj (permF σ a) (permF σ (a ++ [k])) := by
  cases a with
  | nil => exact Or.inl ⟨σ k, rfl⟩
  | cons j q => exact Or.inl ⟨k, rfl⟩

/-- An index bijection between two child lists that matches the children. -/
def IdxBij {α : Type*} (cs cs' : List α) (σ τ : ℕ → ℕ) : Prop :=
  (∀ j (h : j < cs.length), ∃ h' : σ j < cs'.length, cs'[σ j] = cs[j]) ∧
  (∀ j (h : j < cs'.length), ∃ h' : τ j < cs.length, cs[τ j] = cs'[j]) ∧
  (∀ j, j < cs.length → τ (σ j) = j) ∧ (∀ j, j < cs'.length → σ (τ j) = j)

/-- Reordering the root's children, along an index bijection. -/
def permIso (cs cs' : List UTree) (σ τ : ℕ → ℕ) (H : IdxBij cs cs' σ τ) :
    G (UTree.node cs) ≃g G (UTree.node cs') :=
  isoOfMaps (permF σ) (permF τ)
    (by
      intro p hp
      cases p with
      | nil => exact valid_nil _
      | cons j q =>
        obtain ⟨h, hq⟩ := valid_cons.mp hp
        obtain ⟨h', e⟩ := H.1 j h
        exact valid_cons.mpr ⟨h', by rw [e]; exact hq⟩)
    (by
      intro p hp
      cases p with
      | nil => exact valid_nil _
      | cons j q =>
        obtain ⟨h, hq⟩ := valid_cons.mp hp
        obtain ⟨h', e⟩ := H.2.1 j h
        exact valid_cons.mpr ⟨h', by rw [e]; exact hq⟩)
    (by
      intro p hp
      cases p with
      | nil => rfl
      | cons j q =>
        obtain ⟨h, _⟩ := valid_cons.mp hp
        show τ (σ j) :: q = j :: q
        rw [H.2.2.1 j h])
    (by
      intro p hp
      cases p with
      | nil => rfl
      | cons j q =>
        obtain ⟨h, _⟩ := valid_cons.mp hp
        show σ (τ j) :: q = j :: q
        rw [H.2.2.2 j h])
    (fun a k _ => permF_child σ a k) (fun a k _ => permF_child τ a k)

theorem permIso_apply (cs cs' : List UTree) (σ τ : ℕ → ℕ) (H : IdxBij cs cs' σ τ) (v : V (UTree.node cs)) :
    (permIso cs cs' σ τ H v).1 = permF σ v.1 := rfl

/-- Every list permutation has a matching index bijection. -/
theorem idxBij_of_perm {α : Type*} {cs cs' : List α} (hp : cs.Perm cs') : ∃ σ τ, IdxBij cs cs' σ τ := by
  induction hp with
  | nil => exact ⟨id, id, fun j h => absurd h (by simp), fun j h => absurd h (by simp),
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x _ ih =>
    obtain ⟨σ, τ, h1, h2, h3, h4⟩ := ih
    refine ⟨fun j => match j with | 0 => 0 | j + 1 => σ j + 1,
      fun j => match j with | 0 => 0 | j + 1 => τ j + 1, ?_, ?_, ?_, ?_⟩
    · intro j h
      cases j with
      | zero => exact ⟨by simp, rfl⟩
      | succ j =>
        obtain ⟨h', e⟩ := h1 j (by simpa using h)
        exact ⟨by simpa using h', by simpa using e⟩
    · intro j h
      cases j with
      | zero => exact ⟨by simp, rfl⟩
      | succ j =>
        obtain ⟨h', e⟩ := h2 j (by simpa using h)
        exact ⟨by simpa using h', by simpa using e⟩
    · intro j h
      cases j with
      | zero => rfl
      | succ j => simp only; rw [h3 j (by simpa using h)]
    · intro j h
      cases j with
      | zero => rfl
      | succ j => simp only; rw [h4 j (by simpa using h)]
  | swap x y l =>
    let s : ℕ → ℕ := fun j => match j with | 0 => 1 | 1 => 0 | j + 2 => j + 2
    refine ⟨s, s, ?_, ?_, ?_, ?_⟩
    · intro j h
      match j, h with
      | 0, _ => exact ⟨by simp [s], rfl⟩
      | 1, _ => exact ⟨by simp [s], rfl⟩
      | j + 2, h => exact ⟨h, rfl⟩
    · intro j h
      match j, h with
      | 0, _ => exact ⟨by simp [s], rfl⟩
      | 1, _ => exact ⟨by simp [s], rfl⟩
      | j + 2, h => exact ⟨h, rfl⟩
    · intro j _
      match j with
      | 0 => rfl
      | 1 => rfl
      | j + 2 => rfl
    · intro j _
      match j with
      | 0 => rfl
      | 1 => rfl
      | j + 2 => rfl
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ1, τ1, a1, b1, c1, d1⟩ := ih1
    obtain ⟨σ2, τ2, a2, b2, c2, d2⟩ := ih2
    refine ⟨σ2 ∘ σ1, τ1 ∘ τ2, ?_, ?_, ?_, ?_⟩
    · intro j h
      obtain ⟨h', e⟩ := a1 j h
      obtain ⟨h'', e'⟩ := a2 _ h'
      exact ⟨h'', e'.trans e⟩
    · intro j h
      obtain ⟨h', e⟩ := b2 j h
      obtain ⟨h'', e'⟩ := b1 _ h'
      exact ⟨h'', e'.trans e⟩
    · intro j h
      obtain ⟨h', _⟩ := a1 j h
      simp only [Function.comp]
      rw [c2 _ h', c1 j h]
    · intro j h
      obtain ⟨h', _⟩ := b2 j h
      simp only [Function.comp]
      rw [d1 _ h', d2 j h]

/-! ### The root shift -/

/-- Address map of the root shift `node (node ds :: rest) ↦ node (ds ++ [node rest])`, `n = |ds|`. -/
def shF (n : ℕ) : List ℕ → List ℕ
  | [] => [n]
  | 0 :: q => q
  | (k + 1) :: q => n :: k :: q

/-- Its inverse. -/
def shG (n : ℕ) : List ℕ → List ℕ
  | [] => [0]
  | j :: q => if j < n then 0 :: j :: q else
      match q with
      | [] => []
      | k :: q' => (k + 1) :: q'

theorem shF_child (n : ℕ) (a : List ℕ) (k : ℕ) : ladj (shF n a) (shF n (a ++ [k])) := by
  match a, k with
  | [], 0 => exact Or.inr ⟨n, rfl⟩
  | [], k + 1 => exact Or.inl ⟨k, rfl⟩
  | 0 :: q, k => exact Or.inl ⟨k, rfl⟩
  | (m + 1) :: q, k => exact Or.inl ⟨k, rfl⟩

theorem valid_shift_n {ds rest : List UTree} {q : List ℕ} :
    Valid (UTree.node (ds ++ [UTree.node rest])) (ds.length :: q) ↔ Valid (UTree.node rest) q := by
  rw [valid_cons]
  constructor
  · rintro ⟨h, hq⟩; simpa using hq
  · intro hq; exact ⟨by simp, by simpa using hq⟩

theorem valid_shift_lt {ds rest : List UTree} {j : ℕ} {q : List ℕ} (hj : j < ds.length) :
    Valid (UTree.node (ds ++ [UTree.node rest])) (j :: q) ↔ Valid (UTree.node ds) (j :: q) := by
  rw [valid_cons, valid_cons]
  constructor
  · rintro ⟨h, hq⟩; exact ⟨hj, by rwa [List.getElem_append_left hj] at hq⟩
  · rintro ⟨h, hq⟩; exact ⟨by simp; omega, by rwa [List.getElem_append_left hj]⟩

theorem valid_shift_le {ds rest : List UTree} {j : ℕ} {q : List ℕ}
    (h : Valid (UTree.node (ds ++ [UTree.node rest])) (j :: q)) : j ≤ ds.length := by
  obtain ⟨h, _⟩ := valid_cons.mp h; simp at h; omega

theorem valid_shift_zero {ds rest : List UTree} {q : List ℕ} :
    Valid (UTree.node (UTree.node ds :: rest)) (0 :: q) ↔ Valid (UTree.node ds) q := by
  rw [valid_cons]; simp

theorem valid_shift_succ {ds rest : List UTree} {k : ℕ} {q : List ℕ} :
    Valid (UTree.node (UTree.node ds :: rest)) ((k + 1) :: q) ↔ Valid (UTree.node rest) (k :: q) := by
  rw [valid_cons, valid_cons]; simp

/-- The root shift is a graph isomorphism. -/
def shiftIso (ds rest : List UTree) :
    G (UTree.node (UTree.node ds :: rest)) ≃g G (UTree.node (ds ++ [UTree.node rest])) :=
  isoOfMaps (shF ds.length) (shG ds.length)
    (by
      intro p hp
      match p with
      | [] => exact valid_shift_n.mpr (valid_nil _)
      | 0 :: q =>
        have hq := valid_shift_zero.mp hp
        match q with
        | [] => exact valid_nil _
        | j :: q' =>
          obtain ⟨hj, _⟩ := valid_cons.mp hq
          exact (valid_shift_lt hj).mpr hq
      | (k + 1) :: q => exact valid_shift_n.mpr (valid_shift_succ.mp hp))
    (by
      intro p hp
      match p with
      | [] => exact valid_shift_zero.mpr (valid_nil _)
      | j :: q =>
        simp only [shG]
        split_ifs with hj
        · exact valid_shift_zero.mpr ((valid_shift_lt hj).mp hp)
        · have hjn : j = ds.length := le_antisymm (valid_shift_le hp) (by omega)
          subst hjn
          have hq := valid_shift_n.mp hp
          match q with
          | [] => exact valid_nil _
          | k :: q' => exact valid_shift_succ.mpr hq)
    (by
      intro p hp
      match p with
      | [] => simp [shF, shG]
      | 0 :: q =>
        have hq := valid_shift_zero.mp hp
        match q with
        | [] => rfl
        | j :: q' =>
          obtain ⟨hj, _⟩ := valid_cons.mp hq
          simp [shF, shG, hj]
      | (k + 1) :: q => simp [shF, shG])
    (by
      intro p hp
      match p with
      | [] => rfl
      | j :: q =>
        simp only [shG]
        split_ifs with hj
        · rfl
        · have hjn : j = ds.length := le_antisymm (valid_shift_le hp) (by omega)
          subst hjn
          match q with
          | [] => rfl
          | k :: q' => rfl)
    (fun a k _ => shF_child ds.length a k)
    (by
      intro a k hv
      match a with
      | [] =>
        have hk := valid_shift_le (q := []) hv
        rcases Nat.lt_or_ge k ds.length with hk' | hk'
        · simp only [List.nil_append, shG, hk', if_true]; exact Or.inl ⟨k, rfl⟩
        · have : k = ds.length := by omega
          subst this
          simp only [List.nil_append, shG, lt_irrefl, if_false]; exact Or.inr ⟨0, rfl⟩
      | j :: q =>
        have hj := valid_shift_le hv
        rcases Nat.lt_or_ge j ds.length with hj' | hj'
        · simp only [List.cons_append, shG, hj', if_true]; exact Or.inl ⟨k, rfl⟩
        · have : j = ds.length := by omega
          subst this
          match q with
          | [] => simp only [List.cons_append, List.nil_append, shG, lt_irrefl, if_false]; exact Or.inl ⟨k + 1, rfl⟩
          | m :: q' => simp only [List.cons_append, shG, lt_irrefl, if_false]; exact Or.inl ⟨k, rfl⟩)

theorem shiftIso_apply (ds rest : List UTree) (v : V (UTree.node (UTree.node ds :: rest))) :
    (shiftIso ds rest v).1 = shF ds.length v.1 := rfl

/-! ### Soundness: rerooting is an isomorphism -/

theorem uiso_refl (t : UTree) : UIso t t := ⟨SimpleGraph.Iso.refl⟩

theorem uiso_trans {a b c : UTree} (h1 : UIso a b) (h2 : UIso b c) : UIso a c := by
  obtain ⟨e⟩ := h1; obtain ⟨f⟩ := h2; exact ⟨e.trans f⟩

theorem uiso_of_step {t t' : UTree} (h : RerootStep1 t t') : UIso t t' := by
  rcases h with ⟨ds, rest, rfl, rfl⟩ | ⟨cs, cs', hp, rfl, rfl⟩
  · exact ⟨shiftIso ds rest⟩
  · obtain ⟨σ, τ, H⟩ := idxBij_of_perm hp
    exact ⟨permIso cs cs' σ τ H⟩

/-- **Soundness.**  A rerooting (with reordered children) is an isomorphism of unrooted trees. -/
theorem uiso_of_rerootRel {t t' : UTree} (h : RerootRel t t') : UIso t t' := by
  induction h with
  | refl => exact uiso_refl _
  | tail _ h ih => exact uiso_trans ih (uiso_of_step h)

end RerootIso
end R3Cert
