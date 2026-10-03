import Mathlib
import BGUnique.RerootIsoGraph

/-!
Completeness: an isomorphism of unrooted trees is a rerooting with reordered children.

* `reroot_at`: every vertex can be made the root by `RerootRel` moves, through an isomorphism that
  sends it to the root.
* `rerootRel_of_rooted`: a root-preserving isomorphism matches the children up to a bijection, each
  pair again by a root-preserving isomorphism; by induction on size, this is a sequence of moves.
-/

namespace R3Cert
namespace RerootIso

open R3Cert.Step3

/-! ### Moving a child to the front -/

/-- Index map of `cs ↦ cs[i] :: cs.eraseIdx i`. -/
def mvS (i : ℕ) (j : ℕ) : ℕ := if j = i then 0 else if j < i then j + 1 else j

/-- Its inverse. -/
def mvT (i : ℕ) : ℕ → ℕ
  | 0 => i
  | m + 1 => if m < i then m else m + 1

theorem idxBij_move {cs : List UTree} {i : ℕ} (hi : i < cs.length) {x : UTree} (hx : cs[i] = x) :
    IdxBij cs (x :: cs.eraseIdx i) (mvS i) (mvT i) := by
  have hlen : (x :: cs.eraseIdx i).length = cs.length := by
    simp [List.length_eraseIdx, hi]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    unfold mvS
    by_cases h1 : j = i
    · subst h1; simp [hx]
    · by_cases h2 : j < i
      · simp only [h1, h2, if_false, if_true]
        refine ⟨by rw [hlen]; omega, ?_⟩
        simp [List.getElem_eraseIdx, h2]
      · simp only [h1, h2, if_false]
        obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        refine ⟨by rw [hlen]; omega, ?_⟩
        simp [List.getElem_eraseIdx, show ¬ m < i by omega]
  · intro j hj
    cases j with
    | zero => exact ⟨hi, by simp [mvT, hx]⟩
    | succ m =>
      by_cases h2 : m < i
      · simp only [mvT, h2, if_true]
        refine ⟨by omega, ?_⟩
        simp [List.getElem_eraseIdx, h2]
      · simp only [mvT, h2, if_false]
        refine ⟨by rw [hlen] at hj; omega, ?_⟩
        simp [List.getElem_eraseIdx, h2]
  · intro j hj
    unfold mvS
    by_cases h1 : j = i
    · subst h1; simp [mvT]
    · by_cases h2 : j < i
      · simp [h1, h2, mvT]
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        simp only [h1, h2, if_false, mvT, show ¬ m < i by omega]
  · intro j hj
    cases j with
    | zero => simp [mvT, mvS]
    | succ m =>
      by_cases h2 : m < i
      · simp only [mvT, h2, if_true, mvS]; simp [show m ≠ i by omega]
      · simp only [mvT, h2, if_false, mvS]; simp [show m + 1 ≠ i by omega, show ¬ m + 1 < i by omega]

theorem perm_move {cs : List UTree} {i : ℕ} (hi : i < cs.length) {x : UTree} (hx : cs[i] = x) :
    cs.Perm (x :: cs.eraseIdx i) := by
  rw [← hx]; exact (List.getElem_cons_eraseIdx_perm hi).symm

/-! ### Rerooting at any vertex -/

/-- Every vertex `p` of `t` becomes the root of some rerooting `t'` of `t`, through an isomorphism. -/
theorem reroot_at : ∀ (p : List ℕ) (t : UTree) (hp : Valid t p),
    ∃ t' : UTree, RerootRel t t' ∧ ∃ φ : G t ≃g G t', (φ ⟨p, hp⟩).1 = [] := by
  intro p
  induction p with
  | nil => intro t hp; exact ⟨t, Relation.ReflTransGen.refl, SimpleGraph.Iso.refl, rfl⟩
  | cons i q ih =>
    intro t hp
    obtain ⟨cs⟩ := t
    obtain ⟨hi, hq⟩ := valid_cons.mp hp
    obtain ⟨ds, hds⟩ : ∃ ds, cs[i] = UTree.node ds := ⟨kids cs[i], by cases cs[i]; rfl⟩
    have H := idxBij_move hi hds
    let φ1 := permIso cs _ _ _ H
    let φ2 := shiftIso ds (cs.eraseIdx i)
    have e1 : (φ2 (φ1 ⟨i :: q, hp⟩)).1 = q := by
      show shF ds.length (permF (mvS i) (i :: q)) = q
      simp [permF, mvS, shF]
    have hq2 : Valid (UTree.node (ds ++ [UTree.node (cs.eraseIdx i)])) q := e1 ▸ (φ2 (φ1 ⟨i :: q, hp⟩)).2
    obtain ⟨t3, h3, φ3, e3⟩ := ih _ hq2
    refine ⟨t3, ?_, φ1.trans (φ2.trans φ3), ?_⟩
    · exact ((RerootEquiv.perm (perm_move hi hds)).trans (RerootEquiv.shift ds _)).trans h3
    · have : φ2 (φ1 ⟨i :: q, hp⟩) = ⟨q, hq2⟩ := Subtype.ext e1
      show (φ3 (φ2 (φ1 ⟨i :: q, hp⟩))).1 = []
      rw [this]; exact e3

/-! ### Root-preserving isomorphisms -/

section Rooted

variable {cs cs' : List UTree} (φ : G (UTree.node cs) ≃g G (UTree.node cs'))
  (hr : (φ (root _)).1 = [])

include hr

theorem rooted_eq : φ (root _) = root _ := Subtype.ext hr

theorem rooted_symm : (φ.symm (root _)).1 = [] := by
  have := congrArg φ.symm (rooted_eq φ hr)
  rw [φ.symm_apply_apply] at this
  rw [← this]; rfl

theorem rooted_ne {v : V (UTree.node cs)} (hv : v.1 ≠ []) : (φ v).1 ≠ [] := by
  intro h
  have : φ v = φ (root _) := Subtype.ext (by rw [h, hr])
  exact hv (by rw [φ.injective this]; rfl)

theorem rooted_one (i : ℕ) (h : Valid (UTree.node cs) [i]) : ∃ j, (φ ⟨[i], h⟩).1 = [j] := by
  have hadj : (G (UTree.node cs)).Adj (root _) ⟨[i], h⟩ := Or.inl ⟨i, rfl⟩
  have := (φ.map_adj_iff).mpr hadj
  change ladj (φ (root _)).1 (φ ⟨[i], h⟩).1 at this
  rw [hr] at this
  exact ladj_nil_left.mp this

/-- A root-preserving isomorphism keeps each child's subtree together. -/
theorem rooted_head (i j : ℕ) (h1 : Valid (UTree.node cs) [i]) (hj : (φ ⟨[i], h1⟩).1 = [j]) :
    ∀ (q : List ℕ) (hv : Valid (UTree.node cs) (i :: q)), ∃ q', (φ ⟨i :: q, hv⟩).1 = j :: q' := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro hv; exact ⟨[], hj⟩
  | append_singleton q k ih =>
    intro hv
    have hv0 : Valid (UTree.node cs) (i :: q) := valid_of_append (q := [k]) hv
    obtain ⟨q', e⟩ := ih hv0
    have hadj : (G (UTree.node cs)).Adj ⟨i :: q, hv0⟩ ⟨i :: (q ++ [k]), hv⟩ := ladj_child (i :: q) k
    have := (φ.map_adj_iff).mpr hadj
    change ladj (φ ⟨i :: q, hv0⟩).1 (φ ⟨i :: (q ++ [k]), hv⟩).1 at this
    have hne := rooted_ne φ hr (v := ⟨i :: (q ++ [k]), hv⟩) (by simp)
    revert this hne
    generalize (φ ⟨i :: (q ++ [k]), hv⟩).1 = b
    intro this hne
    rw [e] at this
    cases b with
    | nil => exact absurd rfl hne
    | cons j2 b' =>
      obtain ⟨rfl, _⟩ := ladj_cons_cons.mp this
      exact ⟨b', rfl⟩

end Rooted

/-- The child map of a root-preserving isomorphism, on addresses. -/
def childF {cs cs' : List UTree} (φ : G (UTree.node cs) ≃g G (UTree.node cs')) (i : ℕ) (q : List ℕ) :
    List ℕ :=
  if h : Valid (UTree.node cs) (i :: q) then (φ ⟨i :: q, h⟩).1.tail else []

theorem childF_eq {cs cs' : List UTree} (φ : G (UTree.node cs) ≃g G (UTree.node cs')) {i j : ℕ} {q q' : List ℕ}
    (hv : Valid (UTree.node cs) (i :: q)) (e : (φ ⟨i :: q, hv⟩).1 = j :: q') : childF φ i q = q' := by
  unfold childF; rw [dif_pos hv, e]; rfl

/-- A root-preserving isomorphism restricts to a root-preserving isomorphism of matched children. -/
theorem child_iso {cs cs' : List UTree} (φ : G (UTree.node cs) ≃g G (UTree.node cs'))
    (hr : (φ (root _)).1 = []) {i j : ℕ} (hi : i < cs.length) (hj' : j < cs'.length)
    (hj : (φ ⟨[i], valid_cons.mpr ⟨hi, valid_nil _⟩⟩).1 = [j]) :
    ∃ ψ : G cs[i] ≃g G cs'[j], (ψ (root _)).1 = [] := by
  have hr' := rooted_symm φ hr
  have h1 : Valid (UTree.node cs) [i] := valid_cons.mpr ⟨hi, valid_nil _⟩
  have h1' : Valid (UTree.node cs') [j] := valid_cons.mpr ⟨hj', valid_nil _⟩
  have hsj : (φ.symm ⟨[j], h1'⟩).1 = [i] := by
    have : φ ⟨[i], h1⟩ = ⟨[j], h1'⟩ := Subtype.ext hj
    rw [← this, φ.symm_apply_apply]
  -- forward data
  have fw : ∀ q (hq : Valid cs[i] q), ∃ (hv : Valid (UTree.node cs) (i :: q)) (q' : List ℕ),
      (φ ⟨i :: q, hv⟩).1 = j :: q' := by
    intro q hq
    have hv : Valid (UTree.node cs) (i :: q) := valid_cons.mpr ⟨hi, hq⟩
    exact ⟨hv, rooted_head φ hr i j h1 hj q hv⟩
  have bw : ∀ q (hq : Valid cs'[j] q), ∃ (hv : Valid (UTree.node cs') (j :: q)) (q' : List ℕ),
      (φ.symm ⟨j :: q, hv⟩).1 = i :: q' := by
    intro q hq
    have hv : Valid (UTree.node cs') (j :: q) := valid_cons.mpr ⟨hj', hq⟩
    exact ⟨hv, rooted_head φ.symm hr' j i h1' hsj q hv⟩
  refine ⟨isoOfMaps (childF φ i) (childF φ.symm j) ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro q hq
    obtain ⟨hv, q', e⟩ := fw q hq
    rw [childF_eq φ hv e]
    have h2 := (φ ⟨i :: q, hv⟩).2
    rw [e] at h2
    obtain ⟨_, h3⟩ := valid_cons.mp h2
    exact h3
  · intro q hq
    obtain ⟨hv, q', e⟩ := bw q hq
    rw [childF_eq φ.symm hv e]
    have h2 := (φ.symm ⟨j :: q, hv⟩).2
    rw [e] at h2
    obtain ⟨_, h3⟩ := valid_cons.mp h2
    exact h3
  · intro q hq
    obtain ⟨hv, q', e⟩ := fw q hq
    rw [childF_eq φ hv e]
    have h2 := (φ ⟨i :: q, hv⟩).2
    rw [e] at h2
    have e2 : φ.symm ⟨j :: q', h2⟩ = ⟨i :: q, hv⟩ := by
      have : φ ⟨i :: q, hv⟩ = ⟨j :: q', h2⟩ := Subtype.ext e
      rw [← this, φ.symm_apply_apply]
    exact childF_eq φ.symm h2 (by rw [e2])
  · intro q hq
    obtain ⟨hv, q', e⟩ := bw q hq
    rw [childF_eq φ.symm hv e]
    have h2 := (φ.symm ⟨j :: q, hv⟩).2
    rw [e] at h2
    have e2 : φ ⟨i :: q', h2⟩ = ⟨j :: q, hv⟩ := by
      have : φ.symm ⟨j :: q, hv⟩ = ⟨i :: q', h2⟩ := Subtype.ext e
      rw [← this, φ.apply_symm_apply]
    exact childF_eq φ h2 (by rw [e2])
  · intro a k hak
    have ha := valid_of_append (q := [k]) hak
    obtain ⟨hva, a', ea⟩ := fw a ha
    obtain ⟨hvb, b', eb⟩ := fw (a ++ [k]) hak
    rw [childF_eq φ hva ea, childF_eq φ hvb eb]
    have hadj : (G (UTree.node cs)).Adj ⟨i :: a, hva⟩ ⟨i :: (a ++ [k]), hvb⟩ := ladj_child (i :: a) k
    have := (φ.map_adj_iff).mpr hadj
    change ladj (φ ⟨i :: a, hva⟩).1 (φ ⟨i :: (a ++ [k]), hvb⟩).1 at this
    rw [ea, eb] at this
    exact (ladj_cons_cons.mp this).2
  · intro a k hak
    have ha := valid_of_append (q := [k]) hak
    obtain ⟨hva, a', ea⟩ := bw a ha
    obtain ⟨hvb, b', eb⟩ := bw (a ++ [k]) hak
    rw [childF_eq φ.symm hva ea, childF_eq φ.symm hvb eb]
    have hadj : (G (UTree.node cs')).Adj ⟨j :: a, hva⟩ ⟨j :: (a ++ [k]), hvb⟩ := ladj_child (j :: a) k
    have := (φ.symm.map_adj_iff).mpr hadj
    change ladj (φ.symm ⟨j :: a, hva⟩).1 (φ.symm ⟨j :: (a ++ [k]), hvb⟩).1 at this
    rw [ea, eb] at this
    exact (ladj_cons_cons.mp this).2
  · show childF φ i [] = []
    exact childF_eq φ h1 hj

/-! ### From matched children to moves -/

/-- Replacing one child by a related one, at the root. -/
def Qrel (c c' : UTree) : Prop := ∀ rest : List UTree, RerootRel (UTree.node (c :: rest)) (UTree.node (c' :: rest))

theorem replace_all {cs L : List UTree} (h : List.Forall₂ Qrel cs L) :
    ∀ pre : List UTree, RerootRel (UTree.node (pre ++ cs)) (UTree.node (pre ++ L)) := by
  induction h with
  | nil => intro pre; exact Relation.ReflTransGen.refl
  | @cons c l cs L hq _ ih =>
    intro pre
    have p1 : (pre ++ c :: cs).Perm (c :: (pre ++ cs)) := List.perm_middle
    have p2 : (l :: (pre ++ cs)).Perm (pre ++ l :: cs) := List.perm_middle.symm
    have s1 := ((RerootEquiv.perm p1).trans (hq (pre ++ cs))).trans (RerootEquiv.perm p2)
    have s2 := ih (pre ++ [l])
    simp only [List.append_assoc, List.singleton_append] at s2
    exact s1.trans s2

theorem ofFn_equiv_perm {α : Type*} {m m' : ℕ} (e : Fin m ≃ Fin m') (F : Fin m' → α) :
    (List.ofFn (F ∘ e)).Perm (List.ofFn F) := by
  obtain rfl : m = m' := Fin.equiv_iff_eq.mp ⟨e⟩
  exact Equiv.Perm.ofFn_comp_perm e F

theorem usize_child_lt {cs : List UTree} {i : ℕ} (hi : i < cs.length) :
    usize cs[i] < usize (UTree.node cs) := by
  rw [usize_node, ← usizeList_perm (List.getElem_cons_eraseIdx_perm hi), usizeList_cons]
  omega

/-- **A root-preserving isomorphism is a sequence of moves.**  Also gives the child-replacement form. -/
theorem rerootRel_of_rooted : ∀ (n : ℕ) (t t' : UTree), usize t = n → ∀ φ : G t ≃g G t',
    (φ (root t)).1 = [] → RerootRel t t' ∧ Qrel t t' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t t' hn φ hr
  obtain ⟨cs⟩ := t
  obtain ⟨cs'⟩ := t'
  have h1 : ∀ i (h : i < cs.length), Valid (UTree.node cs) [i] := fun i h => valid_cons.mpr ⟨h, valid_nil _⟩
  have h1' : ∀ j (h : j < cs'.length), Valid (UTree.node cs') [j] := fun j h => valid_cons.mpr ⟨h, valid_nil _⟩
  have hr' := rooted_symm φ hr
  -- the index bijection
  let σ : ℕ → ℕ := fun i => if h : i < cs.length then (φ ⟨[i], h1 i h⟩).1.headD 0 else 0
  let τ : ℕ → ℕ := fun j => if h : j < cs'.length then (φ.symm ⟨[j], h1' j h⟩).1.headD 0 else 0
  have hσ : ∀ i (h : i < cs.length), (φ ⟨[i], h1 i h⟩).1 = [σ i] ∧ σ i < cs'.length := by
    intro i h
    obtain ⟨j, e⟩ := rooted_one φ hr i (h1 i h)
    have hs : σ i = j := by simp only [σ, dif_pos h, e]; rfl
    have hv := (φ ⟨[i], h1 i h⟩).2
    rw [e] at hv
    obtain ⟨hj, _⟩ := valid_cons.mp hv
    exact ⟨by rw [e, hs], by rw [hs]; exact hj⟩
  have hτ : ∀ j (h : j < cs'.length), (φ.symm ⟨[j], h1' j h⟩).1 = [τ j] ∧ τ j < cs.length := by
    intro j h
    obtain ⟨i, e⟩ := rooted_one φ.symm hr' j (h1' j h)
    have hs : τ j = i := by simp only [τ, dif_pos h, e]; rfl
    have hv := (φ.symm ⟨[j], h1' j h⟩).2
    rw [e] at hv
    obtain ⟨hi, _⟩ := valid_cons.mp hv
    exact ⟨by rw [e, hs], by rw [hs]; exact hi⟩
  have hτσ : ∀ i (h : i < cs.length), τ (σ i) = i := by
    intro i h
    obtain ⟨e, hb⟩ := hσ i h
    have : φ ⟨[i], h1 i h⟩ = ⟨[σ i], h1' _ hb⟩ := Subtype.ext e
    have e2 : (φ.symm ⟨[σ i], h1' _ hb⟩).1 = [i] := by rw [← this, φ.symm_apply_apply]
    have := (hτ (σ i) hb).1
    rw [e2] at this
    exact (List.singleton_inj.mp this).symm
  have hστ : ∀ j (h : j < cs'.length), σ (τ j) = j := by
    intro j h
    obtain ⟨e, hb⟩ := hτ j h
    have : φ.symm ⟨[j], h1' j h⟩ = ⟨[τ j], h1 _ hb⟩ := Subtype.ext e
    have e2 : (φ ⟨[τ j], h1 _ hb⟩).1 = [j] := by rw [← this, φ.apply_symm_apply]
    have := (hσ (τ j) hb).1
    rw [e2] at this
    exact (List.singleton_inj.mp this).symm
  -- children are related
  have hQ : ∀ i (h : i < cs.length), Qrel cs[i] (cs'[σ i]'(hσ i h).2) := by
    intro i h
    obtain ⟨ψ, hψ⟩ := child_iso φ hr h (hσ i h).2 (hσ i h).1
    have hlt : usize cs[i] < n := hn ▸ usize_child_lt h
    exact (ih _ hlt cs[i] _ rfl ψ hψ).2
  -- the matched list
  let e : Fin cs.length ≃ Fin cs'.length :=
    { toFun := fun i => ⟨σ i, (hσ i i.2).2⟩
      invFun := fun j => ⟨τ j, (hτ j j.2).2⟩
      left_inv := fun i => Fin.ext (hτσ i i.2)
      right_inv := fun j => Fin.ext (hστ j j.2) }
  let L : List UTree := List.ofFn (cs'.get ∘ e)
  have hL : L.Perm cs' := by
    have := ofFn_equiv_perm e cs'.get
    rwa [List.ofFn_get] at this
  have hF : List.Forall₂ Qrel cs L := by
    apply List.forall₂_of_length_eq_of_get (by simp [L])
    intro i h h'
    have : (List.ofFn (cs'.get ∘ e))[i] = cs'[σ i]'(hσ i h).2 := by
      simp [List.getElem_ofFn, e]
    simp only [L, List.get_eq_getElem, this]
    exact hQ i h
  refine ⟨?_, ?_⟩
  · have := replace_all hF []
    simp only [List.nil_append] at this
    exact this.trans (RerootEquiv.perm hL)
  · intro rest
    have hF2 : List.Forall₂ Qrel (cs ++ [UTree.node rest]) (L ++ [UTree.node rest]) :=
      List.rel_append hF (List.Forall₂.cons (fun _ => Relation.ReflTransGen.refl) List.Forall₂.nil)
    have s1 := RerootEquiv.shift cs rest
    have s2 := replace_all hF2 []
    simp only [List.nil_append] at s2
    have p3 : (L ++ [UTree.node rest]).Perm (UTree.node rest :: cs') :=
      (List.perm_append_singleton _ _).trans (List.Perm.cons _ hL)
    have s4 := RerootEquiv.shift rest cs'
    have p5 : (rest ++ [UTree.node cs']).Perm (UTree.node cs' :: rest) := List.perm_append_singleton _ _
    exact (((s1.trans s2).trans (RerootEquiv.perm p3)).trans s4).trans (RerootEquiv.perm p5)

/-- **Completeness.**  Isomorphic unrooted trees are related by rerooting and reordering children. -/
theorem rerootRel_of_uiso {t t' : UTree} (h : UIso t t') : RerootRel t t' := by
  obtain ⟨φ⟩ := h
  obtain ⟨t'', h1, ψ, e⟩ := reroot_at (φ (root t)).1 t' (φ (root t)).2
  have h2 := (rerootRel_of_rooted _ t t'' rfl (φ.trans ψ) e).1
  exact h2.trans (RerootEquiv.symm h1)

/-- **`RerootRel` is exactly isomorphism of unrooted trees.** -/
theorem rerootRel_iff_uiso (t t' : UTree) : RerootRel t t' ↔ UIso t t' :=
  ⟨uiso_of_rerootRel, rerootRel_of_uiso⟩

end RerootIso
end R3Cert
