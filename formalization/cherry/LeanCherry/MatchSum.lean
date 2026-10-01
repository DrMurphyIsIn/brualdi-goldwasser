/-
LeanCherry.MatchSum -- weighted matching sums of finite edge sets (generic vertex type).

  An edge is an ordered pair e = (u, v); its vertex set is ev e = {u, v}.  A matching is a finite set of edges whose vertex
  sets are pairwise disjoint.  Z w E := sum over matchings M of E of prod_{e in M} w e.
Lemmas: Z of the empty set; edge deletion-contraction (Z_insert); product over vertex-disjoint unions (Z_union);
relabelling by an injective vertex map (Z_map).
-/
import Mathlib

open Finset

namespace LeanCherry

namespace MatchSum

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- vertex set of an edge -/
def ev (e : α × α) : Finset α := {e.1, e.2}

/-- a matching: pairwise vertex-disjoint edges -/
def IsM (M : Finset (α × α)) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (ev e) (ev f)

instance : DecidablePred (IsM (α := α)) := fun M => by unfold IsM; infer_instance

/-- the weighted matching sum -/
def Z (w : α × α → ℝ) (E : Finset (α × α)) : ℝ :=
  ∑ M ∈ E.powerset, if IsM M then ∏ e ∈ M, w e else 0

lemma ev_nonempty (e : α × α) : (ev e).Nonempty := ⟨e.1, by simp [ev]⟩

lemma isM_empty : IsM (∅ : Finset (α × α)) := by intro e he; simp at he

lemma Z_empty (w : α × α → ℝ) : Z w ∅ = 1 := by
  simp [Z, isM_empty]

lemma isM_insert {e : α × α} {M : Finset (α × α)} (he : e ∉ M) :
    IsM (insert e M) ↔ IsM M ∧ ∀ f ∈ M, Disjoint (ev e) (ev f) := by
  constructor
  · intro h
    refine ⟨fun a ha b hb hab => h a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab, fun f hf => ?_⟩
    exact h e (mem_insert_self e M) f (mem_insert_of_mem hf) (fun h' => he (h' ▸ hf))
  · rintro ⟨h1, h2⟩ a ha b hb hab
    rcases mem_insert.mp ha with rfl | ha'
    · rcases mem_insert.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact h2 b hb'
    · rcases mem_insert.mp hb with rfl | hb'
      · exact (h2 a ha').symm
      · exact h1 a ha' b hb' hab

lemma sum_powerset_forall (E : Finset (α × α)) (P : α × α → Prop) [DecidablePred P] (g : Finset (α × α) → ℝ) :
    (∑ t ∈ E.powerset, if (∀ f ∈ t, P f) then g t else 0) = ∑ t ∈ (E.filter P).powerset, g t := by
  rw [← sum_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_powerset, subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx; exact ⟨h1 hx, h2 x hx⟩
  · intro h; exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

/-- deletion-contraction at an edge -/
lemma Z_insert (w : α × α → ℝ) {e : α × α} {E : Finset (α × α)} (he : e ∉ E) :
    Z w (insert e E) = Z w E + w e * Z w (E.filter (fun f => Disjoint (ev e) (ev f))) := by
  unfold Z
  rw [sum_powerset_insert he]
  congr 1
  rw [mul_sum, ← sum_powerset_forall E (fun f => Disjoint (ev e) (ev f))]
  apply sum_congr rfl
  intro t ht
  have het : e ∉ t := fun h => he (mem_powerset.mp ht h)
  rw [prod_insert het]
  have key : IsM (insert e t) ↔ IsM t ∧ ∀ f ∈ t, Disjoint (ev e) (ev f) := isM_insert het
  by_cases h1 : IsM t <;> by_cases h2 : ∀ f ∈ t, Disjoint (ev e) (ev f)
  · rw [if_pos (key.mpr ⟨h1, h2⟩), if_pos h2, if_pos h1]
  · rw [if_neg (fun h => h2 (key.mp h).2), if_neg h2]
  · rw [if_neg (fun h => h1 (key.mp h).1), if_pos h2, if_neg h1, mul_zero]
  · rw [if_neg (fun h => h1 (key.mp h).1), if_neg h2]

/-- product over vertex-disjoint unions -/
theorem Z_union (w : α × α → ℝ) : ∀ (A B : Finset (α × α)),
    (∀ e ∈ A, ∀ f ∈ B, Disjoint (ev e) (ev f)) → Z w (A ∪ B) = Z w A * Z w B := by
  intro A
  induction A using Finset.strongInduction with
  | H A IH =>
    intro B hAB
    rcases A.eq_empty_or_nonempty with rfl | ⟨e, he⟩
    · simp [Z_empty]
    · set A' := A.erase e with hA'
      have hA : A = insert e A' := (insert_erase he).symm
      have heA' : e ∉ A' := notMem_erase e A
      have heB : e ∉ B := fun h => by
        have := hAB e he e h
        exact (ev_nonempty e).ne_empty (disjoint_self.mp this)
      have hsub : A' ⊂ A := erase_ssubset he
      have hsub2 : A'.filter (fun f => Disjoint (ev e) (ev f)) ⊂ A :=
        lt_of_le_of_lt (filter_subset _ _) hsub
      have hB' : B.filter (fun f => Disjoint (ev e) (ev f)) = B := by
        apply filter_true_of_mem; intro f hf; exact hAB e he f hf
      have hA'B : ∀ x ∈ A', ∀ f ∈ B, Disjoint (ev x) (ev f) := fun x hx f hf => hAB x (mem_of_mem_erase hx) f hf
      have hA'fB : ∀ x ∈ A'.filter (fun f => Disjoint (ev e) (ev f)), ∀ f ∈ B, Disjoint (ev x) (ev f) :=
        fun x hx f hf => hA'B x (mem_filter.mp hx).1 f hf
      have h1 : Z w (insert e (A' ∪ B)) = Z w (A' ∪ B) + w e * Z w ((A' ∪ B).filter (fun f => Disjoint (ev e) (ev f))) :=
        Z_insert w (by simp [heA', heB])
      rw [filter_union, hB'] at h1
      rw [hA, insert_union, h1, IH A' hsub B hA'B, IH _ hsub2 B hA'fB, Z_insert w heA']
      ring

/-- relabelling by an injective vertex map -/
theorem Z_map (f : α ↪ β) (w : α × α → ℝ) (w' : β × β → ℝ) : ∀ (E : Finset (α × α)),
    (∀ e ∈ E, w' (f e.1, f e.2) = w e) → Z w' (E.map (f.prodMap f)) = Z w E := by
  have hev : ∀ e : α × α, ev ((f.prodMap f) e) = (ev e).map f := by
    intro e; ext x; simp [ev, Function.Embedding.prodMap]
  have hdisj : ∀ a b : α × α, Disjoint (ev ((f.prodMap f) a)) (ev ((f.prodMap f) b)) ↔ Disjoint (ev a) (ev b) := by
    intro a b; rw [hev, hev, disjoint_map]
  intro E
  induction E using Finset.strongInduction with
  | H E IH =>
    intro hw
    rcases E.eq_empty_or_nonempty with rfl | ⟨e, he⟩
    · simp [Z_empty]
    · set E' := E.erase e
      have hE : E = insert e E' := (insert_erase he).symm
      have heE' : e ∉ E' := notMem_erase e E
      have hg : (f.prodMap f) e ∉ E'.map (f.prodMap f) := by
        rw [mem_map']; exact heE'
      have hfil : (E'.map (f.prodMap f)).filter (fun x => Disjoint (ev ((f.prodMap f) e)) (ev x))
          = (E'.filter (fun x => Disjoint (ev e) (ev x))).map (f.prodMap f) := by
        rw [filter_map]; congr 1; apply filter_congr; intro x _; simp only [Function.comp]; exact hdisj e x
      have hw' : ∀ x ∈ E', w' (f x.1, f x.2) = w x := fun x hx => hw x (mem_of_mem_erase hx)
      have hwf : ∀ x ∈ E'.filter (fun x => Disjoint (ev e) (ev x)), w' (f x.1, f x.2) = w x :=
        fun x hx => hw' x (mem_filter.mp hx).1
      rw [hE, map_insert, Z_insert w' hg, Z_insert w heE', hfil, IH E' (erase_ssubset he) hw',
        IH _ (lt_of_le_of_lt (filter_subset _ _) (erase_ssubset he)) hwf]
      congr 1
      have := hw e he
      simp only [Function.Embedding.prodMap, Function.Embedding.coeFn_mk, Prod.map] at this ⊢
      rw [this]

end MatchSum

end LeanCherry
