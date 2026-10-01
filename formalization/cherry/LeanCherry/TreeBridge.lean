/-
LeanCherry.TreeBridge -- from an arbitrary finite Mathlib tree to the cavity recursion.

Generic matching sum over Sym2-edges with a degree function:
  IsGMg M   : distinct edges of M share no vertex;   wS δ l s(u,w) = l / (δ u * δ w);
  MS l δ E  := sum over M ⊆ E with IsGMg M of prod_{e ∈ M} wS δ l e.
The lambda-weighted matching sum of a finite simple graph (true degrees):
  piL l G := MS l (fun v => (G.degree v : ℝ)) G.edgeFinset.
Main results:
  tree_realize : every finite tree G on V has (b : Br, f : V → List ℕ injective) with G.edgeFinset.image (Sym2.map f) = edgeFin b,
                 size b = card V;
  piL_eq_ZTl   : then piL l G = ZTl l b;
  pi_lam_le_tree : 1 + sqrt 5 ≤ l → G.IsTree → piL l G ≤ (1 + l) * (1 + l/2)^((card V - 1)/2).
-/
import LeanCherry.AddLeaf

open Finset LeanCherry.MatchSum

namespace LeanCherry

universe u

noncomputable section

section Generic

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- a matching of Sym2-edges: distinct edges share no vertex -/
def IsGMg (M : Finset (Sym2 α)) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

open Classical in
/-- edge weight l / (δ u * δ w) -/
def wS (δ : α → ℝ) (l : ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u w => l / (δ u * δ w), fun u w => by simp only [mul_comm]⟩

open Classical in
/-- generic weighted matching sum -/
def MS (l : ℝ) (δ : α → ℝ) (E : Finset (Sym2 α)) : ℝ :=
  ∑ M ∈ E.powerset, if IsGMg M then ∏ e ∈ M, wS δ l e else 0

lemma wS_mk (δ : α → ℝ) (l : ℝ) (u w : α) : wS δ l s(u, w) = l / (δ u * δ w) := rfl

/-- relabelling along an injective map -/
theorem MS_image {f : α → β} (hf : Function.Injective f) (l : ℝ) (δ : α → ℝ) (δ' : β → ℝ)
    (hδ : ∀ v, δ' (f v) = δ v) (E : Finset (Sym2 α)) :
    MS l δ' (E.image (Sym2.map f)) = MS l δ E := by
  classical
  have hinj := Sym2.map.injective hf
  unfold MS
  symm
  refine Finset.sum_bij' (fun S _ => S.image (Sym2.map f)) (fun T _ => E.filter (fun e => Sym2.map f e ∈ T))
    ?_ ?_ ?_ ?_ ?_
  · intro S hS; exact mem_powerset.mpr (image_subset_image (mem_powerset.mp hS))
  · intro T _; exact mem_powerset.mpr (filter_subset _ _)
  · intro S hS
    have hSE := mem_powerset.mp hS
    ext e; simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨_, s, hs, hse⟩; rwa [← hinj hse]
    · intro he; exact ⟨hSE he, e, he, rfl⟩
  · intro T hT
    have hTE := mem_powerset.mp hT
    ext x; simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨e, ⟨_, hx⟩, rfl⟩; exact hx
    · intro hx
      obtain ⟨e, he, rfl⟩ := mem_image.mp (hTE hx)
      exact ⟨e, ⟨he, hx⟩, rfl⟩
  · intro S _
    have hiso : IsGMg S ↔ IsGMg (S.image (Sym2.map f)) := by
      constructor
      · intro h x hx y hy hxy w hwx hwy
        obtain ⟨e, he, rfl⟩ := mem_image.mp hx
        obtain ⟨e', he', rfl⟩ := mem_image.mp hy
        obtain ⟨p, hp, rfl⟩ := Sym2.mem_map.mp hwx
        obtain ⟨q, hq, hpq⟩ := Sym2.mem_map.mp hwy
        rw [hf hpq] at hq
        exact h e he e' he' (fun h' => hxy (h' ▸ rfl)) p hp hq
      · intro h e he e' he' hee w hwe hwe'
        exact h _ (mem_image_of_mem _ he) _ (mem_image_of_mem _ he') (fun h' => hee (hinj h'))
          (f w) (Sym2.mem_map.mpr ⟨w, hwe, rfl⟩) (Sym2.mem_map.mpr ⟨w, hwe', rfl⟩)
    have hw : ∀ e : Sym2 α, wS δ' l (Sym2.map f e) = wS δ l e := by
      intro e; induction e using Sym2.ind with
      | h x y => rw [Sym2.map_mk, wS_mk, wS_mk, hδ, hδ]
    have hprod : ∏ e ∈ S, wS δ l e = ∏ x ∈ S.image (Sym2.map f), wS δ' l x := by
      rw [prod_image (fun e _ f' _ h => hinj h)]
      exact prod_congr rfl (fun e _ => (hw e).symm)
    by_cases h : IsGMg S
    · rw [if_pos h, if_pos (hiso.mp h), hprod]
    · rw [if_neg h, if_neg (fun h' => h (hiso.mpr h'))]

end Generic

/-- the lambda-weighted matching sum of a finite simple graph, with true degrees -/
def piL {V : Type u} [Fintype V] [DecidableEq V] (l : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  MS l (fun v => (G.degree v : ℝ)) G.edgeFinset

namespace Br

/-- the generic Sym2 matching sum on edgeFin b is the edge-list matching sum -/
theorem MS_edgeFin (l : ℝ) (δ : List ℕ → ℝ) (b : Br) :
    MS l δ (edgeFin b) = Z (fun e => l / (δ e.1 * δ e.2)) (edges b) := by
  classical
  unfold MS Z edgeFin
  set φ : List ℕ × List ℕ → Sym2 (List ℕ) := fun e => s(e.1, e.2)
  have hinj := sym_injOn b
  symm
  refine Finset.sum_bij' (fun S _ => S.image φ) (fun T _ => (edges b).filter (fun e => φ e ∈ T)) ?_ ?_ ?_ ?_ ?_
  · intro S hS; exact mem_powerset.mpr (image_subset_image (mem_powerset.mp hS))
  · intro T _; exact mem_powerset.mpr (filter_subset _ _)
  · intro S hS
    have hSE := mem_powerset.mp hS
    ext e; simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨he, s, hs, hse⟩; rwa [← hinj (hSE hs) he hse]
    · intro he; exact ⟨hSE he, e, he, rfl⟩
  · intro T hT
    have hTE := mem_powerset.mp hT
    ext x; simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨e, ⟨_, hx⟩, rfl⟩; exact hx
    · intro hx
      obtain ⟨e, he, rfl⟩ := mem_image.mp (hTE hx)
      exact ⟨e, ⟨he, hx⟩, rfl⟩
  · intro S hS
    have hSE := mem_powerset.mp hS
    have hiso : IsM S ↔ IsGMg (S.image φ) := by
      constructor
      · intro h x hx y hy hxy v hvx hvy
        obtain ⟨e, he, rfl⟩ := mem_image.mp hx
        obtain ⟨f, hf, rfl⟩ := mem_image.mp hy
        have hd := h e he f hf (fun h' => hxy (h' ▸ rfl))
        rw [Finset.disjoint_left] at hd
        apply hd (a := v)
        · simp only [φ, Sym2.mem_iff] at hvx; simp only [ev, mem_insert, mem_singleton]; exact hvx
        · simp only [φ, Sym2.mem_iff] at hvy; simp only [ev, mem_insert, mem_singleton]; exact hvy
      · intro h e he f hf hef
        rw [Finset.disjoint_left]
        intro v hve hvf
        have hne : φ e ≠ φ f := fun h' => hef (hinj (hSE he) (hSE hf) h')
        apply h (φ e) (mem_image_of_mem φ he) (φ f) (mem_image_of_mem φ hf) hne v
        · simp only [ev, mem_insert, mem_singleton] at hve; simp only [φ, Sym2.mem_iff]; exact hve
        · simp only [ev, mem_insert, mem_singleton] at hvf; simp only [φ, Sym2.mem_iff]; exact hvf
    have hprod : ∏ e ∈ S, l / (δ e.1 * δ e.2) = ∏ x ∈ S.image φ, wS δ l x := by
      rw [prod_image (fun e he f hf h => hinj (hSE he) (hSE hf) h)]
      rfl
    by_cases h : IsM S
    · rw [if_pos h, if_pos (hiso.mp h), hprod]
    · rw [if_neg h, if_neg (fun h' => h (hiso.mpr h'))]

lemma Z_congr {w w' : List ℕ × List ℕ → ℝ} {E : Finset (List ℕ × List ℕ)} (h : ∀ e ∈ E, w e = w' e) :
    Z w E = Z w' E := by
  unfold Z
  apply sum_congr rfl
  intro M hM
  rw [prod_congr rfl (fun e he => h e (mem_powerset.mp hM he))]

lemma gdeg_valid {b : Br} {v : List ℕ} {c : Br} (h : subt b v = some c) : (gdeg b v : ℝ) = tdeg b v := by
  obtain ⟨ho, hi⟩ := out_in_formula v b
  rw [h] at ho hi
  simp only [Option.isSome_some, if_true] at hi
  rw [gdeg_eq, ho, hi]
  unfold tdeg
  by_cases hv : v = []
  · subst hv; rw [subt_nil, Option.some.injEq] at h; subst h; simp
  · simp only [hv, if_false, pdeg, h]; push_cast; ring

/-- the graph form of the whole-tree matching sum -/
theorem MS_gdeg_eq_ZTl (l : ℝ) (b : Br) : MS l (fun v => (gdeg b v : ℝ)) (edgeFin b) = ZTl l b := by
  rw [MS_edgeFin, ZTl]
  apply Z_congr
  intro e he
  obtain ⟨c1, h1⟩ := valid_fst he
  obtain ⟨c2, h2⟩ := valid_snd he
  simp only [wtT, gdeg_valid h1, gdeg_valid h2]

/-! ### realizing a Mathlib tree as a whole Br-tree -/

lemma edgeFin_addLeaf {a : List ℕ} {b c : Br} (h : subt b a = some c) :
    edgeFin (addLeaf b a) = insert s(a, a ++ [nch c]) (edgeFin b) := by
  unfold edgeFin; rw [edges_addLeaf a b c h, image_insert]

lemma edgeFin_leaf : edgeFin (.node []) = ∅ := by unfold edgeFin; rw [edges_leaf]; rfl

/-- edges of a tree with a leaf v (unique neighbour u) = s(v,u) plus the edges of G - v -/
lemma edgeFinset_leaf {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {v u : V} (hvu : G.Adj v u) (huniq : ∀ y, G.Adj v y → y = u)
    [Fintype {x : V | x ≠ v}] [DecidableRel (G.induce {x | x ≠ v}).Adj] :
    G.edgeFinset = insert s(v, u) ((G.induce {x | x ≠ v}).edgeFinset.image (Sym2.map Subtype.val)) := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_insert, mem_image]
    constructor
    · intro hxy
      by_cases hx : x = v
      · subst hx; left; rw [huniq y hxy]
      · by_cases hy : y = v
        · subst hy; left; rw [huniq x hxy.symm, Sym2.eq_swap]
        · right
          refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
          rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj]; exact hxy
    · rintro (h | ⟨e', he', hee⟩)
      · rw [← SimpleGraph.mem_edgeSet, h, SimpleGraph.mem_edgeSet]; exact hvu
      · induction e' using Sym2.ind with
        | h x' y' =>
          rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he'
          rw [Sym2.map_mk] at hee
          rw [← SimpleGraph.mem_edgeSet, ← hee, SimpleGraph.mem_edgeSet]; exact he'

/-- core: every finite tree is (the edge set of) a whole Br-tree, via an injective relabelling -/
theorem tree_realize : ∀ (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsTree → Fintype.card V = n →
    ∃ (b : Br) (f : V → List ℕ), Function.Injective f ∧ (∀ w, (subt b (f w)).isSome) ∧ size b = n ∧
      G.edgeFinset.image (Sym2.map f) = edgeFin b := by
  intro n
  induction n with
  | zero =>
    intro V _ _ G _ hG hn
    have := hG.connected.nonempty
    have := Fintype.card_pos (α := V); omega
  | succ n IH =>
    intro V _ _ G _ hG hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · -- a single vertex
      have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      refine ⟨.node [], fun _ => [], fun x y _ => Subsingleton.elim x y, fun _ => by rw [subt_nil]; rfl,
        by simp [size, sizeL], ?_⟩
      rw [edgeFin_leaf]
      have : G.edgeFinset = ∅ := by
        ext e; induction e using Sym2.ind with
        | h x y =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.notMem_empty, iff_false]
          intro hxy; exact G.irrefl (Subsingleton.elim x y ▸ hxy)
      rw [this]; rfl
    · -- a leaf
      have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hvu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      set S : Set V := {x | x ≠ v} with hS
      let G' : SimpleGraph S := G.induce S
      haveI : DecidableRel G'.Adj := fun x y => decidable_of_iff (G.Adj x y) (by simp [G'])
      have hset : ({v}ᶜ : Set V) = S := by ext; simp [S]
      have hconn : G'.Connected := by
        have := hG.connected.induce_compl_singleton_of_degree_eq_one hv
        rw [hset] at this; exact this
      have htree : G'.IsTree := ⟨hconn, hG.isAcyclic.induce S⟩
      have hcard : Fintype.card S = n := by
        have := Set.card_ne_eq v (α := V); rw [hn] at this; simp only [S]; omega
      obtain ⟨b', f', hinj', hvalid', hsize', hedge'⟩ := IH G' htree hcard
      have huS : u ∈ S := by simp only [S, Set.mem_setOf_eq]; exact (G.ne_of_adj hvu).symm
      set a := f' ⟨u, huS⟩ with ha
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hvalid' ⟨u, huS⟩)
      rw [← ha] at hc
      set k := nch c
      let f : V → List ℕ := fun w => if h : w = v then a ++ [k] else f' ⟨w, h⟩
      have hfv : f v = a ++ [k] := by simp [f]
      have hfo : ∀ (w : V) (h : w ≠ v), f w = f' ⟨w, h⟩ := fun w h => by simp [f, h]
      have hfu : f u = a := by rw [hfo u huS]
      have hnew : ∀ w : S, f' w ≠ a ++ [k] := by
        intro w h
        have h1 := hvalid' w
        rw [h, subt_new_none a b' c hc] at h1
        exact Bool.false_ne_true h1
      refine ⟨addLeaf b' a, f, ?_, ?_, ?_, ?_⟩
      · intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · rw [hx, hy]
        · rw [hx, hfv, hfo y hy] at hxy; exact absurd hxy.symm (hnew ⟨y, hy⟩)
        · rw [hy, hfv, hfo x hx] at hxy; exact absurd hxy (hnew ⟨x, hx⟩)
        · rw [hfo x hx, hfo y hy] at hxy; exact congrArg Subtype.val (hinj' hxy)
      · intro w
        by_cases hw : w = v
        · rw [hw, hfv, subt_addLeaf_new a b' c hc]; rfl
        · rw [hfo w hw]; exact subt_addLeaf_old _ a b' (hvalid' ⟨w, hw⟩)
      · rw [size_addLeaf a b' c hc, hsize']
      · rw [edgeFinset_leaf G hvu (fun y hy => huniq y hy), image_insert, image_image, edgeFin_addLeaf hc,
          ← hedge', Sym2.map_mk, hfv, hfu, Sym2.eq_swap]
        congr 1
        apply image_congr
        intro e _
        simp only [Function.comp]
        rw [Sym2.map_map]
        congr 1
        funext w
        exact hfo w.1 w.2

/-- degrees are preserved by the realization -/
lemma gdeg_realize {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {b : Br} {f : V → List ℕ} (hf : Function.Injective f) (he : G.edgeFinset.image (Sym2.map f) = edgeFin b)
    (w : V) : (gdeg b (f w) : ℝ) = G.degree w := by
  have hadj : ∀ x y : List ℕ, (Br.G b).Adj x y ↔ s(x, y) ∈ G.edgeFinset.image (Sym2.map f) := by
    intro x y
    rw [he, ← SimpleGraph.mem_edgeSet, ← edgeFin_eq, mem_coe]
  have hnb : (Br.G b).neighborSet (f w) = f '' G.neighborSet w := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, hadj, mem_image, Set.mem_image]
    constructor
    · rintro ⟨e, he', hee⟩
      induction e using Sym2.ind with
      | h p q =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
        rw [Sym2.map_mk] at hee
        rcases Sym2.eq_iff.mp hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hf h1] at he'; exact ⟨q, he', h2⟩
        · rw [hf h2] at he'; exact ⟨p, he'.symm, h1⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨s(w, q), by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hq, rfl⟩
  unfold gdeg
  rw [hnb, Set.ncard_image_of_injective _ hf, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]

/-- the matching sum of a finite tree equals the whole-tree cavity quantity of its realization -/
theorem piL_eq_ZTl {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {b : Br} {f : V → List ℕ} (hf : Function.Injective f) (he : G.edgeFinset.image (Sym2.map f) = edgeFin b)
    (l : ℝ) : piL l G = ZTl l b := by
  unfold piL
  rw [← MS_gdeg_eq_ZTl, ← he, MS_image hf l _ _ (fun w => gdeg_realize G hf he w)]

end Br

/-- the one-block upper bound on Mathlib trees: for every finite tree G on V and every l ≥ 1 + sqrt 5,
    piL l G ≤ (1 + l) (1 + l/2)^((|V| - 1)/2), where piL is the lambda-weighted matching sum with true degrees. -/
theorem pi_lam_le_tree {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : ℝ} (hl : 1 + √5 ≤ l) (hG : G.IsTree) :
    piL l G ≤ (1 + l) * (1 + l / 2) ^ (((Fintype.card V : ℝ) - 1) / 2) := by
  obtain ⟨b, f, hf, _, hsize, he⟩ := Br.tree_realize (Fintype.card V) G hG rfl
  rw [Br.piL_eq_ZTl G hf he l, ← hsize]
  exact Br.oneblock hl b

end

end LeanCherry
