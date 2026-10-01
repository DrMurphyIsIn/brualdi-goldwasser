/-
LeanCherry.GraphMatch -- the cavity recursion for planted branches, stated on a Mathlib SimpleGraph.

  G b : SimpleGraph (List ℕ)   the planted branch as a simple graph on its addresses (u ~ w iff parent-child)
  gdeg b v                     graph degree = ncard of the neighbour set
  pdegG b v                    PLANTED degree = gdeg b v + (1 at the root [], for the phantom parent edge)
  edgeFin b                    the (finite) edge set of G b, as a Finset (Sym2 _);  edgeFin_eq : ↑(edgeFin b) = (G b).edgeSet
  IsGM M                       M is a matching: distinct edges of M share no vertex
  ZG l b := sum over matchings M ⊆ edgeFin b of prod_{s(u,w) ∈ M} l / (pdegG b u * pdegG b w)
Main theorem: Tl_eq_graph_matching_sum : 0 ≤ l → Tl l b = ZG l b.
-/
import LeanCherry.Graph

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

noncomputable section

/-- the planted branch as a simple graph on addresses -/
def G (b : Br) : SimpleGraph (List ℕ) := SimpleGraph.fromRel (fun u w => (u, w) ∈ edges b)

/-- graph degree -/
def gdeg (b : Br) (v : List ℕ) : ℕ := ((G b).neighborSet v).ncard

/-- planted degree: graph degree, plus 1 at the root for the phantom parent edge -/
def pdegG (b : Br) (v : List ℕ) : ℝ := (gdeg b v : ℝ) + (if v = [] then 1 else 0)

/-- the edge set of G b as a finset -/
def edgeFin (b : Br) : Finset (Sym2 (List ℕ)) := (edges b).image (fun e => s(e.1, e.2))

/-- a matching of the graph: distinct edges share no vertex -/
def IsGM (M : Finset (Sym2 (List ℕ))) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

instance : DecidablePred IsGM := fun M => by unfold IsGM; classical infer_instance

/-- edge weight lam / (pdeg u * pdeg w) -/
def wG (l : ℝ) (b : Br) : Sym2 (List ℕ) → ℝ :=
  Sym2.lift ⟨fun u w => l / (pdegG b u * pdegG b w), fun u w => by simp only [mul_comm]⟩

/-- the lambda-weighted matching sum of the graph G b (planted degrees) -/
def ZG (l : ℝ) (b : Br) : ℝ := ∑ M ∈ (edgeFin b).powerset, if IsGM M then ∏ e ∈ M, wG l b e else 0

lemma adj_iff (b : Br) (u w : List ℕ) : (G b).Adj u w ↔ (u, w) ∈ edges b ∨ (w, u) ∈ edges b := by
  simp only [G, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun huw => ?_, h⟩
    subst huw
    rcases h with h | h <;> have := edges_len b _ h <;> simp at this

lemma edgeFin_eq (b : Br) : (↑(edgeFin b) : Set (Sym2 (List ℕ))) = (G b).edgeSet := by
  ext x
  induction x using Sym2.ind with
  | h u w =>
    simp only [edgeFin, coe_image, Set.mem_image, mem_coe, SimpleGraph.mem_edgeSet, adj_iff]
    constructor
    · rintro ⟨e, he, hx⟩
      rcases Sym2.eq_iff.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [← h1, ← h2]; exact he
      · right; rw [← h1, ← h2]; exact he
    · rintro (h | h)
      · exact ⟨_, h, rfl⟩
      · exact ⟨_, h, Sym2.eq_swap⟩

lemma nbr_eq (b : Br) (v : List ℕ) : (G b).neighborSet v =
    ↑((((edges b).filter (fun e => e.1 = v)).image Prod.snd) ∪ (((edges b).filter (fun e => e.2 = v)).image Prod.fst)) := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, adj_iff, coe_union, coe_image, coe_filter, Set.mem_union, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · left; exact ⟨_, ⟨h, rfl⟩, rfl⟩
    · right; exact ⟨_, ⟨h, rfl⟩, rfl⟩
  · rintro (⟨e, ⟨he, h1⟩, h2⟩ | ⟨e, ⟨he, h1⟩, h2⟩)
    · left; rw [← h1, ← h2]; exact he
    · right; rw [← h1, ← h2]; exact he

lemma gdeg_eq (b : Br) (v : List ℕ) : gdeg b v = outC (edges b) v + inC (edges b) v := by
  unfold gdeg outC inC
  rw [nbr_eq, Set.ncard_coe_finset, card_union_of_disjoint]
  · rw [card_image_of_injOn, card_image_of_injOn]
    · intro e he e' he' h
      simp only [coe_filter, Set.mem_setOf_eq] at he he'
      exact Prod.ext h (he.2.trans he'.2.symm)
    · intro e he e' he' h
      simp only [coe_filter, Set.mem_setOf_eq] at he he'
      exact Prod.ext (he.2.trans he'.2.symm) h
  · rw [Finset.disjoint_left]
    intro w h1 h2
    obtain ⟨e, he, rfl⟩ := mem_image.mp h1
    obtain ⟨e', he', he'2⟩ := mem_image.mp h2
    have l1 := edges_len b e (mem_filter.mp he).1
    have l2 := edges_len b e' (mem_filter.mp he').1
    rw [(mem_filter.mp he).2] at l1
    rw [(mem_filter.mp he').2, he'2] at l2
    omega

lemma pdegG_eq {b : Br} {v : List ℕ} {c : Br} (h : subt b v = some c) : pdegG b v = pdeg b v := by
  obtain ⟨ho, hi⟩ := out_in_formula v b
  rw [h] at ho; rw [h] at hi
  simp only [Option.isSome_some, if_true] at hi
  unfold pdegG pdeg
  rw [gdeg_eq, ho, hi, h]
  by_cases hv : v = [] <;> simp [hv]

lemma valid_fst {b : Br} {e : List ℕ × List ℕ} (he : e ∈ edges b) : ∃ c, subt b e.1 = some c := by
  have ho := (out_in_formula e.1 b).1
  have hpos : 0 < outC (edges b) e.1 := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, rfl⟩⟩
  rcases hs : subt b e.1 with _ | c
  · rw [hs] at ho; simp only at ho; omega
  · exact ⟨c, rfl⟩

lemma valid_snd {b : Br} {e : List ℕ × List ℕ} (he : e ∈ edges b) : ∃ c, subt b e.2 = some c := by
  have hi := (out_in_formula e.2 b).2
  have hpos : 0 < inC (edges b) e.2 := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, rfl⟩⟩
  have hne : e.2 ≠ [] := by intro h; have := edges_len b e he; rw [h] at this; simp at this
  rw [if_neg hne] at hi
  rcases hs : subt b e.2 with _ | c
  · rw [hs] at hi; simp at hi; omega
  · exact ⟨c, rfl⟩

lemma wG_edge (l : ℝ) {b : Br} {e : List ℕ × List ℕ} (he : e ∈ edges b) : wG l b s(e.1, e.2) = wt l b e := by
  obtain ⟨c1, h1⟩ := valid_fst he
  obtain ⟨c2, h2⟩ := valid_snd he
  simp only [wG, Sym2.lift_mk, wt, pdegG_eq h1, pdegG_eq h2]

lemma sym_injOn (b : Br) : Set.InjOn (fun e : List ℕ × List ℕ => s(e.1, e.2)) ↑(edges b) := by
  intro e he e' he' h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · have l1 := edges_len b e he; have l2 := edges_len b e' he'
    rw [h1, h2] at l1; omega

/-- the matching sum over the graph equals the edge-list matching sum -/
theorem ZG_eq_Zl (l : ℝ) (b : Br) : ZG l b = Zl l b := by
  unfold ZG Zl Z edgeFin
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
    have hiso : IsM S ↔ IsGM (S.image φ) := by
      constructor
      · intro h x hx y hy hxy v hvx hvy
        obtain ⟨e, he, rfl⟩ := mem_image.mp hx
        obtain ⟨f, hf, rfl⟩ := mem_image.mp hy
        have hef : e ≠ f := fun h' => hxy (h' ▸ rfl)
        have hd := h e he f hf hef
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
    have hprod : ∏ e ∈ S, wt l b e = ∏ x ∈ S.image φ, wG l b x := by
      rw [prod_image (fun e he f hf h => hinj (hSE he) (hSE hf) h)]
      apply prod_congr rfl; intro e he; exact (wG_edge l (hSE he)).symm
    by_cases h : IsM S
    · rw [if_pos h, if_pos (hiso.mp h), hprod]
    · rw [if_neg h, if_neg (fun h' => h (hiso.mpr h'))]

/-- planted branches, on a Mathlib SimpleGraph: the cavity recursion is the lambda-weighted matching sum
    with planted degrees (graph degree, +1 at the root) -/
theorem Tl_eq_graph_matching_sum {l : ℝ} (hl : 0 ≤ l) (b : Br) : Tl l b = ZG l b := by
  rw [Tl_eq_matching_sum hl, ZG_eq_Zl]

end

end Br

end LeanCherry
