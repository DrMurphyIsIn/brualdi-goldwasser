/-
LeanCherry.Realize -- the reverse of tree_realize: every whole Br-tree b is a Mathlib tree on Fin (size b) with the same
matching sum.  Vertices: verts b = {[]} ∪ {children of edges}; a Fintype subtype, equivalent to Fin (size b).
  realize_br : ∃ H : SimpleGraph (Fin (size b)), H.IsTree ∧ ∀ l, piL l H = ZTl l b     (classical decidability)
-/
import LeanCherry.TreeStrict

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

noncomputable section

/-! ### structure of the edge set -/

lemma fan_parent : ∀ (j : ℕ) (L : List Br), ∀ e ∈ fanE j L, e.1 = e.2.dropLast
  | _, [], e, he => by simp [fanE] at he
  | j, c :: L, e, he => by
      simp only [fanE, mem_insert, mem_union, mem_map] at he
      rcases he with rfl | ⟨e', he', rfl⟩ | he
      · rfl
      · cases c with
        | node gs =>
          have h1 := fan_parent 0 gs e' (by rw [← edges_node]; exact he')
          have h2 := edge_len 0 gs e' (by rw [← edges_node]; exact he')
          have hne : e'.2 ≠ [] := by intro h; rw [h] at h2; simp at h2
          simp [sh_apply, h1, List.dropLast_cons_of_ne_nil hne]
      · exact fan_parent (j + 1) L e he

lemma edges_parent (b : Br) : ∀ e ∈ edges b, e.1 = e.2.dropLast := by
  cases b with | node cs => rw [edges_node]; exact fan_parent 0 cs

lemma fan_fst : ∀ (j : ℕ) (L : List Br), ∀ e ∈ fanE j L, e.1 = [] ∨ ∃ e' ∈ fanE j L, e'.2 = e.1
  | _, [], e, he => by simp [fanE] at he
  | j, c :: L, e, he => by
      simp only [fanE, mem_insert, mem_union, mem_map] at he
      rcases he with rfl | ⟨e', he', rfl⟩ | he
      · left; rfl
      · right
        cases c with
        | node gs =>
          rcases fan_fst 0 gs e' (by rw [← edges_node]; exact he') with h | ⟨e'', he'', h⟩
          · refine ⟨([], [j]), mem_insert_self _ _, ?_⟩
            simp [sh_apply, h]
          · refine ⟨sh j e'', ?_, ?_⟩
            · apply mem_insert_of_mem; apply mem_union_left
              exact mem_map_of_mem _ (by rw [edges_node]; exact he'')
            · simp [sh_apply, h]
      · rcases fan_fst (j + 1) L e he with h | ⟨e', he', h⟩
        · left; exact h
        · right; exact ⟨e', mem_insert_of_mem (mem_union_right _ he'), h⟩

lemma edges_fst (b : Br) : ∀ e ∈ edges b, e.1 = [] ∨ ∃ e' ∈ edges b, e'.2 = e.1 := by
  cases b with | node cs => rw [edges_node]; exact fan_fst 0 cs

mutual
theorem edges_card : ∀ b : Br, (edges b).card + 1 = size b
  | .node cs => by rw [edges_node, fan_card 0 cs]; rfl
theorem fan_card : ∀ (j : ℕ) (L : List Br), (fanE j L).card = sizeL L
  | _, [] => by simp [fanE, sizeL]
  | j, c :: L => by
      rw [fanE, card_insert_of_notMem (root_notin j c L),
        card_union_of_disjoint (disjoint_sh_fan_edges j c L), card_map, fan_card (j + 1) L]
      have := edges_card c
      simp only [sizeL]; omega
end

/-! ### vertices -/

def verts (b : Br) : Finset (List ℕ) := insert [] ((edges b).image Prod.snd)

lemma verts_card (b : Br) : (verts b).card = size b := by
  unfold verts
  rw [card_insert_of_notMem, card_image_of_injOn, edges_card]
  · intro e he e' he' h
    have h1 := edges_parent b e he; have h2 := edges_parent b e' he'
    exact Prod.ext (by rw [h1, h2]; exact congrArg _ h) h
  · intro h
    obtain ⟨e, he, h0⟩ := mem_image.mp h
    have := edges_len b e he; rw [h0] at this; simp at this

lemma fst_mem_verts {b : Br} {e : List ℕ × List ℕ} (he : e ∈ edges b) : e.1 ∈ verts b := by
  rcases edges_fst b e he with h | ⟨e', he', h⟩
  · rw [h]; exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_image.mpr ⟨e', he', h⟩)

lemma snd_mem_verts {b : Br} {e : List ℕ × List ℕ} (he : e ∈ edges b) : e.2 ∈ verts b :=
  mem_insert_of_mem (mem_image_of_mem _ he)

/-! ### the realization on Fin (size b) -/

/-- vertex numbering -/
def eqvV (b : Br) : Fin (size b) ≃ {v // v ∈ verts b} :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, verts_card])).symm

def gV (b : Br) (i : Fin (size b)) : List ℕ := (eqvV b i).val

lemma gV_inj (b : Br) : Function.Injective (gV b) := fun i j h => (eqvV b).injective (Subtype.ext h)

lemma gV_surj {b : Br} {v : List ℕ} (hv : v ∈ verts b) : gV b ((eqvV b).symm ⟨v, hv⟩) = v := by
  simp [gV]

/-- the realized graph -/
def HB (b : Br) : SimpleGraph (Fin (size b)) := SimpleGraph.fromRel (fun i j => (gV b i, gV b j) ∈ edges b)

open Classical in
lemma HB_edges (b : Br) : (HB b).edgeFinset.image (Sym2.map (gV b)) = edgeFin b := by
  ext x
  induction x using Sym2.ind with
  | h u w =>
    simp only [mem_image, edgeFin]
    constructor
    · rintro ⟨y, hy, hyx⟩
      induction y using Sym2.ind with
      | h i j =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, HB, SimpleGraph.fromRel_adj] at hy
        rw [Sym2.map_mk] at hyx
        rcases hy.2 with h | h
        · exact ⟨_, h, hyx⟩
        · exact ⟨_, h, by rw [← hyx, Sym2.eq_swap]⟩
    · rintro ⟨e, he, hex⟩
      set i := (eqvV b).symm ⟨e.1, fst_mem_verts he⟩
      set j := (eqvV b).symm ⟨e.2, snd_mem_verts he⟩
      have hi : gV b i = e.1 := gV_surj _
      have hj : gV b j = e.2 := gV_surj _
      refine ⟨s(i, j), ?_, by rw [Sym2.map_mk, hi, hj]; exact hex⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, HB, SimpleGraph.fromRel_adj]
      refine ⟨fun hij => ?_, Or.inl (by rw [hi, hj]; exact he)⟩
      have := edges_len b e he
      rw [← hi, ← hj, hij] at this; omega

lemma HB_adj_of_edge {b : Br} {e : List ℕ × List ℕ} (he : e ∈ edges b) :
    (HB b).Adj ((eqvV b).symm ⟨e.1, fst_mem_verts he⟩) ((eqvV b).symm ⟨e.2, snd_mem_verts he⟩) := by
  rw [HB, SimpleGraph.fromRel_adj, gV_surj, gV_surj]
  refine ⟨fun hij => ?_, Or.inl he⟩
  have h1 := congrArg (gV b) hij
  rw [gV_surj, gV_surj] at h1
  have := edges_len b e he; rw [h1] at this; omega

lemma HB_reach (b : Br) : ∀ k : ℕ, ∀ v (hv : v ∈ verts b), v.length = k →
    (HB b).Reachable ((eqvV b).symm ⟨[], mem_insert_self _ _⟩) ((eqvV b).symm ⟨v, hv⟩) := by
  intro k
  induction k with
  | zero =>
    intro v hv hk
    have : v = [] := List.length_eq_zero_iff.mp hk
    subst this; rfl
  | succ k IH =>
    intro v hv hk
    rcases mem_insert.mp hv with h | h
    · rw [h] at hk; simp at hk
    · obtain ⟨e, he, rfl⟩ := mem_image.mp h
      have hpar := edges_parent b e he
      have hlen := edges_len b e he
      have h1 := IH e.1 (fst_mem_verts he) (by omega)
      exact h1.trans (HB_adj_of_edge he).reachable

open Classical in
theorem HB_isTree (b : Br) : (HB b).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · have hn : Nonempty (Fin (size b)) := ⟨(eqvV b).symm ⟨[], mem_insert_self _ _⟩⟩
    refine ⟨fun x y => ?_⟩
    have hx := HB_reach b _ (gV b x) (eqvV b x).2 rfl
    have hy := HB_reach b _ (gV b y) (eqvV b y).2 rfl
    have ex : (eqvV b).symm ⟨gV b x, (eqvV b x).2⟩ = x := by simp [gV]
    have ey : (eqvV b).symm ⟨gV b y, (eqvV b y).2⟩ = y := by simp [gV]
    rw [ex] at hx; rw [ey] at hy
    exact hx.symm.trans hy
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 : ((HB b).edgeFinset.image (Sym2.map (gV b))).card = (HB b).edgeFinset.card :=
      card_image_of_injective _ (Sym2.map.injective (gV_inj b))
    rw [← h1, HB_edges, edgeFin, card_image_of_injOn (sym_injOn b), edges_card]

open Classical in
/-- every whole Br-tree is a Mathlib tree on Fin (size b) with the same matching sum -/
theorem realize_br (b : Br) : (HB b).IsTree ∧ ∀ l : ℝ, piL l (HB b) = ZTl l b :=
  ⟨HB_isTree b, fun l => piL_eq_ZTl (HB b) (gV_inj b) (HB_edges b) l⟩

end

end Br

end LeanCherry
