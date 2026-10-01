/-
LeanCherry.Bridge -- the cavity recursion for planted branches: Tl equals the lambda-weighted matching sum.

Vertices of b are addresses (List ℕ): [] is the root, i :: p is vertex p of the i-th child.  Edges are parent-child pairs
(parent, child): the root edges ([], [i]) and, for each child c_i, the edges of c_i with both endpoints prefixed by i.
Planted degree pdeg b v = (#children of the subtree at v) + 1 (for the root this is graph degree + 1 for the phantom parent
edge; for every other vertex it is its graph degree).  Edge weight wt l b (u, v) = l / (pdeg b u * pdeg b v).
  Zl l b := sum over matchings M of edges b of prod_{e in M} wt l b e      (MatchSum.Z)
Main theorem: Tl_eq_matching_sum : Tl l b = Zl l b.
-/
import LeanCherry.Extra
import LeanCherry.MatchSum

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

noncomputable section

/-- prefixing an address by i -/
def consE (i : ℕ) : List ℕ ↪ List ℕ := ⟨List.cons i, List.cons_injective⟩
/-- prefixing both endpoints of an edge by i -/
def sh (i : ℕ) : (List ℕ × List ℕ) ↪ (List ℕ × List ℕ) := (consE i).prodMap (consE i)

lemma sh_apply (i : ℕ) (e : List ℕ × List ℕ) : sh i e = (i :: e.1, i :: e.2) := rfl

mutual
/-- parent-child edges of a planted branch -/
def edges : Br → Finset (List ℕ × List ℕ)
  | .node cs => fanE 0 cs
/-- edges of a root whose children are the list, numbered from i -/
def fanE : ℕ → List Br → Finset (List ℕ × List ℕ)
  | _, [] => ∅
  | i, c :: cs => insert ([], [i]) ((edges c).map (sh i) ∪ fanE (i + 1) cs)
end

/-- the same without the root edges (the forest of children, numbered from i) -/
def restE : ℕ → List Br → Finset (List ℕ × List ℕ)
  | _, [] => ∅
  | i, c :: cs => (edges c).map (sh i) ∪ restE (i + 1) cs

/-- children of a node -/
def kids : Br → List Br
  | .node cs => cs
/-- number of children -/
def nch (b : Br) : ℕ := (kids b).length

/-- the subtree at an address -/
def subt : Br → List ℕ → Option Br
  | b, [] => some b
  | .node cs, i :: p => match cs[i]? with
    | some c => subt c p
    | none => none

/-- planted degree of a vertex: #children + 1 -/
def pdeg (b : Br) (v : List ℕ) : ℝ :=
  match subt b v with
  | some c => (nch c : ℝ) + 1
  | none => 1

/-- edge weight -/
def wt (l : ℝ) (b : Br) (e : List ℕ × List ℕ) : ℝ := l / (pdeg b e.1 * pdeg b e.2)

/-- the lambda-weighted matching sum of a planted branch -/
def Zl (l : ℝ) (b : Br) : ℝ := Z (wt l b) (edges b)

/-! ### weights of shifted edges -/

lemma subt_cons {cs : List Br} {i : ℕ} {c : Br} (h : cs[i]? = some c) (p : List ℕ) :
    subt (.node cs) (i :: p) = subt c p := by
  simp [subt, h]

lemma wt_sh {l : ℝ} {cs : List Br} {i : ℕ} {c : Br} (h : cs[i]? = some c) (e : List ℕ × List ℕ) :
    wt l (.node cs) (sh i e) = wt l c e := by
  simp only [wt, pdeg, sh_apply, subt_cons h]

lemma wt_root {l : ℝ} {cs : List Br} {i : ℕ} {c : Br} (h : cs[i]? = some c) :
    wt l (.node cs) ([], [i]) = l / (((cs.length : ℝ) + 1) * ((nch c : ℝ) + 1)) := by
  have h1 : subt (.node cs) [i] = some c := by rw [subt_cons h]; rfl
  simp only [wt, pdeg, h1]
  rfl

/-! ### vertex-support facts -/

/-- every vertex of a fan edge (offset j) is the root or starts with some k >= j -/
lemma fanE_verts : ∀ (j : ℕ) (L : List Br), ∀ e ∈ fanE j L, ∀ v ∈ ev e,
    v = [] ∨ ∃ k u, j ≤ k ∧ v = k :: u
  | _, [], e, he => by simp [fanE] at he
  | j, c :: L, e, he => by
      intro v hv
      simp only [fanE, mem_insert, mem_union, mem_map] at he
      rcases he with rfl | ⟨e', _, rfl⟩ | he
      · simp only [ev, mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · left; rfl
        · right; exact ⟨j, [], le_rfl, rfl⟩
      · simp only [ev, sh_apply, mem_insert, mem_singleton] at hv
        right; rcases hv with rfl | rfl
        · exact ⟨j, _, le_rfl, rfl⟩
        · exact ⟨j, _, le_rfl, rfl⟩
      · rcases fanE_verts (j + 1) L e he v hv with h | ⟨k, u, hk, rfl⟩
        · left; exact h
        · right; exact ⟨k, u, by omega, rfl⟩

lemma restE_verts : ∀ (j : ℕ) (L : List Br), ∀ e ∈ restE j L, ∀ v ∈ ev e, ∃ k u, j ≤ k ∧ v = k :: u
  | _, [], e, he => by simp [restE] at he
  | j, c :: L, e, he => by
      intro v hv
      simp only [restE, mem_union, mem_map] at he
      rcases he with ⟨e', _, rfl⟩ | he
      · simp only [ev, sh_apply, mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact ⟨j, _, le_rfl, rfl⟩
        · exact ⟨j, _, le_rfl, rfl⟩
      · obtain ⟨k, u, hk, rfl⟩ := restE_verts (j + 1) L e he v hv
        exact ⟨k, u, by omega, rfl⟩

lemma sh_verts (i : ℕ) (E : Finset (List ℕ × List ℕ)) : ∀ e ∈ E.map (sh i), ∀ v ∈ ev e, ∃ u, v = i :: u := by
  intro e he v hv
  obtain ⟨e', _, rfl⟩ := mem_map.mp he
  simp only [ev, sh_apply, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩

lemma disj_sh_fan (i : ℕ) (E : Finset (List ℕ × List ℕ)) (L : List Br) :
    ∀ e ∈ E.map (sh i), ∀ f ∈ fanE (i + 1) L, Disjoint (ev e) (ev f) := by
  intro e he f hf
  rw [Finset.disjoint_left]
  intro v hve hvf
  obtain ⟨u, rfl⟩ := sh_verts i E e he v hve
  rcases fanE_verts (i + 1) L f hf _ hvf with h | ⟨k, u', hk, h⟩
  · exact List.cons_ne_nil _ _ h
  · have := (List.cons.inj h).1; omega

lemma disj_sh_rest (i : ℕ) (E : Finset (List ℕ × List ℕ)) (L : List Br) :
    ∀ e ∈ E.map (sh i), ∀ f ∈ restE (i + 1) L, Disjoint (ev e) (ev f) := by
  intro e he f hf
  rw [Finset.disjoint_left]
  intro v hve hvf
  obtain ⟨u, rfl⟩ := sh_verts i E e he v hve
  obtain ⟨k, u', hk, h⟩ := restE_verts (i + 1) L f hf _ hvf
  have := (List.cons.inj h).1; omega

/-! ### filtering out the root -/

/-- removing the edges at the root of a fan leaves the forest -/
lemma fanE_filter_root : ∀ (j : ℕ) (L : List Br),
    (fanE j L).filter (fun f => ([] : List ℕ) ∉ ev f) = restE j L
  | _, [] => by simp [fanE, restE]
  | j, c :: L => by
      rw [fanE, filter_insert, if_neg (by simp [ev]), filter_union, fanE_filter_root (j + 1) L, restE]
      congr 1
      apply filter_true_of_mem
      intro f hf h0
      obtain ⟨u, hu⟩ := sh_verts j (edges c) f hf [] h0
      exact List.cons_ne_nil _ _ hu.symm

end

end Br

end LeanCherry
