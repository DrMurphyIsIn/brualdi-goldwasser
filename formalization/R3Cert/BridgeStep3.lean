/-
  Bridge STEP 3 (RTree.Ztot = weighted matching sum).  See ../BRIDGE_DESIGN.md.

  `msum` is the weighted matching sum of an edge list (vertices in a decidable type `V`, edge `(u,v,w)`),
  by the standard include/exclude-the-head recursion.  Validated (exact Fraction, 200/200) to equal both the
  brute-force sum over matchings and `Ztot` of the realized RTree.

  CHUNK 1 (done): `msum`, `msum_cons`, `VDisj`, and disjoint-union multiplicativity `msum_append`.
  CHUNK 2 (this commit): generalize to a decidable vertex type `V`; realize a `RTree` as an edge list with
  ADDRESS vertices (`List ℕ`, the path from the root -- automatically unique), root edges emitted first
  (`rEdges = rRoot ++ rSub`) so `msum` can peel them.  The `Ztot = msum (rEdges [] t)` induction is next.
  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.CavityTree

namespace R3Cert
namespace Step3

open RTree

variable {V : Type} [DecidableEq V]

/-- `f` shares a vertex with the edge on vertices `u, v`. -/
def conflict (u v : V) (f : V × V × ℝ) : Bool :=
  decide (f.1 = u ∨ f.1 = v ∨ f.2.1 = u ∨ f.2.1 = v)

/-- The weighted matching sum of an edge list, by include/exclude the head edge. -/
def msum : List (V × V × ℝ) → ℝ
  | [] => 1
  | e :: rest => msum rest + e.2.2 * msum (rest.filter (fun f => ! conflict e.1 e.2.1 f))
termination_by E => E.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

@[simp] theorem msum_nil : msum ([] : List (V × V × ℝ)) = 1 := by rw [msum]

theorem msum_cons (e : V × V × ℝ) (rest : List (V × V × ℝ)) :
    msum (e :: rest) = msum rest + e.2.2 * msum (rest.filter (fun f => ! conflict e.1 e.2.1 f)) := by
  rw [msum]

/-- Vertex-disjointness of two edge lists: no edge of `E2` shares a vertex with any edge of `E1`. -/
def VDisj (E1 E2 : List (V × V × ℝ)) : Prop := ∀ f ∈ E2, ∀ e ∈ E1, conflict e.1 e.2.1 f = false

theorem VDisj.tail {e : V × V × ℝ} {E1 E2 : List (V × V × ℝ)} (h : VDisj (e :: E1) E2) : VDisj E1 E2 :=
  fun f hf g hg => h f hf g (List.mem_cons_of_mem _ hg)

theorem VDisj.filter {E1 E2 : List (V × V × ℝ)} (p : (V × V × ℝ) → Bool) (h : VDisj E1 E2) :
    VDisj (E1.filter p) E2 :=
  fun f hf g hg => h f hf g (List.mem_of_mem_filter hg)

theorem VDisj.tail_right {e : V × V × ℝ} {E1 E2 : List (V × V × ℝ)} (h : VDisj E1 (e :: E2)) :
    VDisj E1 E2 :=
  fun f hf g hg => h f (List.mem_cons_of_mem _ hf) g hg

theorem VDisj.filter_right {E1 E2 : List (V × V × ℝ)} (p : (V × V × ℝ) → Bool) (h : VDisj E1 E2) :
    VDisj E1 (E2.filter p) :=
  fun f hf g hg => h f (List.mem_of_mem_filter hf) g hg

/-- **Disjoint-union multiplicativity of the matching sum.** -/
theorem msum_append : ∀ (E1 E2 : List (V × V × ℝ)), VDisj E1 E2 → msum (E1 ++ E2) = msum E1 * msum E2
  | [], E2, _ => by simp
  | e :: E1, E2, h => by
    have hE2 : E2.filter (fun f => ! conflict e.1 e.2.1 f) = E2 := by
      apply List.filter_eq_self.mpr
      intro f hf
      have : conflict e.1 e.2.1 f = false := h f hf e (List.mem_cons.mpr (Or.inl rfl))
      simp [this]
    rw [List.cons_append, msum_cons, msum_cons, List.filter_append, hE2,
      msum_append E1 E2 h.tail, msum_append (E1.filter _) E2 (h.tail.filter _)]
    ring
termination_by E1 _ _ => E1.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

/-! ### Realization of an RTree as an edge list with ADDRESS vertices (`List ℕ`) -/

/- Realize an `RTree` rooted at address `a` as an edge list (address vertices), ROOT edges first. -/
mutual
/-- Realize an `RTree` rooted at address `a` as an edge list (address vertices), root edges first. -/
def rEdges : List ℕ → RTree → List (List ℕ × List ℕ × ℝ)
  | a, .node cs => rRoot a 0 cs ++ rSub a 0 cs
/-- The root's incident edges `(a, i :: a, w)` for each child `i`. -/
def rRoot : List ℕ → ℕ → List (ℝ × RTree) → List (List ℕ × List ℕ × ℝ)
  | _, _, [] => []
  | a, i, (w, _) :: rest => (a, i :: a, w) :: rRoot a (i + 1) rest
/-- The children's subtree edges (rooted at `i :: a`). -/
def rSub : List ℕ → ℕ → List (ℝ × RTree) → List (List ℕ × List ℕ × ℝ)
  | _, _, [] => []
  | a, i, (_, c) :: rest => rEdges (i :: a) c ++ rSub a (i + 1) rest
end

/-- The realized edge list of a whole tree (root address `[]`). -/
def realize (t : RTree) : List (List ℕ × List ℕ × ℝ) := rEdges [] t

theorem rRoot_nil (a : List ℕ) (i : ℕ) : rRoot a i [] = [] := by rw [rRoot]

theorem rSub_nil (a : List ℕ) (i : ℕ) : rSub a i [] = [] := by rw [rSub]

/-! ### Address-suffix structure and subtree disjointness -/

/-- Every endpoint of `E` has `b` as a suffix. -/
def AllSuffix (b : List ℕ) (E : List (List ℕ × List ℕ × ℝ)) : Prop :=
  ∀ e ∈ E, b <:+ e.1 ∧ b <:+ e.2.1

theorem allSuffix_append {b} {E1 E2 : List (List ℕ × List ℕ × ℝ)}
    (h1 : AllSuffix b E1) (h2 : AllSuffix b E2) : AllSuffix b (E1 ++ E2) := by
  intro e he; rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

mutual
theorem rEdges_allSuffix (b : List ℕ) (t : RTree) : AllSuffix b (rEdges b t) := by
  cases t with
  | node cs => rw [rEdges]; exact allSuffix_append (rRoot_allSuffix b 0 cs) (rSub_allSuffix b 0 cs)
theorem rRoot_allSuffix (b : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) : AllSuffix b (rRoot b i cs) := by
  cases cs with
  | nil => rw [rRoot]; intro e he; simp at he
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    rw [rRoot]
    intro e he
    rcases List.mem_cons.mp he with h | h
    · subst h; exact ⟨List.suffix_refl _, ⟨[i], rfl⟩⟩
    · exact rRoot_allSuffix b (i + 1) rest e h
theorem rSub_allSuffix (b : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) : AllSuffix b (rSub b i cs) := by
  cases cs with
  | nil => rw [rSub]; intro e he; simp at he
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    rw [rSub]
    refine allSuffix_append ?_ (rSub_allSuffix b (i + 1) rest)
    intro e he
    obtain ⟨h1, h2⟩ := rEdges_allSuffix (i :: b) c e he
    exact ⟨(List.suffix_cons i b).trans h1, (List.suffix_cons i b).trans h2⟩
end

/-- Two equal-length suffixes of the same list are equal. -/
theorem suffix_eq_of_length {s₁ s₂ l : List ℕ} (h₁ : s₁ <:+ l) (h₂ : s₂ <:+ l)
    (hl : s₁.length = s₂.length) : s₁ = s₂ := by
  obtain ⟨t₁, rfl⟩ := h₁
  obtain ⟨t₂, he⟩ := h₂
  have hlen : t₂.length = t₁.length := by
    have := congrArg List.length he
    simp only [List.length_append] at this; omega
  exact ((List.append_inj he hlen).2).symm

/-- **Subtree disjointness:** the realized edge lists of two DISTINCT children (addresses `i::a`, `j::a`)
    are vertex-disjoint. -/
theorem subtree_disj {a : List ℕ} {i j : ℕ} (ci cj : RTree) (hij : i ≠ j) :
    VDisj (rEdges (i :: a) ci) (rEdges (j :: a) cj) := by
  intro f hf e he
  obtain ⟨hf1, hf2⟩ := rEdges_allSuffix (j :: a) cj f hf
  obtain ⟨he1, he2⟩ := rEdges_allSuffix (i :: a) ci e he
  have key : ∀ (x y : List ℕ), (j :: a) <:+ x → (i :: a) <:+ y → x ≠ y := by
    intro x y hx hy hxy; subst hxy
    have : (j :: a) = (i :: a) := suffix_eq_of_length hx hy (by simp)
    exact hij (by simpa using this.symm)
  have h1 : f.1 ≠ e.1 := key _ _ hf1 he1
  have h2 : f.1 ≠ e.2.1 := key _ _ hf1 he2
  have h3 : f.2.1 ≠ e.1 := key _ _ hf2 he1
  have h4 : f.2.1 ≠ e.2.1 := key _ _ hf2 he2
  unfold conflict
  simp only [decide_eq_false_iff_not, not_or]
  exact ⟨h1, h2, h3, h4⟩

/-! ### Reusable `msum`/`VDisj` structure lemmas for the main induction -/

theorem conflict_comm (a b : List ℕ × List ℕ × ℝ) :
    conflict a.1 a.2.1 b = conflict b.1 b.2.1 a := by
  simp only [conflict, decide_eq_decide]
  constructor <;> rintro (h | h | h | h) <;> simp [h]

theorem VDisj.symm {E1 E2 : List (List ℕ × List ℕ × ℝ)} (h : VDisj E1 E2) : VDisj E2 E1 := by
  intro f hf e he
  rw [conflict_comm]
  exact h e he f hf

theorem VDisj.append_right {E1 E2 E3 : List (List ℕ × List ℕ × ℝ)}
    (h2 : VDisj E1 E2) (h3 : VDisj E1 E3) : VDisj E1 (E2 ++ E3) := by
  intro f hf e he
  rcases List.mem_append.mp hf with h | h
  · exact h2 f h e he
  · exact h3 f h e he

/-- Pull a disjoint block out of the middle of a matching-sum. -/
theorem msum_middle {A B C : List (List ℕ × List ℕ × ℝ)}
    (hAB : VDisj A B) (hAC : VDisj A C) (hBC : VDisj B C) :
    msum (A ++ B ++ C) = msum B * msum (A ++ C) := by
  rw [List.append_assoc, msum_append A (B ++ C) (hAB.append_right hAC),
    msum_append B C hBC, msum_append A C hAC]
  ring

/-- Vertex-disjointness from a common-suffix separation: `E1`'s endpoints all have suffix `p`, `E2`'s
    endpoints all avoid it. -/
theorem disj_of_suffix {E1 E2 : List (List ℕ × List ℕ × ℝ)} {p : List ℕ}
    (h1 : ∀ e ∈ E1, p <:+ e.1 ∧ p <:+ e.2.1)
    (h2 : ∀ f ∈ E2, ¬ p <:+ f.1 ∧ ¬ p <:+ f.2.1) : VDisj E1 E2 := by
  intro f hf e he
  obtain ⟨he1, he2⟩ := h1 e he
  obtain ⟨hf1, hf2⟩ := h2 f hf
  unfold conflict
  simp only [decide_eq_false_iff_not, not_or]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at hf1; exact hf1 he1
  · rw [h] at hf1; exact hf1 he2
  · rw [h] at hf2; exact hf2 he1
  · rw [h] at hf2; exact hf2 he2

/-! ### Filter-computation lemmas for the root-edge conditioning -/

theorem conflict_false {a b : List ℕ} {f : List ℕ × List ℕ × ℝ}
    (h1 : f.1 ≠ a) (h2 : f.1 ≠ b) (h3 : f.2.1 ≠ a) (h4 : f.2.1 ≠ b) :
    conflict a b f = false := by
  unfold conflict; simp only [decide_eq_false_iff_not, not_or]; exact ⟨h1, h2, h3, h4⟩

/-- A suffix equal in length to the whole list is that list. -/
theorem suffix_eq_self {s l : List ℕ} (h : s <:+ l) (hl : s.length = l.length) : s = l := by
  obtain ⟨t, rfl⟩ := h
  have ht : t = [] := by
    have : t.length = 0 := by simp only [List.length_append] at hl; omega
    exact List.length_eq_zero_iff.mp this
  simp [ht]

/-- Every root edge starts at the root vertex `a`. -/
theorem rRoot_first (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), ∀ f ∈ rRoot a j cs, f.1 = a := by
  induction cs with
  | nil => intro j f hf; rw [rRoot] at hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro j f hf
    rw [rRoot] at hf
    rcases List.mem_cons.mp hf with h | h
    · subst h; rfl
    · exact ih (j + 1) f h

/-- Under the include-filter for any root incident vertex `b`, all root edges vanish. -/
theorem rRoot_filter (a b : List ℕ) (cs : List (ℝ × RTree)) (j : ℕ) :
    (rRoot a j cs).filter (fun f => ! conflict a b f) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro f hf
  have hfa : f.1 = a := rRoot_first a cs j f hf
  simp [conflict, hfa]

/-- Subtree edges of children `≥ j` (with `j > i`) never touch `a` or `i :: a`. -/
theorem rSub_no_touch (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), i < j → ∀ f ∈ rSub a j cs, conflict a (i :: a) f = false := by
  induction cs with
  | nil => intro j _ f hf; rw [rSub] at hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro j hij f hf
    rw [rSub] at hf
    rcases List.mem_append.mp hf with h | h
    · obtain ⟨hf1, hf2⟩ := rEdges_allSuffix (j :: a) c f h
      refine conflict_false ?_ ?_ ?_ ?_
      · refine fun he => ?_
        have h' := (he ▸ hf1).length_le; simp only [List.length_cons] at h'; omega
      · refine fun he => ?_
        have hji : (j :: a) = (i :: a) := suffix_eq_self (he ▸ hf1) (by simp)
        simp only [List.cons.injEq] at hji; omega
      · refine fun he => ?_
        have h' := (he ▸ hf2).length_le; simp only [List.length_cons] at h'; omega
      · refine fun he => ?_
        have hji : (j :: a) = (i :: a) := suffix_eq_self (he ▸ hf2) (by simp)
        simp only [List.cons.injEq] at hji; omega
    · exact ih (j + 1) (by omega) f h

/-- Under the include-filter for `i :: a`, subtree edges of children `> i` are all preserved. -/
theorem rSub_filter (a : List ℕ) (i j : ℕ) (cs : List (ℝ × RTree)) (hij : i < j) :
    (rSub a j cs).filter (fun f => ! conflict a (i :: a) f) = rSub a j cs := by
  apply List.filter_eq_self.mpr
  intro f hf
  rw [rSub_no_touch a i cs j hij f hf]; rfl

/-- **Pull a disjoint block out of the middle of a matching sum** (needs only that `B` is disjoint from
    `A` and from `C`, NOT that `A`, `C` are mutually disjoint).  Well-founded on `A.length`. -/
theorem msum_pull : ∀ (A B C : List (List ℕ × List ℕ × ℝ)),
    VDisj B A → VDisj B C → msum (A ++ B ++ C) = msum B * msum (A ++ C)
  | [], B, C, _, hBC => by
    simp only [List.nil_append]
    exact msum_append B C hBC
  | a0 :: A', B, C, hBA, hBC => by
    have hBself : B.filter (fun f => ! conflict a0.1 a0.2.1 f) = B := by
      apply List.filter_eq_self.mpr
      intro f hf
      have : conflict a0.1 a0.2.1 f = false := by
        rw [conflict_comm]; exact hBA a0 (List.mem_cons.mpr (Or.inl rfl)) f hf
      rw [this]; rfl
    simp only [List.cons_append]
    rw [msum_cons, msum_cons]
    simp only [List.filter_append, hBself]
    rw [msum_pull A' B C hBA.tail_right hBC,
      msum_pull (A'.filter _) B (C.filter _) (hBA.tail_right.filter_right _) (hBC.filter_right _)]
    ring
termination_by A _ _ _ _ => A.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

/-! ### chunk 3d: cross-disjointness, the filter split, and the main theorem -/

/-- Disjointness from two DIFFERENT equal-length common suffixes. -/
theorem VDisj_of_suffix_ne {E1 E2 : List (List ℕ × List ℕ × ℝ)} {p q : List ℕ}
    (hp : ∀ e ∈ E1, p <:+ e.1 ∧ p <:+ e.2.1) (hq : ∀ f ∈ E2, q <:+ f.1 ∧ q <:+ f.2.1)
    (hlen : p.length = q.length) (hpq : p ≠ q) : VDisj E1 E2 := by
  intro f hf e he
  obtain ⟨he1, he2⟩ := hp e he
  obtain ⟨hf1, hf2⟩ := hq f hf
  have key : ∀ (x : List ℕ), p <:+ x → q <:+ x → False := fun x hx hqx =>
    hpq (suffix_eq_of_length hx hqx hlen)
  refine conflict_false (fun h => ?_) (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · exact key e.1 he1 (h ▸ hf1)
  · exact key e.2.1 he2 (h ▸ hf1)
  · exact key e.1 he1 (h ▸ hf2)
  · exact key e.2.1 he2 (h ▸ hf2)

theorem rEdges_disj_rSub (a : List ℕ) (i : ℕ) (c : RTree) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), i < j → VDisj (rEdges (i :: a) c) (rSub a j cs) := by
  induction cs with
  | nil => intro j _; rw [rSub]; intro f hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c'⟩ := p
    intro j hij
    rw [rSub]
    exact VDisj.append_right (subtree_disj c c' (by omega)) (ih (j + 1) (by omega))

theorem rRoot_no_isuffix (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), i < j → ∀ f ∈ rRoot a j cs, ¬ (i :: a) <:+ f.1 ∧ ¬ (i :: a) <:+ f.2.1 := by
  induction cs with
  | nil => intro j _ f hf; rw [rRoot] at hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c'⟩ := p
    intro j hij f hf
    rw [rRoot] at hf
    rcases List.mem_cons.mp hf with h | h
    · subst h
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · have := hs.length_le; simp only [List.length_cons] at this; omega
      · have heq : (i :: a) = (j :: a) := suffix_eq_self hs (by simp)
        simp only [List.cons.injEq] at heq; omega
    · exact ih (j + 1) (by omega) f h

theorem rEdges_disj_rRoot (a : List ℕ) (i : ℕ) (c : RTree) (cs : List (ℝ × RTree))
    (j : ℕ) (hij : i < j) : VDisj (rEdges (i :: a) c) (rRoot a j cs) :=
  disj_of_suffix (rEdges_allSuffix (i :: a) c) (rRoot_no_isuffix a i cs j hij)

theorem rSubc_disj_rSub (a : List ℕ) (i : ℕ) (csc : List (ℝ × RTree)) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), i < j → VDisj (rSub (i :: a) 0 csc) (rSub a j cs) := by
  induction cs with
  | nil => intro j _; rw [rSub]; intro f hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c'⟩ := p
    intro j hij
    rw [rSub]
    refine VDisj.append_right ?_ (ih (j + 1) (by omega))
    exact VDisj_of_suffix_ne (rSub_allSuffix (i :: a) 0 csc) (rEdges_allSuffix (j :: a) c')
      (by simp) (fun h => by simp only [List.cons.injEq] at h; omega)

theorem rSub_endpoints_long (b : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), ∀ f ∈ rSub b j cs, b.length < f.1.length ∧ b.length < f.2.1.length := by
  induction cs with
  | nil => intro j f hf; rw [rSub] at hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro j f hf
    rw [rSub] at hf
    rcases List.mem_append.mp hf with h | h
    · obtain ⟨hf1, hf2⟩ := rEdges_allSuffix (j :: b) c f h
      refine ⟨?_, ?_⟩
      · have := hf1.length_le; simp only [List.length_cons] at this; omega
      · have := hf2.length_le; simp only [List.length_cons] at this; omega
    · exact ih (j + 1) f h

/-- The children list of an `RTree`. -/
def childrenOf : RTree → List (ℝ × RTree) | .node cs => cs

/-- Under the include-filter for `i :: a`, a child subtree keeps exactly its grandchild subtrees. -/
theorem rEdges_filter (a : List ℕ) (i : ℕ) (c : RTree) :
    (rEdges (i :: a) c).filter (fun f => ! conflict a (i :: a) f) = rSub (i :: a) 0 (childrenOf c) := by
  cases c with
  | node cs =>
    rw [rEdges, List.filter_append]
    have h1 : (rRoot (i :: a) 0 cs).filter (fun f => ! conflict a (i :: a) f) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro f hf
      have : f.1 = i :: a := rRoot_first (i :: a) cs 0 f hf
      simp [conflict, this]
    have h2 : (rSub (i :: a) 0 cs).filter (fun f => ! conflict a (i :: a) f) = rSub (i :: a) 0 cs := by
      apply List.filter_eq_self.mpr
      intro f hf
      obtain ⟨hl1, hl2⟩ := rSub_endpoints_long (i :: a) cs 0 f hf
      have hne : conflict a (i :: a) f = false := by
        refine conflict_false (fun he => ?_) (fun he => ?_) (fun he => ?_) (fun he => ?_)
        · rw [he] at hl1; simp only [List.length_cons] at hl1; omega
        · rw [he] at hl1; simp only [List.length_cons] at hl1; omega
        · rw [he] at hl2; simp only [List.length_cons] at hl2; omega
        · rw [he] at hl2; simp only [List.length_cons] at hl2; omega
      rw [hne]; rfl
    rw [h1, h2, List.nil_append, childrenOf]

mutual
theorem Ztot_eq (a : List ℕ) (t : RTree) : Ztot t = msum (rEdges a t) := by
  cases t with
  | node cs => rw [rEdges, main_cond a 0 cs, Ztot]
  termination_by sizeOf t
theorem msum_rSub (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    msum (rSub a i cs) = Popen cs := by
  cases cs with
  | nil => rw [rSub, Popen]; simp
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    rw [rSub, Popen, msum_append _ _ (rEdges_disj_rSub a i c rest (i + 1) (by omega)),
      ← Ztot_eq (i :: a) c, msum_rSub a (i + 1) rest]
  termination_by sizeOf cs
theorem main_cond (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    msum (rRoot a i cs ++ rSub a i cs) = Popen cs + Matched cs := by
  cases cs with
  | nil => rw [rRoot, rSub, Popen, Matched]; simp
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    cases c with
    | node csc =>
      have hstruct : rRoot a i ((w, RTree.node csc) :: rest) ++ rSub a i ((w, RTree.node csc) :: rest)
          = (a, i :: a, w) :: (rRoot a (i + 1) rest ++ rEdges (i :: a) (RTree.node csc)
              ++ rSub a (i + 1) rest) := by
        rw [rRoot, rSub]; simp [List.append_assoc]
      have hr : (rRoot a (i + 1) rest).filter (fun f => ! conflict a (i :: a) f) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro f hf
        have : f.1 = a := rRoot_first a rest (i + 1) f hf
        simp [conflict, this]
      have hfilt : (rRoot a (i + 1) rest ++ rEdges (i :: a) (RTree.node csc) ++ rSub a (i + 1) rest).filter
          (fun f => ! conflict a (i :: a) f) = rSub (i :: a) 0 csc ++ rSub a (i + 1) rest := by
        rw [List.filter_append, List.filter_append, hr,
          rEdges_filter a i (RTree.node csc), rSub_filter a i (i + 1) rest (by omega),
          List.nil_append, childrenOf]
      rw [hstruct, msum_cons,
        msum_pull (rRoot a (i + 1) rest) (rEdges (i :: a) (RTree.node csc)) (rSub a (i + 1) rest)
          (rEdges_disj_rRoot a i (RTree.node csc) rest (i + 1) (by omega))
          (rEdges_disj_rSub a i (RTree.node csc) rest (i + 1) (by omega)),
        ← Ztot_eq (i :: a) (RTree.node csc), main_cond a (i + 1) rest, hfilt,
        msum_append _ _ (rSubc_disj_rSub a i csc rest (i + 1) (by omega)),
        msum_rSub (i :: a) 0 csc, msum_rSub a (i + 1) rest]
      simp only [Popen, Matched, Zopen]; ring
  termination_by sizeOf cs
end

/-- **STEP 3 (main): `Ztot t = weighted matching sum of the realized tree-graph`.** -/
theorem Ztot_eq_msum (t : RTree) : Ztot t = msum (realize t) := by
  rw [realize]; exact Ztot_eq [] t

end Step3
end R3Cert
