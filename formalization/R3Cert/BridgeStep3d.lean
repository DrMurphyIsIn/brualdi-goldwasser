/-
  Bridge STEP 3d: the involutions <-> matchings bijection.

  `Matching.lean`'s H2a (`pi_eq_weighted_matching_sum`, CI-green) writes
  `pi(T) = per L(T) / prod deg` as a `Finset` sum over the EDGE-SUPPORTED PERMUTATIONS of an
  acyclic `SimpleGraph`; `BridgeStep3c` (`msum_eq_finset_sum`) writes `msum E` as a `Finset`
  sum over the matching enumeration `subm E`.  This file closes that gap with the explicit
  bijection:

  * forward  `sigma |-> E.filter (fun e => sigma e.1 = e.2.1)`  (the matched edges);
  * backward `M |-> toPerm M`  (the product of the transpositions `swap e.1 e.2.1`, `e in M`);
  * weights  `prod_v (1 if sigma v = v else 1/deg v) = wprod M`  (2-cycles pair the degrees).

  Main results, for `E : IsEdgeEnum G` (each edge of `G` listed exactly once in one
  orientation, weight `1/(deg u * deg v)`) with `G` acyclic:

  * `sum_involutions_eq_msum` -- the H2a involution sum equals `msum E`;
  * `pi_eq_msum` -- `per L(G) / prod deg = msum E`: the REAL amplitude `pi` is a `Step3.msum`,
    the same combinatorial language the `Branch`/`RTree` side already speaks (Steps 1-3).

  Genuine proofs (no `sorry`).  The remaining bridge gap after this file is Step 4's
  amplitude seam (the `p -> infinity` cherry-hub limit).
-/
import Mathlib
import R3Cert.Matching
import R3Cert.BridgeStep3c

namespace R3Cert
namespace Step3

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### An edge enumeration of a `SimpleGraph` with Laplacian weights -/

/-- `E` lists every edge of `G` exactly once (in one orientation), weighted `1/(deg u * deg v)`. -/
structure IsEdgeEnum (E : List (V × V × ℝ)) : Prop where
  nodup : E.Nodup
  adj : ∀ e ∈ E, G.Adj e.1 e.2.1
  weight : ∀ e ∈ E, e.2.2 = 1 / ((G.degree e.1 : ℝ) * (G.degree e.2.1 : ℝ))
  complete : ∀ {u v : V}, G.Adj u v → ∃ e ∈ E, (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u)
  unique : ∀ e ∈ E, ∀ f ∈ E,
    (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e

/-! ### `compatQ`/`matchQ` unpacking -/

theorem compat_vertex_ne {e f : V × V × ℝ} (h : compatQ e f = true) :
    f.1 ≠ e.1 ∧ f.1 ≠ e.2.1 ∧ f.2.1 ≠ e.1 ∧ f.2.1 ≠ e.2.1 := by
  unfold compatQ at h
  cases hc : conflict e.1 e.2.1 f with
  | true => rw [hc] at h; exact absurd h (by decide)
  | false =>
    unfold conflict at hc
    have h' := of_decide_eq_false hc
    push_neg at h'
    exact h'

theorem conflict_cases {e f : V × V × ℝ} (h : ¬ compatQ e f = true) :
    f.1 = e.1 ∨ f.1 = e.2.1 ∨ f.2.1 = e.1 ∨ f.2.1 = e.2.1 := by
  cases hc : conflict e.1 e.2.1 f with
  | false => exact absurd (show compatQ e f = true by unfold compatQ; rw [hc]; decide) h
  | true =>
    unfold conflict at hc
    exact of_decide_eq_true hc

theorem matchQ_cons {e : V × V × ℝ} {M : List (V × V × ℝ)} (h : matchQ (e :: M) = true) :
    (∀ f ∈ M, compatQ e f = true) ∧ matchQ M = true := by
  rw [matchQ] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h

/-- A filter of a duplicate-free list is a matching as soon as any two DISTINCT selected
    elements are vertex-disjoint. -/
theorem matchQ_filter {p : V × V × ℝ → Bool} :
    ∀ (E : List (V × V × ℝ)), E.Nodup →
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → p e = true → p f = true → compatQ e f = true) →
      matchQ (E.filter p) = true
  | [], _, _ => rfl
  | e :: E, hnd, h => by
    obtain ⟨he, hE⟩ := List.nodup_cons.mp hnd
    have hsub : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → p a = true → p b = true → compatQ a b = true :=
      fun a ha b hb => h a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb))
    rw [List.filter_cons]
    by_cases hp : p e = true
    · rw [if_pos hp, matchQ]
      simp only [Bool.and_eq_true, List.all_eq_true]
      refine ⟨fun f hf => ?_, matchQ_filter E hE hsub⟩
      have hfE : f ∈ E := List.mem_of_mem_filter hf
      have hpf : p f = true := List.of_mem_filter hf
      exact h e (List.mem_cons.mpr (Or.inl rfl)) f (List.mem_cons.mpr (Or.inr hfE))
        (fun hef => he (by rw [hef]; exact hfE)) hp hpf
    · rw [if_neg hp]
      exact matchQ_filter E hE hsub

/-! ### The touched-vertex set of an edge list -/

/-- The set of vertices covered by an edge list. -/
def touchedSet : List (V × V × ℝ) → Finset V
  | [] => ∅
  | e :: M => insert e.1 (insert e.2.1 (touchedSet M))

@[simp] theorem touchedSet_nil : touchedSet ([] : List (V × V × ℝ)) = ∅ := rfl

theorem touchedSet_cons (e : V × V × ℝ) (M : List (V × V × ℝ)) :
    touchedSet (e :: M) = insert e.1 (insert e.2.1 (touchedSet M)) := rfl

theorem mem_touchedSet : ∀ {M : List (V × V × ℝ)} {v : V},
    v ∈ touchedSet M ↔ ∃ e ∈ M, e.1 = v ∨ e.2.1 = v := by
  intro M v
  induction M with
  | nil => simp [touchedSet_nil]
  | cons e M ih =>
    simp only [touchedSet_cons, Finset.mem_insert, ih, List.mem_cons]
    constructor
    · rintro (rfl | rfl | ⟨f, hf, h⟩)
      · exact ⟨e, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨e, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨f, Or.inr hf, h⟩
    · rintro ⟨f, (rfl | hf), (h | h)⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr ⟨f, hf, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨f, hf, Or.inr h⟩)

/-! ### The involution built from a matching -/

/-- The permutation swapping the endpoints of every edge of `M`. -/
def toPerm : List (V × V × ℝ) → Equiv.Perm V
  | [] => 1
  | e :: M => Equiv.swap e.1 e.2.1 * toPerm M

@[simp] theorem toPerm_nil : toPerm ([] : List (V × V × ℝ)) = 1 := rfl

theorem toPerm_cons (e : V × V × ℝ) (M : List (V × V × ℝ)) :
    toPerm (e :: M) = Equiv.swap e.1 e.2.1 * toPerm M := rfl

/-- A vertex touched by no edge of `M` is fixed. -/
theorem toPerm_apply_of_notMem : ∀ (M : List (V × V × ℝ)) (v : V),
    (∀ e ∈ M, e.1 ≠ v ∧ e.2.1 ≠ v) → toPerm M v = v
  | [], v, _ => by rw [toPerm_nil]; rfl
  | e :: M, v, h => by
    have he := h e (List.mem_cons.mpr (Or.inl rfl))
    rw [toPerm_cons, Equiv.Perm.mul_apply,
      toPerm_apply_of_notMem M v (fun f hf => h f (List.mem_cons.mpr (Or.inr hf)))]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm he.1) (Ne.symm he.2)

/-- The head edge of a matching is swapped by `toPerm`. -/
theorem toPerm_head (g : V × V × ℝ) (M : List (V × V × ℝ))
    (hall : ∀ f ∈ M, compatQ g f = true) :
    toPerm (g :: M) g.1 = g.2.1 ∧ toPerm (g :: M) g.2.1 = g.1 := by
  have h1 : toPerm M g.1 = g.1 := toPerm_apply_of_notMem M g.1 (fun f hf => by
    obtain ⟨a, b, c, d⟩ := compat_vertex_ne (hall f hf); exact ⟨a, c⟩)
  have h2 : toPerm M g.2.1 = g.2.1 := toPerm_apply_of_notMem M g.2.1 (fun f hf => by
    obtain ⟨a, b, c, d⟩ := compat_vertex_ne (hall f hf); exact ⟨b, d⟩)
  constructor
  · rw [toPerm_cons, Equiv.Perm.mul_apply, h1, Equiv.swap_apply_left]
  · rw [toPerm_cons, Equiv.Perm.mul_apply, h2, Equiv.swap_apply_right]

/-- **`toPerm` swaps every edge of a matching.** -/
theorem toPerm_apply_fst : ∀ (M : List (V × V × ℝ)), matchQ M = true →
    ∀ e ∈ M, toPerm M e.1 = e.2.1 ∧ toPerm M e.2.1 = e.1
  | [], _, e, he => absurd he (by simp)
  | g :: M, hM, e, he => by
    obtain ⟨hall, hM'⟩ := matchQ_cons hM
    rcases List.mem_cons.mp he with heq | he'
    · rw [heq]; exact toPerm_head g M hall
    · obtain ⟨ih1, ih2⟩ := toPerm_apply_fst M hM' e he'
      obtain ⟨a, b, c, d⟩ := compat_vertex_ne (hall e he')
      constructor
      · rw [toPerm_cons, Equiv.Perm.mul_apply, ih1]
        exact Equiv.swap_apply_of_ne_of_ne c d
      · rw [toPerm_cons, Equiv.Perm.mul_apply, ih2]
        exact Equiv.swap_apply_of_ne_of_ne a b

/-! ### Well-definedness of the two maps -/

/-- The matched-edge list of an edge-supported permutation of an acyclic graph is a matching. -/
theorem matchQ_Mσ (hG : G.IsAcyclic) {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E)
    {σ : Equiv.Perm V} (hES : EdgeSupported G σ) :
    matchQ (E.filter (fun e => decide (σ e.1 = e.2.1))) = true := by
  have hinv : Function.Involutive σ := acyclicForcesInvolution G σ hG hES
  refine matchQ_filter E henum.nodup (fun e he f hf hef hpe hpf => ?_)
  have hσe : σ e.1 = e.2.1 := of_decide_eq_true hpe
  have hσf : σ f.1 = f.2.1 := of_decide_eq_true hpf
  have hback : σ e.2.1 = e.1 := by rw [← hσe]; exact hinv e.1
  have hbackf : σ f.2.1 = f.1 := by rw [← hσf]; exact hinv f.1
  by_contra hc
  rcases conflict_cases hc with h | h | h | h
  · exact hef (henum.unique e he f hf
      (Or.inl ⟨h, by rw [← hσf, h, hσe]⟩)).symm
  · exact hef (henum.unique e he f hf
      (Or.inr ⟨h, by rw [← hσf, h, hback]⟩)).symm
  · exact hef (henum.unique e he f hf
      (Or.inr ⟨by rw [← hbackf, h, hσe], h⟩)).symm
  · exact hef (henum.unique e he f hf
      (Or.inl ⟨by rw [← hbackf, h, hback], h⟩)).symm

/-- `toPerm` of a matching of `E` is edge-supported. -/
theorem toPerm_edgeSupported {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E)
    {M : List (V × V × ℝ)} (hM : M ∈ subm E) : EdgeSupported G (toPerm M) := by
  obtain ⟨hsub, hmatch⟩ := (mem_subm E M).mp hM
  intro v
  by_cases htouch : ∃ f ∈ M, f.1 = v ∨ f.2.1 = v
  · obtain ⟨f, hfM, hor⟩ := htouch
    have hadj := henum.adj f (hsub.subset hfM)
    obtain ⟨h1, h2⟩ := toPerm_apply_fst M hmatch f hfM
    rcases hor with rfl | rfl
    · exact Or.inr (by rw [h1]; exact hadj)
    · exact Or.inr (by rw [h2]; exact hadj.symm)
  · push_neg at htouch
    exact Or.inl (toPerm_apply_of_notMem M v htouch)

/-! ### The two round trips -/

/-- Two sublists of a duplicate-free list with the same members are equal. -/
theorem sublist_eq_of_nodup {α : Type} {E : List α} : ∀ {M M' : List α},
    M.Sublist E → M'.Sublist E → E.Nodup → (∀ x, x ∈ M ↔ x ∈ M') → M = M' := by
  induction E with
  | nil =>
    intro M M' h h' _ _
    rw [List.sublist_nil.mp h, List.sublist_nil.mp h']
  | cons a E ih =>
    intro M M' h h' hnd hiff
    obtain ⟨ha, hE⟩ := List.nodup_cons.mp hnd
    rcases List.sublist_cons_iff.mp h with hM | ⟨M₁, rfl, hM₁⟩
    · rcases List.sublist_cons_iff.mp h' with hM' | ⟨M₁', rfl, hM₁'⟩
      · exact ih hM hM' hE hiff
      · exact absurd (hM.subset ((hiff a).mpr (List.mem_cons.mpr (Or.inl rfl)))) ha
    · rcases List.sublist_cons_iff.mp h' with hM' | ⟨M₁', rfl, hM₁'⟩
      · exact absurd (hM'.subset ((hiff a).mp (List.mem_cons.mpr (Or.inl rfl)))) ha
      · have htails : M₁ = M₁' := by
          refine ih hM₁ hM₁' hE (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
          · have hxa : x ≠ a := fun hxa => ha (hxa ▸ hM₁.subset hx)
            rcases List.mem_cons.mp ((hiff x).mp (List.mem_cons.mpr (Or.inr hx))) with
              hcontra | hgood
            · exact absurd hcontra hxa
            · exact hgood
          · have hxa : x ≠ a := fun hxa => ha (hxa ▸ hM₁'.subset hx)
            rcases List.mem_cons.mp ((hiff x).mpr (List.mem_cons.mpr (Or.inr hx))) with
              hcontra | hgood
            · exact absurd hcontra hxa
            · exact hgood
        rw [htails]

/-- **Round trip 2: filtering `E` by `toPerm M` recovers the matching `M`.** -/
theorem filter_toPerm {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E)
    {M : List (V × V × ℝ)} (hM : M ∈ subm E) :
    E.filter (fun e => decide (toPerm M e.1 = e.2.1)) = M := by
  obtain ⟨hsub, hmatch⟩ := (mem_subm E M).mp hM
  refine sublist_eq_of_nodup List.filter_sublist hsub henum.nodup (fun e => ?_)
  constructor
  · intro he
    have heE := List.mem_of_mem_filter he
    have hpe' := List.of_mem_filter he
    have hpe : toPerm M e.1 = e.2.1 := of_decide_eq_true hpe'
    by_cases htouch : ∃ f ∈ M, f.1 = e.1 ∨ f.2.1 = e.1
    · obtain ⟨f, hfM, hor⟩ := htouch
      have hfE : f ∈ E := hsub.subset hfM
      obtain ⟨hf1, hf2⟩ := toPerm_apply_fst M hmatch f hfM
      rcases hor with h | h
      · have hkey : f.2.1 = e.2.1 := by rw [← hpe, ← h, hf1]
        rw [← henum.unique e heE f hfE (Or.inl ⟨h, hkey⟩)]
        exact hfM
      · have hkey : f.1 = e.2.1 := by rw [← hpe, ← h, hf2]
        rw [← henum.unique e heE f hfE (Or.inr ⟨hkey, h⟩)]
        exact hfM
    · push_neg at htouch
      have hfixed : toPerm M e.1 = e.1 := toPerm_apply_of_notMem M e.1 htouch
      rw [hfixed] at hpe
      exact absurd hpe (henum.adj e heE).ne
  · intro heM
    exact List.mem_filter.mpr ⟨hsub.subset heM,
      decide_eq_true (toPerm_apply_fst M hmatch e heM).1⟩

/-- **Round trip 1: `toPerm` of the matched-edge list recovers the involution.** -/
theorem toPerm_filter (hG : G.IsAcyclic) {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E)
    {σ : Equiv.Perm V} (hES : EdgeSupported G σ) :
    toPerm (E.filter (fun e => decide (σ e.1 = e.2.1))) = σ := by
  have hinv : Function.Involutive σ := acyclicForcesInvolution G σ hG hES
  have hmσ : matchQ (E.filter (fun e => decide (σ e.1 = e.2.1))) = true :=
    matchQ_Mσ G hG henum hES
  apply Equiv.ext
  intro v
  by_cases hv : σ v = v
  · rw [hv]
    refine toPerm_apply_of_notMem _ v (fun f hf => ?_)
    have hfσ' := List.of_mem_filter hf
    have hfσ : σ f.1 = f.2.1 := of_decide_eq_true hfσ'
    have hadj := henum.adj f (List.mem_of_mem_filter hf)
    constructor
    · intro h
      exact hadj.ne (by rw [← hfσ, h, hv])
    · intro h
      have hb : σ f.2.1 = f.1 := by rw [← hfσ]; exact hinv f.1
      exact hadj.ne (by rw [← hb, h, hv])
  · rcases hES v with h | hadj
    · exact absurd h hv
    · obtain ⟨e, heE, hor⟩ := henum.complete hadj
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hin : e ∈ E.filter (fun e => decide (σ e.1 = e.2.1)) :=
          List.mem_filter.mpr ⟨heE, decide_eq_true (by rw [h1, h2])⟩
        have happ := (toPerm_apply_fst _ hmσ e hin).1
        rw [h1, h2] at happ
        exact happ
      · have hin : e ∈ E.filter (fun e => decide (σ e.1 = e.2.1)) :=
          List.mem_filter.mpr ⟨heE, decide_eq_true (by rw [h1, h2, hinv v])⟩
        have happ := (toPerm_apply_fst _ hmσ e hin).2
        rw [h2, h1] at happ
        exact happ

/-! ### The weight identity -/

/-- The degree product over the touched vertices of a matching is its weight product. -/
theorem prod_touched_eq_wprod {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E) :
    ∀ (M : List (V × V × ℝ)), M.Sublist E → matchQ M = true →
      ∏ v ∈ touchedSet M, (1 / (G.degree v : ℝ)) = wprod M := by
  intro M
  induction M with
  | nil => intro _ _; simp [touchedSet_nil, wprod]
  | cons e M ih =>
    intro hsub hq
    obtain ⟨hall, hq'⟩ := matchQ_cons hq
    have heE : e ∈ E := hsub.subset (List.mem_cons.mpr (Or.inl rfl))
    have hadj := henum.adj e heE
    have hsub' : M.Sublist E := (List.sublist_cons_self e M).trans hsub
    have he1 : e.1 ∉ insert e.2.1 (touchedSet M) := by
      simp only [Finset.mem_insert, mem_touchedSet]
      rintro (h | ⟨f, hf, h | h⟩)
      · exact hadj.ne h
      · exact (compat_vertex_ne (hall f hf)).1 h
      · exact (compat_vertex_ne (hall f hf)).2.2.1 h
    have he2 : e.2.1 ∉ touchedSet M := by
      rw [mem_touchedSet]
      rintro ⟨f, hf, h | h⟩
      · exact (compat_vertex_ne (hall f hf)).2.1 h
      · exact (compat_vertex_ne (hall f hf)).2.2.2 h
    rw [touchedSet_cons e M, Finset.prod_insert he1, Finset.prod_insert he2,
      ih hsub' hq', wprod_cons, henum.weight e heE]
    ring

/-- **The weight identity: the H2a per-vertex product equals `wprod` of the matching.** -/
theorem prod_weights {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E)
    {M : List (V × V × ℝ)} (hM : M ∈ subm E) :
    ∏ v, (if toPerm M v = v then (1 : ℝ) else 1 / (G.degree v : ℝ)) = wprod M := by
  obtain ⟨hsub, hmatch⟩ := (mem_subm E M).mp hM
  have hfix : ∀ v, toPerm M v = v ↔ v ∉ touchedSet M := by
    intro v
    constructor
    · intro hv htouch
      rw [mem_touchedSet] at htouch
      obtain ⟨f, hfM, hor⟩ := htouch
      have hadj := henum.adj f (hsub.subset hfM)
      obtain ⟨h1, h2⟩ := toPerm_apply_fst M hmatch f hfM
      rcases hor with h | h
      · exact hadj.ne (by rw [← h1, h, hv])
      · exact hadj.ne' (by rw [← h2, h, hv])
    · intro h
      refine toPerm_apply_of_notMem M v (fun f hf => ?_)
      constructor
      · exact fun h1 => h (mem_touchedSet.mpr ⟨f, hf, Or.inl h1⟩)
      · exact fun h2 => h (mem_touchedSet.mpr ⟨f, hf, Or.inr h2⟩)
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => toPerm M v = v)]
  have h1 : (∏ v ∈ Finset.univ.filter (fun v => toPerm M v = v),
      (if toPerm M v = v then (1 : ℝ) else 1 / (G.degree v : ℝ))) = 1 :=
    Finset.prod_eq_one (fun v hv => if_pos (Finset.mem_filter.mp hv).2)
  have hset : Finset.univ.filter (fun v => ¬ toPerm M v = v) = touchedSet M := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfix v]
    exact not_not
  have h2 : (∏ v ∈ Finset.univ.filter (fun v => ¬ toPerm M v = v),
      (if toPerm M v = v then (1 : ℝ) else 1 / (G.degree v : ℝ)))
      = ∏ v ∈ touchedSet M, (1 / (G.degree v : ℝ)) := by
    rw [hset]
    refine Finset.prod_congr rfl (fun v hv => ?_)
    exact if_neg (fun h => (hfix v).mp h hv)
  rw [h1, h2, one_mul]
  exact prod_touched_eq_wprod G henum M hsub hmatch

/-! ### The bijection and the main theorem -/

open scoped Classical in
/-- **The involutions <-> matchings bijection: the H2a sum is `msum E`.** -/
theorem sum_involutions_eq_msum (hG : G.IsAcyclic) {E : List (V × V × ℝ)}
    (henum : IsEdgeEnum G E) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm V => EdgeSupported G σ),
        ∏ v, (if σ v = v then (1 : ℝ) else 1 / (G.degree v : ℝ))
      = msum E := by
  rw [msum_eq_finset_sum E henum.nodup]
  refine Finset.sum_nbij' (i := fun σ => E.filter (fun e => decide (σ e.1 = e.2.1)))
    (j := fun M => toPerm M) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    exact List.mem_toFinset.mpr ((mem_subm E _).mpr
      ⟨List.filter_sublist, matchQ_Mσ G hG henum (Finset.mem_filter.mp hσ).2⟩)
  · intro M hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      toPerm_edgeSupported G henum (List.mem_toFinset.mp hM)⟩
  · intro σ hσ
    exact toPerm_filter G hG henum (Finset.mem_filter.mp hσ).2
  · intro M hM
    exact filter_toPerm G henum (List.mem_toFinset.mp hM)
  · intro σ hσ
    have hES := (Finset.mem_filter.mp hσ).2
    have hmem : E.filter (fun e => decide (σ e.1 = e.2.1)) ∈ subm E :=
      (mem_subm E _).mpr ⟨List.filter_sublist, matchQ_Mσ G hG henum hES⟩
    have hw := prod_weights G henum hmem
    rwa [toPerm_filter G hG henum hES] at hw

open scoped Classical in
/-- **STEP 3d (main): `pi(T) = per L / prod deg` IS the weighted matching sum `msum E`.**
    Composes H2a (`pi_eq_weighted_matching_sum`) with the bijection above.  The SimpleGraph
    amplitude now lives in the same `msum` language as the `Branch`/`RTree` side. -/
theorem pi_eq_msum (hG : G.IsAcyclic) (hpos : ∀ v, (G.degree v : ℝ) ≠ 0)
    {E : List (V × V × ℝ)} (henum : IsEdgeEnum G E) :
    (lapl G).permanent / (∏ v, (G.degree v : ℝ)) = msum E := by
  rw [pi_eq_weighted_matching_sum G hG hpos]
  exact sum_involutions_eq_msum G hG henum

end Step3
end R3Cert
