/-
LeanCherry.R3Copy -- VERBATIM COPY (provenance) of the lambda = 1 permanent/matching development from the Arda repository:
  proof/formalization/R3Cert/Involution.lean  (whole file)  and
  proof/formalization/R3Cert/Matching.lean    (section Combinatorial),
  DrMurphyIsIn/Arda, last commit touching them 3c26d4619d123a5aa06fa322dd15fd72c5f7e4cc (2026-08-15).
Copied read-only on 2026-10-01 into this project; the only change is the namespace (R3Cert -> LeanCherry.R3Copy)
and the removal of the Matching.lean import of R3Cert.Involution.  Not re-proved; recompiled here by the Lean kernel.
-/
import Mathlib

namespace LeanCherry.R3Copy

open Equiv Function SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (σ : Perm V) (x : V)

/-- Walk along the forward σ-orbit of `x`, of length `len` (built by `concat`, base fixed at `x`). -/
def owalk (hb : ∀ n : ℕ, G.Adj (σ^[n] x) (σ (σ^[n] x))) : (len : ℕ) → G.Walk x (σ^[len] x)
  | 0 => Walk.nil
  | len + 1 => (owalk hb len).concat (by rw [Function.iterate_succ_apply']; exact hb len)

lemma owalk_length (hb : ∀ n : ℕ, G.Adj (σ^[n] x) (σ (σ^[n] x))) (len : ℕ) :
    (owalk G σ x hb len).length = len := by
  induction len with
  | zero => rfl
  | succ n ih => rw [owalk, Walk.length_concat, ih]

lemma owalk_support (hb : ∀ n : ℕ, G.Adj (σ^[n] x) (σ (σ^[n] x))) (len : ℕ) :
    (owalk G σ x hb len).support = (List.range (len + 1)).map (fun i => σ^[i] x) := by
  induction len with
  | zero => simp [owalk]
  | succ n ih =>
    have hr : (List.range (n + 1 + 1)).map (fun i => σ^[i] x)
        = (List.range (n + 1)).map (fun i => σ^[i] x) ++ [σ^[n + 1] x] := by
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [owalk, Walk.support_concat, ih, hr]

end LeanCherry.R3Copy

namespace LeanCherry.R3Copy
open Equiv Function SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- σ maps non-fixed points to non-fixed points, so every step along the orbit of a non-fixed point is an
    edge (via edge-support). -/
lemma orbit_nonfixed {σ : Perm V} {x : V} (hx : σ x ≠ x) (n : ℕ) : σ (σ^[n] x) ≠ σ^[n] x := by
  intro hfix
  apply hx
  have h1 : σ^[n] (σ x) = σ^[n] x := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hfix]
  exact (σ.injective.iterate n) h1

/-- **The crux.** On an acyclic graph, an edge-supported permutation is an involution. -/
theorem acyclic_edgeSupported_involutive {G : SimpleGraph V} {σ : Perm V}
    (hG : G.IsAcyclic) (hE : ∀ v, σ v = v ∨ G.Adj v (σ v)) : Function.Involutive σ := by
  intro x
  by_contra hxx
  have hx : σ x ≠ x := by intro h; apply hxx; rw [h, h]
  have hσx : σ (σ x) ≠ σ x := fun h => hx (σ.injective h)
  have hstep : ∀ v : V, σ v ≠ v → G.Adj v (σ v) := fun v hv => (hE v).resolve_left hv
  have hb0 : G.Adj x (σ x) := hstep x hx
  have hbσ : ∀ n : ℕ, G.Adj (σ^[n] (σ x)) (σ (σ^[n] (σ x))) := fun n => hstep _ (orbit_nonfixed hσx n)
  have hxper : x ∈ Function.periodicPts σ := σ.injective.mem_periodicPts x
  set p := Function.minimalPeriod σ x with hp
  have hp0 : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hxper
  have hend : σ^[p] x = x := Function.iterate_minimalPeriod
  have hp1 : p ≠ 1 := by
    intro h
    have h2 : σ^[1] x = x := h ▸ hend
    rw [Function.iterate_one] at h2; exact hx h2
  have hp2 : p ≠ 2 := by
    intro h
    have h2 : σ^[2] x = x := h ▸ hend
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply] at h2
    simp only [Function.iterate_one] at h2; exact hxx h2
  have hp3 : 3 ≤ p := by omega
  have hend' : σ^[p - 1] (σ x) = x := by
    have h1 : σ^[p - 1] (σ x) = σ^[p] x := by
      rw [← Function.iterate_succ_apply]; congr 1; omega
    rw [h1, hend]
  -- copy preserves IsPath (support is unchanged)
  have hcopy : ∀ {a b a' b' : V} (w : G.Walk a b) (hu : a = a') (hv : b = b'),
      w.IsPath → (w.copy hu hv).IsPath := by
    intro a b a' b' w hu hv hw
    rw [SimpleGraph.Walk.isPath_def, Walk.support_copy]
    rwa [SimpleGraph.Walk.isPath_def] at hw
  -- tail walk σx → x of length p-1, and the closed walk W : x → x of length p
  let tail : G.Walk (σ x) x := (owalk G σ (σ x) hbσ (p - 1)).copy rfl hend'
  let W : G.Walk x x := Walk.cons hb0 tail
  refine hG W ?_
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, ?_⟩
  · have hper : Function.minimalPeriod σ (σ x) = p := Function.minimalPeriod_apply hxper
    have hinj : Set.InjOn (fun i => σ^[i] (σ x)) (Set.Iio p) := by
      rw [← hper]; exact Function.iterate_injOn_Iio_minimalPeriod
    have htp : tail.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      have hsupp : tail.support = (List.range p).map (fun i => σ^[i] (σ x)) := by
        show ((owalk G σ (σ x) hbσ (p - 1)).copy rfl hend').support = _
        rw [Walk.support_copy, owalk_support, Nat.sub_add_cancel hp0]
      rw [hsupp]
      exact List.Nodup.map_on
        (fun i hi j hj hij => hinj (Set.mem_Iio.mpr (List.mem_range.mp hi))
          (Set.mem_Iio.mpr (List.mem_range.mp hj)) hij)
        List.nodup_range
    show (Walk.cons hb0 tail).tail.IsPath
    rw [Walk.tail_cons hb0 tail]
    exact hcopy tail _ _ htp
  · show 3 ≤ W.length
    have htl : tail.length = p - 1 := by
      show ((owalk G σ (σ x) hbσ (p - 1)).copy rfl hend').length = p - 1
      rw [Walk.length_copy, owalk_length]
    have hW : W.length = p := by
      show (Walk.cons hb0 tail).length = p
      rw [Walk.length_cons, htl]; omega
    omega

end LeanCherry.R3Copy

namespace LeanCherry.R3Copy

open scoped BigOperators

section Combinatorial
open Equiv Function
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Laplacian matrix over ℝ: diagonal `deg`, `-1` on edges, `0` elsewhere. -/
noncomputable def lapl : Matrix V V ℝ :=
  fun i j => if i = j then (G.degree i : ℝ) else if G.Adj i j then -1 else 0

@[simp] lemma lapl_diag (i : V) : lapl G i i = (G.degree i : ℝ) := by simp [lapl]

lemma lapl_adj {i j : V} (h : G.Adj i j) : lapl G i j = -1 := by
  have hij : i ≠ j := h.ne
  simp [lapl, hij, h]

/-- `σ` maps every vertex to itself or to a neighbour -- the support condition on a nonzero permanent term. -/
def EdgeSupported (σ : Perm V) : Prop := ∀ v, σ v = v ∨ G.Adj v (σ v)

/-- A nonzero permanent term forces `EdgeSupported`: if some factor `lapl (σ v) v ≠ 0` for all `v`, then each
    `v` is fixed or a neighbour of its image (the entries are `0` off the diagonal and non-edges). -/
lemma edgeSupported_of_term_ne_zero {σ : Perm V} (h : ∀ v, lapl G (σ v) v ≠ 0) : EdgeSupported G σ := by
  intro v
  rcases eq_or_ne (σ v) v with hv | hv
  · exact Or.inl hv
  · refine Or.inr ?_
    by_contra hadj
    apply h v
    unfold lapl
    rw [if_neg hv, if_neg (fun h' => hadj (G.adj_symm h'))]

omit [Fintype V] [DecidableEq V] in
/-- `σ` maps non-fixed points to non-fixed points (injectivity). -/
lemma nonfixed_image {σ : Perm V} {v : V} (h : σ v ≠ v) : σ (σ v) ≠ σ v :=
  fun he => h (σ.injective he)

/-- Permanent-term factor at a NON-fixed vertex of an edge-supported `σ` is `-1` (the transposition weight). -/
lemma term_factor_nonfixed {σ : Perm V} (hE : EdgeSupported G σ) {v : V} (h : σ v ≠ v) :
    lapl G (σ v) v = -1 :=
  lapl_adj G ((hE v).resolve_left h).symm

/-- Permanent-term factor at a FIXED vertex is `deg v`. -/
lemma term_factor_fixed {σ : Perm V} {v : V} (h : σ v = v) : lapl G (σ v) v = (G.degree v : ℝ) := by
  rw [h]; exact lapl_diag G v

/-- **The crux -- now a THEOREM** (`R3Cert.acyclic_edgeSupported_involutive`, Involution.lean).  If `G` is
    acyclic and `σ` is edge-supported, then `σ` is an involution -- its 2-cycles form a matching and there are
    no longer cycles.  Proof: a non-involution has a `σ`-orbit of length `≥ 3`; iterating `σ` along it builds a
    `SimpleGraph.Walk` that is a cycle (`isCycle_iff_isPath_tail_and_le_length`, with orbit-vertex
    distinctness from `Function.iterate_injOn_Iio_minimalPeriod`), contradicting `IsAcyclic`.  Machine-checked,
    no `sorry`. -/
def AcyclicForcesInvolution : Prop :=
  ∀ (σ : Perm V), G.IsAcyclic → EdgeSupported G σ → Function.Involutive σ

/-- The crux holds (discharged by Involution.lean), so it is no longer an assumption. -/
theorem acyclicForcesInvolution : AcyclicForcesInvolution G :=
  fun σ hG hE => acyclic_edgeSupported_involutive hG hE

open scoped Classical in
/-- **The reindexing step of H1** (machine-checked): the permanent is the sum of its terms over only the
    edge-supported permutations -- every other permutation has a zero factor (an off-diagonal non-edge entry)
    and contributes `0`.  On an acyclic graph the edge-supported permutations are exactly the involutions whose
    2-cycles are edges (the crux), i.e.\ the matchings; so this is `per L = Σ over matchings (of the term)`. -/
theorem permanent_eq_sum_edgeSupported :
    (lapl G).permanent
      = ∑ σ ∈ Finset.univ.filter (fun σ : Perm V => EdgeSupported G σ), ∏ v, lapl G (σ v) v := by
  rw [Matrix.permanent]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro σ _ hσ
  have hnotES : ¬ EdgeSupported G σ := fun hES =>
    hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hES⟩)
  by_contra hprod
  exact hnotES (edgeSupported_of_term_ne_zero G
    (fun v hv => hprod (Finset.prod_eq_zero (Finset.mem_univ v) hv)))

open scoped Classical in
/-- **Per-term evaluation** (machine-checked): for an edge-supported INVOLUTION `σ`, the permanent term is the
    product of degrees over the FIXED points -- the `-1`s at the non-fixed points pair off (`v` with `σ v`,
    each contributing `(-1)(-1)=1`) via `Finset.prod_involution`.  For a matching `M` (= such a `σ`) the fixed
    points are exactly the unmatched vertices, so this is `Π_{v ∉ V(M)} deg v`. -/
theorem term_eval {σ : Perm V} (hE : EdgeSupported G σ) (hinv : Function.Involutive σ) :
    ∏ v, lapl G (σ v) v = ∏ v ∈ Finset.univ.filter (fun v => σ v = v), (G.degree v : ℝ) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => σ v = v)]
  have hnf : (∏ v ∈ Finset.univ.filter (fun v => ¬ σ v = v), lapl G (σ v) v) = 1 := by
    refine Finset.prod_involution (fun a _ => σ a) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha
      have h1 : lapl G (σ a) a = -1 := term_factor_nonfixed G hE ha.2
      have h2 : lapl G (σ (σ a)) (σ a) = -1 := by
        rw [hinv a]; exact lapl_adj G ((hE a).resolve_left ha.2)
      rw [h1, h2]; norm_num
    · intro a ha _
      rw [Finset.mem_filter] at ha; exact ha.2
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hinv a]; exact fun h => ha.2 h.symm
    · intro a _; exact hinv a
  rw [hnf, mul_one]
  refine Finset.prod_congr rfl (fun v hv => ?_)
  rw [Finset.mem_filter] at hv
  exact term_factor_fixed G hv.2

open scoped Classical in
/-- **(H1) permanent = matching sum -- THEOREM (no `sorry`).**  For an acyclic `G`, the permanent of the
    Laplacian is the sum, over the edge-supported involutions `σ` of `G`, of the product of degrees over the
    fixed points of `σ`.  Each such `σ` is exactly a matching `M` of `G` (its 2-cycles are the matched edges,
    `edgeSupported` makes them edges, `Involutive` makes them disjoint transpositions), and its fixed points are
    exactly the unmatched vertices, so this is literally `per L(T) = Σ_M Π_{v ∉ V(M)} deg v`.

    Assembles the three proved halves: `permanent_eq_sum_edgeSupported` (only edge-supported terms survive) +
    `acyclicForcesInvolution` (on an acyclic graph every edge-supported permutation is an involution -- the
    crux) + `term_eval` (the `-1`s at the non-fixed points pair off to `+1`, leaving the fixed-point degrees). -/
theorem permanent_eq_matching_sum (hG : G.IsAcyclic) :
    (lapl G).permanent
      = ∑ σ ∈ Finset.univ.filter (fun σ : Perm V => EdgeSupported G σ),
          ∏ v ∈ Finset.univ.filter (fun v => σ v = v), (G.degree v : ℝ) := by
  rw [permanent_eq_sum_edgeSupported G]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  exact term_eval G hσ.2 (acyclicForcesInvolution G σ hG hσ.2)

open scoped Classical in
/-- **(H1) as a `Prop`** -- now genuinely the matching-sum identity (was the mislabeled crux `Prop`), proved by
    `permanent_eq_matching_sum`. -/
def permanent_is_matching_sum : Prop :=
  G.IsAcyclic →
    (lapl G).permanent
      = ∑ σ ∈ Finset.univ.filter (fun σ : Perm V => EdgeSupported G σ),
          ∏ v ∈ Finset.univ.filter (fun v => σ v = v), (G.degree v : ℝ)

/-- H1 holds (discharged), so it is a theorem, not an assumption. -/
theorem permanent_is_matching_sum_holds : permanent_is_matching_sum G :=
  fun hG => permanent_eq_matching_sum G hG

open scoped Classical in
/-- **(H2a) π = weighted matching sum -- THEOREM (no `sorry`).**  Dividing H1 by `∏ deg`, the normalized
    amplitude `π(T) = per L(T) / ∏_v deg v` equals the sum, over the same matchings `σ`, of the per-vertex
    product `∏_v (1 if v fixed else 1/deg v)`.  Grouping the non-fixed vertices into the 2-cycles (edges) of
    the matching, each matched edge `{v, σv}` contributes `(1/deg v)(1/deg σv) = 1/(deg v · deg σv)`, so this is
    exactly `Σ_M ∏_{ij ∈ M} 1/(deg i · deg j)` -- the weighted matching partition function.  Needs every degree
    nonzero (true for any tree on `≥ 2` vertices). -/
theorem pi_eq_weighted_matching_sum (hG : G.IsAcyclic) (hpos : ∀ v, (G.degree v : ℝ) ≠ 0) :
    (lapl G).permanent / (∏ v, (G.degree v : ℝ))
      = ∑ σ ∈ Finset.univ.filter (fun σ : Perm V => EdgeSupported G σ),
          ∏ v, (if σ v = v then (1 : ℝ) else 1 / (G.degree v : ℝ)) := by
  rw [permanent_eq_matching_sum G hG, Finset.sum_div]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_filter, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases h : σ v = v
  · rw [if_pos h, if_pos h, div_self (hpos v)]
  · rw [if_neg h, if_neg h]

end Combinatorial

end LeanCherry.R3Copy
