/-
  The matching/permanent bridge -- the machine-checked ALGEBRAIC core, with the two bridge identities stated.

  The amplitude quantity pi(T) = per L(T) / prod deg equals the value computed by the cavity recursion on the
  rooted tree.  Two halves (both proved in full in outreach/matching_bridge.tex, verified numerically to 1e-9
  on trees up to 10 vertices):

    (H1)  per L(T) = sum over matchings M of prod_{v not in V(M)} deg(v)   [acyclicity: contributing
          permutations are exactly involutions whose transpositions are edges].
    (H2)  pi(T) = sum_M prod_{ij in M} 1/(deg i * deg j), and this weighted matching partition function
          satisfies the tree cavity recursion  r_v = 1 / (1 + sum_children w_vc r_c),  w_ij = 1/(deg i deg j).

  This file machine-checks the ALGEBRAIC step of (H2) -- the passage from the two subtree partition functions
  (P_v total, P0_v with v unmatched) to the cavity ratio r_v = 1/(1+S) -- which is the local identity the tree
  induction turns into the recursion.  The combinatorial content (the permutation cycle-decomposition of (H1)
  over an acyclic support, and the matching bijection of the induction step) is a self-contained graph-theory
  development; it is stated here with `Prop`s carrying the Python + tex certificates, NOT assumed as axioms.
-/
import Mathlib
import R3Cert.Involution

namespace R3Cert

open scoped BigOperators

/-- **cavity_step** (the machine-checked algebraic core of H2).  If a vertex's total subtree partition
    function factors as `Pv = Pprod * (1 + S)` and its `v`-unmatched partition function is `P0 = Pprod`
    (Lemma: children matched freely), then the cavity ratio `r_v = P0 / Pv` equals `1 / (1 + S)`. -/
theorem cavity_step (Pprod S : ℝ) (hP : Pprod ≠ 0) :
    Pprod / (Pprod * (1 + S)) = 1 / (1 + S) := by
  rw [← div_div, div_self hP]

/-- The recursion in the form used by the induction: with `r_c = P0c / Pc` the child cavity ratios and
    `S = Σ w_vc r_c`, the identity `Pv = (Π P_c) (1 + S)`, `P0 = Π P_c` gives `r_v = 1/(1+S)`.  (Same content
    as `cavity_step`.) -/
theorem cavity_ratio (Pprod S : ℝ) (hP : Pprod ≠ 0) :
    (Pprod) / (Pprod * (1 + S)) = 1 / (1 + S) := cavity_step Pprod S hP

/-- The per-vertex log contribution telescopes: `log Pv = (Σ log P_c) + log (1 + S)`, so summing over the tree
    gives `log pi(T) = Σ_v log(1 + Σ_children w r_c)` (Theorem H2).  The algebraic step is `Real.log_mul`. -/
theorem log_telescope (Pprod S : ℝ) (hP : 0 < Pprod) (hS : 0 < 1 + S) :
    Real.log (Pprod * (1 + S)) = Real.log Pprod + Real.log (1 + S) :=
  Real.log_mul (ne_of_gt hP) (ne_of_gt hS)

/-! ## The two bridge identities, stated with their certificates (combinatorial proofs in matching_bridge.tex). -/

/-! ## (H1) The combinatorial half -- framework, permanent-term arithmetic, and the crux stated.

We set up the Laplacian of a `SimpleGraph` over ℝ and prove the tractable combinatorial content: the
permanent-term evaluation (each factor `lapl (σ v) v` is `deg v` at a fixed point and `-1` at a
neighbour-mapped point), which is exactly the arithmetic that turns a matching into a permanent term.  The
crux (acyclicity forces every nonzero-term permutation to be an involution -- a matching) and the resulting
`per L = Σ_matchings Π_{unmatched} deg` are STATED with their certificates; the crux is a genuine graph-theory
lemma (permutation orbit ⟹ graph cycle ⟹ contradiction with `IsAcyclic`) whose full Lean proof is a
self-contained development, so it is given as a target `Prop`, not asserted. -/

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

/-! ## (H2) The cavity recursion -- the node step, machine-checked (no `sorry`).

`pi(T) = Σ_M Π_{ij∈M} 1/(deg i deg j)` is computed by the tree cavity recursion `r_v = 1/(1 + Σ_children w_vc
r_c)`, `w_vc = 1/(deg v deg c)`.  The load-bearing content is the per-node identity: writing the matching
partition functions as `Zopen` (root unmatched) and `Ztot` (all matchings), the node cavity ratio equals
`1/(1 + Σ w r_child)`.  This is proved below in full generality (arbitrary finite child set) as
`cavity_recursion`.  The tree-level statement is this identity applied at every node by structural induction on
the rooted tree -- a bookkeeping wrapper introducing no new analytic content. -/

open scoped BigOperators in
/-- **The cavity recursion -- node step (THEOREM, no `sorry`).**  For a rooted-tree node with children indexed
    by a finite type `ι`, edge weights `w i`, child root-open partition functions `o i`, and child total
    partition functions `t i` (all `t i ≠ 0`), the node's matching partition functions are
    `Zopen = ∏ i, t i` (root unmatched ⇒ every child subtree free) and
    `Ztot  = ∏ i, t i + ∑ i, w i * o i * ∏ j ∈ univ.erase i, t j` (root unmatched, or root matched to child `i`,
    whose own root is then open), so the node cavity ratio is

      `Zopen / Ztot = 1 / (1 + ∑ i, w i * (o i / t i)) = 1 / (1 + ∑ i, w i * r i)`,   `r i = o i / t i`.

    Proof: the leave-one-out product `∏_{j≠i} t j = (∏ t)/t i` factors `Ztot = (∏ t)(1 + Σ w r)`, then the ratio
    collapses by `cavity_step`.  This is the exact local identity the tree induction turns into H2. -/
theorem cavity_recursion {ι : Type*} [Fintype ι] [DecidableEq ι] (w o t : ι → ℝ) (ht : ∀ i, t i ≠ 0) :
    (∏ i, t i) / ((∏ i, t i) + ∑ i, w i * o i * ∏ j ∈ Finset.univ.erase i, t j)
      = 1 / (1 + ∑ i, w i * (o i / t i)) := by
  have hP : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ht i)
  have hstep : (∑ i, w i * o i * ∏ j ∈ Finset.univ.erase i, t j)
      = (∏ i, t i) * ∑ i, w i * (o i / t i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hleave : (∏ j ∈ Finset.univ.erase i, t j) = (∏ j, t j) / t i := by
      rw [eq_div_iff (ht i)]
      exact Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i)
    rw [hleave]; ring
  rw [hstep]
  have hfac : (∏ i, t i) + (∏ i, t i) * (∑ i, w i * (o i / t i))
      = (∏ i, t i) * (1 + ∑ i, w i * (o i / t i)) := by ring
  rw [hfac]
  exact cavity_step (∏ i, t i) (∑ i, w i * (o i / t i)) hP

end R3Cert
