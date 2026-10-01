/-
LeanCherry.Lambda1 -- at lambda = 1 the matching sum is the normalized Laplacian permanent.
  pi_one_eq_permanent : G acyclic, all degrees nonzero  ->  piL 1 G = per(L G) / prod_v deg v
  pi_one_eq_permanent_tree : G a tree with |V| >= 2      ->  same
via the bijection between edge-supported involutions sigma and matchings M (M = {s(v, sigma v) : sigma v != v}),
using the copied Arda identity R3Copy.pi_eq_weighted_matching_sum.
-/
import LeanCherry.TreeBridge
import LeanCherry.R3Copy

open Finset Equiv

namespace LeanCherry

universe u

noncomputable section

namespace Lam1

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- non-fixed points -/
def NF (σ : Perm V) : Finset V := univ.filter (fun v => σ v ≠ v)

/-- the edges of an involution -/
def edgesOf (σ : Perm V) : Finset (Sym2 V) := (NF σ).image (fun v => s(v, σ v))

/-- partner of v in a matching M (v itself if unmatched) -/
def pm (M : Finset (Sym2 V)) (v : V) : V := by
  classical
  exact if h : ∃ e ∈ M, v ∈ e then Sym2.Mem.other h.choose_spec.2 else v

variable {G}

lemma uniq {M : Finset (Sym2 V)} (hM : IsGMg M) {v : V} {e e' : Sym2 V} (he : e ∈ M) (he' : e' ∈ M)
    (hv : v ∈ e) (hv' : v ∈ e') : e = e' := by
  by_contra h; exact hM e he e' he' h v hv hv'

lemma pm_spec {M : Finset (Sym2 V)} (hM : IsGMg M) {v : V} {e : Sym2 V} (he : e ∈ M) (hv : v ∈ e) :
    s(v, pm M v) = e := by
  classical
  have h : ∃ e ∈ M, v ∈ e := ⟨e, he, hv⟩
  unfold pm
  rw [dif_pos h, Sym2.other_spec]
  exact uniq hM h.choose_spec.1 he h.choose_spec.2 hv

lemma pm_unmatched {M : Finset (Sym2 V)} {v : V} (h : ¬ ∃ e ∈ M, v ∈ e) : pm M v = v := by
  classical
  unfold pm; rw [dif_neg h]

lemma pm_invol {M : Finset (Sym2 V)} (hM : IsGMg M) : Function.Involutive (pm M) := by
  intro v
  by_cases h : ∃ e ∈ M, v ∈ e
  · obtain ⟨e, he, hv⟩ := h
    have h1 := pm_spec hM he hv
    have hw : pm M v ∈ e := by rw [← h1]; exact Sym2.mem_mk_right _ _
    have h2 := pm_spec hM he hw
    rw [← h1] at h2
    rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨_, h4⟩
    · rw [h4, h3]
    · exact h4
  · rw [pm_unmatched h, pm_unmatched h]

/-- the involution of a matching -/
def sigOf {M : Finset (Sym2 V)} (hM : IsGMg M) : Perm V := Function.Involutive.toPerm _ (pm_invol hM)

lemma sigOf_apply {M : Finset (Sym2 V)} (hM : IsGMg M) (v : V) : sigOf hM v = pm M v := rfl

lemma not_diag_of_edge {e : Sym2 V} (he : e ∈ G.edgeFinset) {a b : V} (h : e = s(a, b)) : a ≠ b := by
  rw [h, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he; exact he.ne

lemma edgeSupported_sigOf {M : Finset (Sym2 V)} (hM : IsGMg M) (hsub : M ⊆ G.edgeFinset) :
    R3Copy.EdgeSupported G (sigOf hM) := by
  intro v
  rw [sigOf_apply]
  by_cases h : ∃ e ∈ M, v ∈ e
  · obtain ⟨e, he, hv⟩ := h
    right
    have h1 := pm_spec hM he hv
    have := hsub he
    rw [← h1, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    exact this
  · left; exact pm_unmatched h

lemma edgesOf_sigOf {M : Finset (Sym2 V)} (hM : IsGMg M) (hsub : M ⊆ G.edgeFinset) :
    edgesOf (sigOf hM) = M := by
  ext e
  simp only [edgesOf, NF, mem_image, mem_filter, mem_univ, true_and, sigOf_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    by_cases h : ∃ e ∈ M, v ∈ e
    · obtain ⟨e', he', hv'⟩ := h
      rw [pm_spec hM he' hv']; exact he'
    · exact absurd (pm_unmatched h) hv
  · intro he
    induction e using Sym2.ind with
    | h a b =>
      have hab := not_diag_of_edge (hsub he) rfl
      have h1 := pm_spec hM he (Sym2.mem_mk_left a b)
      have h2 : pm M a = b := Sym2.congr_right.mp h1
      exact ⟨a, by rw [h2]; exact hab.symm, by rw [h2]⟩

lemma edgesOf_sub {σ : Perm V} (hE : R3Copy.EdgeSupported G σ) : edgesOf σ ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := mem_image.mp he
  rw [NF, mem_filter] at hv
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (hE v).resolve_left hv.2

lemma edgesOf_isGM {σ : Perm V} (hinv : Function.Involutive σ) : IsGMg (edgesOf σ) := by
  intro e he f hf hef x hxe hxf
  obtain ⟨a, _, rfl⟩ := mem_image.mp he
  obtain ⟨b, _, rfl⟩ := mem_image.mp hf
  apply hef
  rw [Sym2.mem_iff] at hxe hxf
  have key : a = b ∨ a = σ b := by
    rcases hxe with h1 | h1 <;> rcases hxf with h2 | h2
    · exact Or.inl (h1.symm.trans h2)
    · exact Or.inr (h1.symm.trans h2)
    · have h3 : σ a = b := h1.symm.trans h2
      exact Or.inr (by rw [← h3, hinv a])
    · exact Or.inl (σ.injective (h1.symm.trans h2))
  rcases key with h | h
  · rw [h]
  · rw [h, hinv b, Sym2.eq_swap]

lemma sigOf_edgesOf {σ : Perm V} (hinv : Function.Involutive σ) :
    sigOf (edgesOf_isGM hinv) = σ := by
  ext v
  rw [sigOf_apply]
  have hM := edgesOf_isGM hinv
  by_cases hv : σ v ≠ v
  · have he : s(v, σ v) ∈ edgesOf σ := mem_image.mpr ⟨v, by simp [NF, hv], rfl⟩
    exact Sym2.congr_right.mp (pm_spec hM he (Sym2.mem_mk_left _ _))
  · push Not at hv
    rw [hv]
    apply pm_unmatched
    rintro ⟨e, he, hve⟩
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    rw [NF, mem_filter] at hw
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · exact hw.2 hv
    · rw [hinv w] at hv; exact hw.2 hv.symm

/-- the product over vertices regroups into the product over the matched edges -/
lemma prod_regroup {σ : Perm V} (hinv : Function.Involutive σ) (δ : V → ℝ) :
    ∏ v, (if σ v = v then (1 : ℝ) else 1 / δ v) = ∏ e ∈ edgesOf σ, wS δ 1 e := by
  rw [← prod_filter_mul_prod_filter_not univ (fun v => σ v = v)]
  rw [prod_congr rfl (fun v hv => if_pos (mem_filter.mp hv).2), prod_const_one, one_mul,
    prod_congr rfl (fun v hv => if_neg (mem_filter.mp hv).2)]
  unfold edgesOf
  symm
  apply prod_image'
  intro c hc
  have hc' : σ c ≠ c := (mem_filter.mp hc).2
  have hfib : (NF σ).filter (fun x => s(x, σ x) = s(c, σ c)) = {c, σ c} := by
    ext x
    simp only [mem_filter, NF, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · left; exact h1
      · right; exact h1
    · rintro (rfl | rfl)
      · exact ⟨hc', rfl⟩
      · refine ⟨by rw [hinv c]; exact fun h => hc' h.symm, ?_⟩
        rw [hinv c, Sym2.eq_swap]
  rw [hfib, prod_pair (fun h => hc' h.symm), wS_mk, one_div_mul_one_div]

end Lam1

open Lam1 in
/-- at lambda = 1, the matching sum of an acyclic graph with nonzero degrees is per(L)/prod deg -/
theorem pi_one_eq_permanent {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (hpos : ∀ v, (G.degree v : ℝ) ≠ 0) :
    piL 1 G = (R3Copy.lapl G).permanent / ∏ v, (G.degree v : ℝ) := by
  classical
  rw [R3Copy.pi_eq_weighted_matching_sum G hG hpos]
  unfold piL MS
  rw [← sum_filter]
  symm
  refine sum_bij' (fun σ _ => edgesOf σ) (fun M hM => sigOf (mem_filter.mp hM).2) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    have hE := (mem_filter.mp hσ).2
    have hinv := R3Copy.acyclic_edgeSupported_involutive hG hE
    exact mem_filter.mpr ⟨mem_powerset.mpr (edgesOf_sub hE), edgesOf_isGM hinv⟩
  · intro M hM
    exact mem_filter.mpr ⟨mem_univ _, edgeSupported_sigOf _ (mem_powerset.mp (mem_filter.mp hM).1)⟩
  · intro σ hσ
    have hinv := R3Copy.acyclic_edgeSupported_involutive hG (mem_filter.mp hσ).2
    exact sigOf_edgesOf hinv
  · intro M hM
    exact edgesOf_sigOf _ (mem_powerset.mp (mem_filter.mp hM).1)
  · intro σ hσ
    exact prod_regroup (R3Copy.acyclic_edgeSupported_involutive hG (mem_filter.mp hσ).2) _

/-- the lambda = 1 link for trees: every tree on at least two vertices has all degrees positive -/
theorem pi_one_eq_permanent_tree {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (h2 : 2 ≤ Fintype.card V) :
    piL 1 G = (R3Copy.lapl G).permanent / ∏ v, (G.degree v : ℝ) := by
  apply pi_one_eq_permanent G hG.isAcyclic
  intro v
  have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := hG.connected.preconnected v w
  have hdeg : 0 < G.degree v := by
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact h.degree_pos_left
  exact_mod_cast hdeg.ne'

end

end LeanCherry
