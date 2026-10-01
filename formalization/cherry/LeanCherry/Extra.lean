/-
LeanCherry.Extra -- two supplementary facts:
  * gE_antitone_two: g_b(l) = log Tl l b - (|b|/2) log(2+l) is antitone on [2, inf) (the monotonicity in lambda, non-strict part);
  * permutation invariance of the cavity recursion (children are an ordered list in Br, but Tl, msgl only see the multiset).
-/
import LeanCherry.ThmE

open Real

namespace LeanCherry

namespace Br

noncomputable section

/-- monotonicity in lambda (non-strict): g_b is antitone on [2, inf) -/
theorem gE_antitone_two (b : Br) : AntitoneOn (gE b) (Set.Ici 2) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
  · intro x hx
    exact (hasDeriv_gE (by linarith [Set.mem_Ici.mp hx]) b).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hasDeriv_gE (by linarith [Set.mem_Ioi.mp hx]) b).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact gE_deriv_nonpos (le_of_lt hx) b

lemma sumYl_eq_map (l : ℝ) : ∀ cs : List Br, sumYl l cs = (cs.map (msgl l)).sum
  | [] => by simp [sumYl]
  | c :: cs => by simp only [sumYl, List.map_cons, List.sum_cons]; rw [sumYl_eq_map l cs]

lemma prodTl_eq_map (l : ℝ) : ∀ cs : List Br, prodTl l cs = (cs.map (Tl l)).prod
  | [] => by simp [prodTl]
  | c :: cs => by simp only [prodTl, List.map_cons, List.prod_cons]; rw [prodTl_eq_map l cs]

/-- reordering the children of a node does not change its message -/
theorem msgl_perm (l : ℝ) {cs cs' : List Br} (h : cs.Perm cs') :
    msgl l (.node cs) = msgl l (.node cs') := by
  rw [msgl_node, msgl_node, sumYl_eq_map, sumYl_eq_map, (h.map (msgl l)).sum_eq, h.length_eq]

/-- reordering the children of a node does not change T -/
theorem Tl_perm (l : ℝ) {cs cs' : List Br} (h : cs.Perm cs') :
    Tl l (.node cs) = Tl l (.node cs') := by
  rw [Tl_node, Tl_node, sumYl_eq_map, sumYl_eq_map, prodTl_eq_map, prodTl_eq_map,
    (h.map (msgl l)).sum_eq, (h.map (Tl l)).prod_eq, h.length_eq]

/-- "same rooted tree up to reordering children at every vertex" -/
inductive Equiv : Br → Br → Prop
  | node {cs cs' ds : List Br} : List.Forall₂ Equiv cs ds → ds.Perm cs' → Equiv (.node cs) (.node cs')

mutual
lemma Equiv.msgl_Tl {l : ℝ} : ∀ {b b' : Br}, Equiv b b' → msgl l b = msgl l b' ∧ Tl l b = Tl l b'
  | .node cs, .node cs', .node (ds := ds) hF hP => by
      obtain ⟨hy, ht⟩ := forall2_msgl_Tl hF
      have hlen := hF.length_eq
      refine ⟨?_, ?_⟩
      · rw [← msgl_perm l hP, msgl_node, msgl_node, hy, hlen]
      · rw [← Tl_perm l hP, Tl_node, Tl_node, hy, ht, hlen]
lemma forall2_msgl_Tl {l : ℝ} : ∀ {cs ds : List Br}, List.Forall₂ Equiv cs ds →
    sumYl l cs = sumYl l ds ∧ prodTl l cs = prodTl l ds
  | [], [], .nil => by simp [sumYl, prodTl]
  | _ :: _, _ :: _, .cons h hF => by
      obtain ⟨h1, h2⟩ := Equiv.msgl_Tl (l := l) h
      obtain ⟨h3, h4⟩ := forall2_msgl_Tl (l := l) hF
      simp only [sumYl, prodTl]; rw [h1, h2, h3, h4]; exact ⟨rfl, rfl⟩
end

/-- T is an invariant of the unordered rooted tree -/
theorem Tl_equiv (l : ℝ) {b b' : Br} (h : Equiv b b') : Tl l b = Tl l b' := (Equiv.msgl_Tl h).2

end

end Br

end LeanCherry
