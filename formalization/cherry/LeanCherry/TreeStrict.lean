/-
LeanCherry.TreeStrict -- the oneblock bound is strict for every finite tree (every n >= 1, every l >= 1 + sqrt 5).
  Root step: ZTl = prod T_c * (1 + l R/k), R/k <= 1 with equality iff every child of the root is a leaf (the star, where
  prod T_c = 1 and the bound has the extra factor (1 + l/2)^((n-1)/2) > 1); n = 1: 1 < 1 + l.
-/
import LeanCherry.Strict

open Real

namespace LeanCherry

namespace Br

noncomputable section

lemma msgl_lt_one {l : ℝ} (hl : 0 ≤ l) (c : Br) (hc : c ≠ .node []) : msgl l c < 1 := by
  cases c with
  | node ds =>
    cases ds with
    | nil => exact absurd rfl hc
    | cons d ds =>
      rw [msgl_node]
      have := sumYl_nonneg hl (d :: ds)
      rw [div_lt_one (by positivity)]
      have : (1:ℝ) ≤ ((d :: ds).length : ℝ) := by simp
      nlinarith [mul_nonneg hl (sumYl_nonneg hl (d :: ds))]

lemma sumYl_lt_length {l : ℝ} (hl : 0 ≤ l) : ∀ cs : List Br, (∃ c ∈ cs, c ≠ .node []) → sumYl l cs < cs.length
  | [] => fun h => by obtain ⟨c, hc, _⟩ := h; simp at hc
  | c :: cs => fun ⟨d, hd, hne⟩ => by
      simp only [sumYl, List.length_cons]; push_cast
      rcases List.mem_cons.mp hd with rfl | hd'
      · linarith [msgl_lt_one hl d hne, sumYl_le_length hl cs]
      · linarith [msgl_le_one hl c, sumYl_lt_length hl cs ⟨d, hd', hne⟩]

lemma all_leaves {l : ℝ} : ∀ cs : List Br, (∀ c ∈ cs, c = .node []) → prodTl l cs = 1 ∧ sumYl l cs = cs.length
  | [] => fun _ => by simp [prodTl, sumYl]
  | c :: cs => fun h => by
      obtain ⟨h1, h2⟩ := all_leaves cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rw [h c List.mem_cons_self]
      simp only [prodTl, sumYl, h1, h2, List.length_cons]
      rw [Tl_node, msgl_node]; simp [prodTl, sumYl]
      refine ⟨h1, ?_⟩
      rw [h2]; push_cast; ring

lemma sizeL_pos : ∀ cs : List Br, cs ≠ [] → 1 ≤ sizeL cs
  | [], h => absurd rfl h
  | c :: cs, _ => by simp only [sizeL]; cases c; simp [size]; omega

/-- strictness on Br-trees -/
theorem oneblock_strict {l : ℝ} (hl : 1 + √5 ≤ l) (b : Br) :
    ZTl l b < (1 + l) * (1 + l / 2) ^ (((size b : ℝ) - 1) / 2) := by
  have hl0 : 0 < l := by have := Real.sqrt_nonneg 5; linarith
  have hb : 1 < 1 + l / 2 := by linarith
  cases b with
  | node cs =>
    have hs : ((size (.node cs) : ℝ) - 1) / 2 = (sizeL cs : ℝ) / 2 := by simp only [size]; push_cast; ring
    rw [hs]
    rcases eq_or_ne cs [] with rfl | hne
    · rw [ZTl_leaf]; simp [sizeL]; linarith
    · rw [ZTl_node hl0.le]
      have hk : (0:ℝ) < cs.length := by exact_mod_cast List.length_pos_iff.mpr hne
      have hsz : (0:ℝ) < (sizeL cs : ℝ) / 2 := by
        have := sizeL_pos cs hne; positivity
      have hpow : 1 < (1 + l / 2) ^ ((sizeL cs : ℝ) / 2) := Real.one_lt_rpow hb hsz
      by_cases hall : ∀ c ∈ cs, c = .node []
      · obtain ⟨h1, h2⟩ := all_leaves (l := l) cs hall
        rw [h1, h2, mul_div_assoc, div_self hk.ne', mul_one, one_mul]
        have : 0 < 1 + l := by linarith
        nlinarith
      · push Not at hall
        have hR := sumYl_lt_length hl0.le cs hall
        have hfac : 1 + l * sumYl l cs / (cs.length : ℝ) < 1 + l := by
          rw [add_lt_add_iff_left, div_lt_iff₀ hk]; nlinarith
        have hP := prodTl_le hl cs
        have hP0 := prodTl_pos hl0.le cs
        calc prodTl l cs * (1 + l * sumYl l cs / (cs.length : ℝ))
            < prodTl l cs * (1 + l) := mul_lt_mul_of_pos_left hfac hP0
          _ ≤ (1 + l / 2) ^ ((sizeL cs : ℝ) / 2) * (1 + l) :=
              mul_le_mul_of_nonneg_right hP (by linarith)
          _ = (1 + l) * (1 + l / 2) ^ ((sizeL cs : ℝ) / 2) := by ring

end

end Br

/-- the oneblock bound is strict on every finite tree -/
theorem pi_lam_lt_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : ℝ} (hl : 1 + √5 ≤ l) (hG : G.IsTree) :
    piL l G < (1 + l) * (1 + l / 2) ^ (((Fintype.card V : ℝ) - 1) / 2) := by
  obtain ⟨b, f, hf, _, hsize, he⟩ := Br.tree_realize (Fintype.card V) G hG rfl
  rw [Br.piL_eq_ZTl G hf he l, ← hsize]
  exact Br.oneblock_strict hl b

end LeanCherry
