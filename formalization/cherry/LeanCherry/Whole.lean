/-
LeanCherry.Whole -- whole trees: the root step and the one-block upper bound.

A WHOLE tree is a Br used as a rooted tree with no phantom parent edge: its root has degree k = #children; every other vertex
has degree #children + 1 (its parent edge).  tdeg is this true degree; ZTl the lambda-weighted matching sum with true degrees.
  ZTl_node : ZTl l (node cs) = prodTl l cs * (1 + l * sumYl l cs / k),   k = cs.length  (k = 0: the single vertex, ZTl = 1)
  oneblock : 1 + sqrt 5 <= l -> ZTl l b <= (1 + l) * (1 + l/2) ^ ((size b - 1)/2)      (the one-block upper bound on Br-trees)
-/
import LeanCherry.GraphMatch

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

noncomputable section

/-- true degree in a whole tree: #children at the root, #children + 1 elsewhere -/
def tdeg (b : Br) (v : List ℕ) : ℝ := if v = [] then (nch b : ℝ) else pdeg b v

/-- edge weight with true degrees -/
def wtT (l : ℝ) (b : Br) (e : List ℕ × List ℕ) : ℝ := l / (tdeg b e.1 * tdeg b e.2)

/-- the whole-tree matching sum -/
def ZTl (l : ℝ) (b : Br) : ℝ := Z (wtT l b) (edges b)

/-- the two recursion facts of the planted bridge, for every branch -/
lemma planted_facts {l : ℝ} (hl : 0 ≤ l) (b : Br) :
    Z (wt l b) (edges b) = Tl l b ∧ Z (wt l b) (restE 0 (kids b)) = prodTl l (kids b) := by
  have H : ∀ n : ℕ, ∀ b : Br, size b ≤ n →
      Z (wt l b) (edges b) = Tl l b ∧ Z (wt l b) (restE 0 (kids b)) = prodTl l (kids b) := by
    intro n
    induction n with
    | zero => intro b hb; cases b with | node cs => simp [size] at hb
    | succ n IH =>
      intro b hb
      cases b with
      | node cs =>
        have hIH : ∀ c ∈ cs, Z (wt l c) (edges c) = Tl l c ∧ Z (wt l c) (restE 0 (kids c)) = prodTl l (kids c) := by
          intro c hc; apply IH; have := size_le_of_mem cs c hc; simp only [size] at hb; omega
        have hfit := fits_self l cs cs 0 (List.drop_zero)
        refine ⟨?_, ?_⟩
        · rw [edges_node, fan_Z hl 0 cs hfit hIH, Tl_node]
        · exact rest_Z 0 cs hfit (fun c hc => (hIH c hc).1)
  exact H (size b) b le_rfl

lemma wtT_sh {l : ℝ} {cs : List Br} {i : ℕ} {c : Br} (h : cs[i]? = some c) (e : List ℕ × List ℕ) :
    wtT l (.node cs) (sh i e) = wt l c e := by
  rw [← wt_sh h e]
  simp only [wtT, wt, tdeg, sh_apply, reduceCtorEq, if_false]

lemma wtT_root {l : ℝ} {cs : List Br} {i : ℕ} {c : Br} (h : cs[i]? = some c) :
    wtT l (.node cs) ([], [i]) = l / ((cs.length : ℝ) * ((nch c : ℝ) + 1)) := by
  have h1 : subt (.node cs) [i] = some c := by rw [subt_cons h]; rfl
  simp only [wtT, tdeg, if_true, reduceCtorEq, if_false, pdeg, h1]
  rfl

lemma fits_whole (l : ℝ) (cs : List Br) : ∀ (L : List Br) (i : ℕ), cs.drop i = L →
    Fits l (cs.length : ℝ) (wtT l (.node cs)) i L
  | [], _, _ => trivial
  | c :: L, i, h => by
      have hc := drop_getElem? h
      exact ⟨fun e => wtT_sh hc e, wtT_root hc, fits_whole l cs L (i + 1) (drop_succ_of h)⟩

/-- the whole-tree root step -/
theorem ZTl_node {l : ℝ} (hl : 0 ≤ l) (cs : List Br) :
    ZTl l (.node cs) = prodTl l cs * (1 + l * sumYl l cs / (cs.length : ℝ)) := by
  unfold ZTl
  rw [edges_node, fan_Z hl 0 cs (fits_whole l cs cs 0 List.drop_zero) (fun c _ => planted_facts hl c)]

/-- the single vertex -/
theorem ZTl_leaf (l : ℝ) : ZTl l (.node []) = 1 := by
  unfold ZTl; rw [edges_node]; simp [fanE, Z_empty]

lemma sumYl_le_length {l : ℝ} (hl : 0 ≤ l) : ∀ cs : List Br, sumYl l cs ≤ cs.length
  | [] => by simp [sumYl]
  | c :: cs => by
      simp only [sumYl, List.length_cons]; push_cast
      linarith [msgl_le_one hl c, sumYl_le_length hl cs]

lemma prodTl_le {l : ℝ} (hl : 1 + √5 ≤ l) : ∀ cs : List Br,
    prodTl l cs ≤ (1 + l / 2) ^ ((sizeL cs : ℝ) / 2)
  | [] => by simp [prodTl, sizeL]
  | c :: cs => by
      have hl0 : 0 ≤ l := by have := Real.sqrt_nonneg 5; linarith
      have hb : 0 < 1 + l / 2 := by linarith
      simp only [prodTl, sizeL]
      push_cast
      rw [show ((size c : ℝ) + (sizeL cs : ℝ)) / 2 = (size c : ℝ) / 2 + (sizeL cs : ℝ) / 2 by ring,
        Real.rpow_add hb]
      exact mul_le_mul (ceiling_cherry_regime l hl c) (prodTl_le hl cs) (prodTl_pos hl0 cs).le
        (Real.rpow_nonneg hb.le _)

/-- the one-block upper bound for whole Br-trees -/
theorem oneblock {l : ℝ} (hl : 1 + √5 ≤ l) (b : Br) :
    ZTl l b ≤ (1 + l) * (1 + l / 2) ^ (((size b : ℝ) - 1) / 2) := by
  have hl0 : 0 ≤ l := by have := Real.sqrt_nonneg 5; linarith
  have hb : 0 < 1 + l / 2 := by linarith
  cases b with
  | node cs =>
    have hs : ((size (.node cs) : ℝ) - 1) / 2 = (sizeL cs : ℝ) / 2 := by simp only [size]; push_cast; ring
    rw [hs]
    rcases eq_or_ne cs [] with rfl | hne
    · rw [ZTl_leaf]; simp [sizeL]; linarith
    · rw [ZTl_node hl0]
      have hk : (0:ℝ) < cs.length := by
        have := List.length_pos_iff.mpr hne; exact_mod_cast this
      have hR : l * sumYl l cs / (cs.length : ℝ) ≤ l := by
        rw [div_le_iff₀ hk]
        exact mul_le_mul_of_nonneg_left (sumYl_le_length hl0 cs) hl0
      have hR0 : 0 ≤ l * sumYl l cs / (cs.length : ℝ) :=
        div_nonneg (mul_nonneg hl0 (sumYl_nonneg hl0 cs)) hk.le
      calc prodTl l cs * (1 + l * sumYl l cs / (cs.length : ℝ))
          ≤ (1 + l / 2) ^ ((sizeL cs : ℝ) / 2) * (1 + l) :=
            mul_le_mul (prodTl_le hl cs) (by linarith) (by linarith) (Real.rpow_nonneg hb.le _)
        _ = (1 + l) * (1 + l / 2) ^ ((sizeL cs : ℝ) / 2) := by ring

end

end Br

end LeanCherry
