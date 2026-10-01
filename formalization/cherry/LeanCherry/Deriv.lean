/-
LeanCherry.Deriv -- the lam-derivatives of the cavity recursion:
  HasDerivAt (msgl . b) (Ml l b),  HasDerivAt (Tl . b) (Tl l b * Dl l b),  HasDerivAt (log Tl . b) (Dl l b)   (l > 0).
-/
import LeanCherry.Param

open Real

namespace LeanCherry

namespace Br

noncomputable section

lemma denom_pos {l : ℝ} (hl : 0 ≤ l) (cs : List Br) : 0 < (cs.length : ℝ) + 1 + l * sumYl l cs := by
  have := sumYl_nonneg hl cs; have : 0 ≤ l * sumYl l cs := mul_nonneg hl this; positivity

mutual
lemma hasDeriv_msgl {l : ℝ} (hl : 0 < l) : ∀ b : Br, HasDerivAt (fun x => msgl x b) (Ml l b) l
  | .node cs => by
      have hR := hasDeriv_sumYl hl cs
      have hg : HasDerivAt (fun x => ((cs.length : ℝ) + 1) + x * sumYl x cs)
          (sumYl l cs + l * sumMl l cs) l :=
        (((hasDerivAt_id' l).mul hR).const_add ((cs.length : ℝ) + 1)).congr_deriv (by ring)
      have hpos := denom_pos hl.le cs
      have hinv := hg.inv hpos.ne'
      have hfun : (fun x => msgl x (.node cs)) = fun x => (((cs.length : ℝ) + 1) + x * sumYl x cs)⁻¹ := by
        funext x; rw [msgl_node, one_div]
      rw [hfun]
      refine hinv.congr_deriv ?_
      rw [Ml_node, msgl_node]
      field_simp
lemma hasDeriv_sumYl {l : ℝ} (hl : 0 < l) : ∀ cs : List Br, HasDerivAt (fun x => sumYl x cs) (sumMl l cs) l
  | [] => by simp only [sumYl, sumMl]; exact hasDerivAt_const l 0
  | c :: cs => by
      simp only [sumYl, sumMl]
      exact (hasDeriv_msgl hl c).add (hasDeriv_sumYl hl cs)
end

mutual
lemma hasDeriv_Tl {l : ℝ} (hl : 0 < l) : ∀ b : Br, HasDerivAt (fun x => Tl x b) (Tl l b * Dl l b) l
  | .node cs => by
      have hP := hasDeriv_prodTl hl cs
      have hR := hasDeriv_sumYl hl cs
      have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
      have hh : HasDerivAt (fun x => 1 + x * sumYl x cs / ((cs.length : ℝ) + 1))
          ((sumYl l cs + l * sumMl l cs) / ((cs.length : ℝ) + 1)) l :=
        ((((hasDerivAt_id' l).mul hR).div_const ((cs.length : ℝ) + 1)).const_add 1).congr_deriv (by ring)
      have hfun : (fun x => Tl x (.node cs)) =
          fun x => prodTl x cs * (1 + x * sumYl x cs / ((cs.length : ℝ) + 1)) := by
        funext x; rw [Tl_node]
      rw [hfun]
      refine (hP.mul hh).congr_deriv ?_
      rw [Tl_node, Dl_node, msgl_node]
      have hpos := denom_pos hl.le cs
      field_simp
lemma hasDeriv_prodTl {l : ℝ} (hl : 0 < l) : ∀ cs : List Br,
    HasDerivAt (fun x => prodTl x cs) (prodTl l cs * sumDl l cs) l
  | [] => by simp only [prodTl, sumDl, mul_zero]; exact hasDerivAt_const l 1
  | c :: cs => by
      simp only [prodTl, sumDl]
      exact ((hasDeriv_Tl hl c).mul (hasDeriv_prodTl hl cs)).congr_deriv (by ring)
end

lemma hasDeriv_logTl {l : ℝ} (hl : 0 < l) (b : Br) : HasDerivAt (fun x => Real.log (Tl x b)) (Dl l b) l := by
  have h := (hasDeriv_Tl hl b).log (Tl_pos hl.le b).ne'
  refine h.congr_deriv ?_
  have := (Tl_pos hl.le b).ne'
  field_simp

end

end Br

end LeanCherry
