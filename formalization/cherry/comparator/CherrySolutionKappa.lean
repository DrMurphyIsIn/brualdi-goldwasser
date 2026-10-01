/- Comparator control (solution side): the three-piece window witness with slope kappa = 2 in place of
   kap = f*/t (Lean proves kap in [0.776, 0.8107]). `kap2_not_witness`: for EVERY l in the window this h is NOT a
   witness, since the Bellman inequality fails at (E, m, ybar) = (0, 1, y_C). `window_witness_kap2` is the false
   claim, left as `sorry` on purpose: the `neg_kappa` configuration must reject it. -/
import LeanCherry

namespace LeanCherry

noncomputable section

open Br

def hWk2 (l y : ℝ) : ℝ := max (max 0 (s1W l * (y - ydag l))) (epsW l + 2 * (y - yC l))

theorem window_witness_kap2 (l : ℝ) (h1 : 3.22 ≤ l) (h2 : l < 1 + √5) :
    Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hWk2 l) := by
  sorry

theorem kap2_not_witness (l : ℝ) (h1 : 3.22 ≤ l) (h2 : l < 1 + √5) :
    ¬ Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hWk2 l) := by
  intro W
  have H : InWin l := ⟨h1, h2⟩
  have hyc0 := H.yc_lo; have hyc1 := H.yc_hi
  have hTNE : TypeNonExempt {Br.node []} 0 1 := by
    intro b hb hbA
    rw [Set.mem_singleton_iff] at hbA
    have := (typeOf_leaf_iff {Br.node []} b).mpr hbA
    rw [hb] at this
    simp at this
  have hb := W.bell 0 1 (by simp) (by simp) hTNE (yC l) (fun _ => ⟨by linarith, by linarith⟩)
  unfold Bellman at hb
  simp only [Multiset.card_zero, Multiset.map_zero, Multiset.sum_zero, Nat.cast_zero, Nat.cast_one,
    zero_add, one_mul, add_zero] at hb
  rw [H.l_yc] at hb
  -- h(y_ch) = eps
  have hhy : hWk2 l (yC l) ≤ epsW l := by
    unfold hWk2
    have hs := H.s1_w; have he := H.eps_nonneg
    have e : s1W l * (yC l - ydag l) = epsW l := by rw [← hs]; rfl
    apply max_le (max_le he (le_of_eq e)); linarith
  -- h(1/(2+t)) >= eps + 2 (1/(2+t) - y_ch)
  have hlow : epsW l + 2 * (1 / (1 + 1 + tC l) - yC l) ≤ hWk2 l (1 / (1 + 1 + tC l)) := le_max_right _ _
  have ht0 := H.t_lo; have ht1 := H.t_hi
  have hq : (0.38196 : ℝ) ≤ 1 / (1 + 1 + tC l) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hF : fstar l < 1 / 2 + 0.000001 := by
    rw [H.fstar_eq]; linarith [H.fch_lt_half, H.eps_small]
  have hlog : (0.6168 / 2) / (1 + 0.61804 / 2) ≤ Real.log (1 + tC l / (1 + 1)) := by
    have hp : 0 < 1 + tC l / (1 + 1) := by linarith
    have h := Real.one_sub_inv_le_log_of_pos hp
    have e : 1 - (1 + tC l / (1 + 1))⁻¹ = (tC l / 2) / (1 + tC l / 2) := by field_simp; ring
    rw [e] at h
    have : (0.6168 / 2) / (1 + 0.61804 / 2) ≤ (tC l / 2) / (1 + tC l / 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith
  linarith

end

end LeanCherry
