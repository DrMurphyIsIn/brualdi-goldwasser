/-
LeanCherry.ThmE -- the branch ceiling in the whole cherry regime, kernel-checked:

  for every lam >= 1 + sqrt 5 and every planted branch b:   Tl lam b <= (1 + lam/2) ^ (|b|/2).

Proof: g(l) = log Tl l b - (|b|/2) log(2 + l) has derivative Dl l b - (|b|/2)/(2+l) = (l Dl - |b| alpha)/l <= 0 for l >= 2
(the recursive monomer-density inequality), so g is antitone on [lam_c, inf); at lam_c, the anchor gives Tl lam_c b <= phi^|b| and 2 + lam_c = 2 phi^2.
-/
import LeanCherry.LemmaMTree

open Real

namespace LeanCherry

namespace Br

noncomputable section

/-- g(l) = log T_b(l) - (|b|/2) log(2 + l) -/
def gE (b : Br) (l : ℝ) : ℝ := Real.log (Tl l b) - (size b : ℝ) / 2 * Real.log (2 + l)

lemma hasDeriv_gE {l : ℝ} (hl : 0 < l) (b : Br) :
    HasDerivAt (gE b) (Dl l b - (size b : ℝ) / 2 * (1 / (2 + l))) l := by
  have h1 := hasDeriv_logTl hl b
  have h2 : HasDerivAt (fun x => Real.log (2 + x)) (1 / (2 + l)) l := by
    have := ((hasDerivAt_id' l).const_add 2).log (by linarith)
    exact this.congr_deriv (by simp)
  exact h1.sub (h2.const_mul ((size b : ℝ) / 2))

lemma gE_deriv_nonpos {l : ℝ} (hl : 2 ≤ l) (b : Br) : Dl l b - (size b : ℝ) / 2 * (1 / (2 + l)) ≤ 0 := by
  have hM := lemmaM hl b
  have hl0 : 0 < l := by linarith
  have h2 : (0:ℝ) < 2 + l := by linarith
  unfold alpha at hM
  have e : (size b : ℝ) * (l / (2 * (2 + l))) = l * ((size b : ℝ) / 2 * (1 / (2 + l))) := by
    field_simp
  rw [e] at hM
  have := le_of_mul_le_mul_left hM hl0
  linarith

lemma lam_ge_two : (2:ℝ) ≤ lam := by unfold lam; linarith [φ_gt_one]

lemma gE_antitone (b : Br) : AntitoneOn (gE b) (Set.Ici lam) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici lam)
  · intro x hx
    have hx2 : 2 ≤ x := le_trans lam_ge_two hx
    exact (hasDeriv_gE (by linarith) b).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx2 : 2 ≤ x := le_trans lam_ge_two (le_of_lt hx)
    exact (hasDeriv_gE (by linarith) b).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact gE_deriv_nonpos (le_trans lam_ge_two (le_of_lt hx)) b

/-- The branch ceiling (kernel-checked): for every lam >= 1 + sqrt 5, every planted branch b satisfies
    T_b(lam) <= (1 + lam/2)^(|b|/2), i.e. log T_b(lam) <= |b| * (1/2) log(1 + lam/2) = |b| F*(lam). -/
theorem ceiling_cherry_regime (l : ℝ) (hl : 1 + √5 ≤ l) (b : Br) :
    Tl l b ≤ (1 + l / 2) ^ ((size b : ℝ) / 2) := by
  have hl' : lam ≤ l := by rw [lam_eq]; exact hl
  have hl0 : 0 < l := by linarith [lam_ge_two]
  have hmono := gE_antitone b (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hl') hl'
  -- value at lam_c
  have hA := ceiling_at_lam_c b
  rw [← Tl_lam] at hA
  have hTc := Tl_pos lam_pos.le b
  have hlogA : Real.log (Tl lam b) ≤ (size b : ℝ) * Real.log φ := by
    have := Real.log_le_log hTc hA
    rwa [Real.log_pow] at this
  have h2c : Real.log (2 + lam) = Real.log 2 + 2 * Real.log φ := by
    rw [two_add_lam, Real.log_mul (by norm_num) (pow_pos φ_pos 2).ne', Real.log_pow]; push_cast; ring
  unfold gE at hmono
  rw [h2c] at hmono
  -- so log T(l) <= (n/2)(log(2+l) - log 2) = (n/2) log(1 + l/2)
  have hlogl : Real.log (Tl l b) ≤ (size b : ℝ) / 2 * Real.log (1 + l / 2) := by
    have e : Real.log (1 + l / 2) = Real.log (2 + l) - Real.log 2 := by
      rw [← Real.log_div (by linarith) (by norm_num)]; congr 1; ring
    rw [e]; nlinarith
  have hpos : 0 < 1 + l / 2 := by linarith
  rw [Real.rpow_def_of_pos hpos]
  calc Tl l b = Real.exp (Real.log (Tl l b)) := (Real.exp_log (Tl_pos hl0.le b)).symm
    _ ≤ Real.exp (Real.log (1 + l / 2) * ((size b : ℝ) / 2)) := by
        apply Real.exp_le_exp.mpr; linarith

end

end Br

end LeanCherry
