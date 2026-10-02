/-
LeanCherry.PBW2 -- part (B), the kinked witness W2 on (0, 3/20], where F = f* = f_3 (PBGap.fstar_eq_f3, a direct
comparison of the arms, in place of lem:lam-cross):
  h(y) = max(0, s_a (y - ydag), h2 + s_b (y - y2), eps + kappa (y - y_ch)),  h2 = (4/5) g(A_2),
  s_a = h2/(y2 - ydag),  s_b = (eps - h2)/(y_ch - y2),  y2 = y(A_2) = 1/(3 + 2t).
The scalar conditions (T1)-(T8) are LeanCherry.PBC.cert_C10; (S2) is cert_C1; m = 1 uses C4-C6.
-/
import LeanCherry.PBWstar

open Real

namespace LeanCherry

noncomputable section

/-- the kink value h2 = (4/5) g(A_2) -/
def h2v (l : ℝ) : ℝ := 4 / 5 * gArm l 2
/-- the slope s_a of the first ramp -/
def saW (l : ℝ) : ℝ := h2v l / (yA l 2 - ydag l)
/-- the slope s_b of the second ramp -/
def sbW (l : ℝ) : ℝ := (epsW l - h2v l) / (yC l - yA l 2)
/-- the witness W2 -/
def hT (l y : ℝ) : ℝ :=
  max (max (max 0 (saW l * (y - ydag l))) (h2v l + sbW l * (y - yA l 2))) (epsW l + kapP l * (y - yC l))

lemma affine_convex (a b : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) (1 / 2)) (fun y => a * y + b) := by
  refine ⟨convex_Icc _ _, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  apply le_of_eq
  linear_combination (-b) * hpq

lemma hT_eq (l : ℝ) : hT l = fun y => max (max (max (0 * y + 0) (saW l * y + -(saW l * ydag l)))
    (sbW l * y + (h2v l - sbW l * yA l 2))) (kapP l * y + (epsW l - kapP l * yC l)) := by
  funext y; unfold hT; ring_nf

lemma hT_convex (l : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) (1 / 2)) (hT l) := by
  rw [hT_eq]
  exact (((affine_convex 0 0).sup (affine_convex _ _)).sup (affine_convex _ _)).sup (affine_convex _ _)

/-- the W2 facts on (0, 3/20], given F = f3 there -/
structure W2Facts (l : ℝ) : Prop where
  base : PB l
  le : l ≤ 3 / 20
  F3 : fstar l = fArm l 3

namespace W2Facts

variable {l : ℝ} (W : W2Facts l)
include W

lemma H : PB l := W.base
lemma t43 : tC l ≤ 3 / 43 := by
  have hl := W.base.pos
  unfold tC; rw [div_le_iff₀ (by linarith)]; linarith [W.le]

lemma eps_eq : epsW l = PBC.eps3 (tC l) := by
  rw [W.base.eps3_eq]; unfold epsW; rw [W.F3]
lemma E_eq : Real.exp (fstar l) = PBC.E3 (tC l) := by rw [W.base.E3_eq, W.F3]
lemma f_eq : fstar l = PBC.f3 (tC l) := by rw [W.base.f3_eq, W.F3]
lemma h2_eq : h2v l = PBC.h2 (tC l) := by
  have H := W.base
  unfold h2v PBC.h2 PBC.G2
  have hg : gArm l 2 = 5 / 2 * epsW l - Dj l 2 := by
    unfold gArm Dj; rw [PB.fstar_eq]; push_cast; ring
  rw [hg, W.eps_eq, ← H.D2_eq]
  unfold PBC.eps3 PBC.D2 PBC.f3 PBC.ell
  ring

/-- the scalar conditions (T1)-(T8) at F = f* -/
lemma C10 :
    Real.exp (fstar l) - 1 < kapP l ∧ h2v l < epsW l ∧ kapP l < tC l ∧ 0 < fstar l ∧ 0 < h2v l ∧
    h2v l * (tC l - kapP l) ≤ (epsW l - h2v l) * (kapP l - Real.exp (fstar l) + 1) ∧
    epsW l - h2v l ≤ (tC l - kapP l) * yA l 4 * (1 - kapP l * yA l 4) ∧
    kapP l - Real.exp (fstar l) + 1 ≤ h2v l * (1 + 14 * Real.exp (fstar l)) ∧
    13 * (Real.exp (fstar l) - 1) ≤ 14 * fstar l ∧
    0 ≤ fstar l - kapP l - h2v l + 2 * Real.sqrt (kapP l * h2v l) ∧
    0 ≤ fstar l + 5 * epsW l - 5 * tC l / 6 ∧ tC l / 36 ≤ epsW l := by
  have H := W.base
  obtain ⟨T1, T3a, T3b, Tf, TG, T2, T4, T5, T6, T7, T8, T8b⟩ := PBC.cert_C10 (tC l) H.t_pos W.t43
  rw [H.kap_eq] at *
  rw [H.y4_eq] at T4
  rw [← W.E_eq] at T1 T2 T5 T6
  rw [← W.eps_eq] at T3a T2 T4 T8 T8b
  rw [← W.h2_eq] at T3a T2 T4 T5 T7
  rw [← W.f_eq] at Tf T6 T7 T8
  have hh2 : 0 < h2v l := by
    rw [W.h2_eq]; unfold PBC.h2; positivity
  exact ⟨T1, T3a, T3b, Tf, hh2, T2, T4, T5, T6, T7, T8, T8b⟩

lemma ydag_lt_y2 : ydag l < yA l 2 := by
  have H := W.base
  obtain ⟨T1, -⟩ := W.C10
  have h1 := H.l_ydag
  have h2 : l * yA l 2 = kapP l := (PB.kap_eq_y2).symm
  have : l * ydag l < l * yA l 2 := by linarith
  exact lt_of_mul_lt_mul_left this H.pos.le

lemma y2_lt_yc : yA l 2 < yC l := by
  have H := W.base
  obtain ⟨-, -, T3b, -⟩ := W.C10
  have h1 := H.l_yc
  have h2 : l * yA l 2 = kapP l := (PB.kap_eq_y2).symm
  have : l * yA l 2 < l * yC l := by linarith
  exact lt_of_mul_lt_mul_left this H.pos.le

lemma sa_mul : saW l * (yA l 2 - ydag l) = h2v l := by
  unfold saW; field_simp [(sub_pos.mpr W.ydag_lt_y2).ne']
lemma sb_mul : h2v l + sbW l * (yC l - yA l 2) = epsW l := by
  unfold sbW; field_simp [(sub_pos.mpr W.y2_lt_yc).ne']; ring

lemma l_y2d : l * (yA l 2 - ydag l) = kapP l - Real.exp (fstar l) + 1 := by
  have := W.base.l_ydag; have h2 : l * yA l 2 = kapP l := (PB.kap_eq_y2).symm
  linear_combination h2 - this
lemma l_yc2 : l * (yC l - yA l 2) = tC l - kapP l := by
  have := W.base.l_yc; have h2 : l * yA l 2 = kapP l := (PB.kap_eq_y2).symm
  linear_combination this - h2

lemma sa_eq : saW l = l * h2v l / (kapP l - Real.exp (fstar l) + 1) := by
  unfold saW; rw [← W.l_y2d]; have := W.base.pos; field_simp
lemma sb_eq : sbW l = l * (epsW l - h2v l) / (tC l - kapP l) := by
  unfold sbW; rw [← W.l_yc2]; have := W.base.pos; field_simp

lemma sa_pos : 0 < saW l := by
  unfold saW; obtain ⟨-, -, -, -, hh, -⟩ := W.C10
  exact div_pos hh (sub_pos.mpr W.ydag_lt_y2)
lemma sb_pos : 0 < sbW l := by
  unfold sbW; obtain ⟨-, h, -⟩ := W.C10
  exact div_pos (by linarith) (sub_pos.mpr W.y2_lt_yc)

lemma sa_le_sb : saW l ≤ sbW l := by
  obtain ⟨T1, -, T3b, -, -, T2, -⟩ := W.C10
  rw [W.sa_eq, W.sb_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  have := mul_le_mul_of_nonneg_left T2 W.base.pos.le
  nlinarith

lemma sb_le : sbW l ≤ l * yA l 4 * (1 - kapP l * yA l 4) := by
  obtain ⟨-, -, T3b, -, -, -, T4, -⟩ := W.C10
  rw [W.sb_eq, div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left T4 W.base.pos.le
  nlinarith

lemma sb_le_kap : sbW l ≤ kapP l := by
  have H := W.base
  have h := W.sb_le
  have hy4 : 0 < yA l 4 := by unfold yA; have := H.t_pos; positivity
  have hk := H.kap_pos
  have h1 : l * yA l 4 * (1 - kapP l * yA l 4) ≤ l * yA l 4 := by
    have : 0 ≤ l * yA l 4 * (kapP l * yA l 4) := by have := H.pos; positivity
    nlinarith
  have h2 : l * yA l 4 ≤ kapP l := by
    rw [PB.kap_eq_y2]
    apply mul_le_mul_of_nonneg_left _ H.pos.le
    unfold yA; apply one_div_le_one_div_of_le (by have := H.t_pos; positivity); have := H.t_pos; linarith
  linarith


lemma shape : PShape l (sbW l) (hT l) where
  conv := hT_convex l
  nonneg := fun y => le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  zero := by
    intro y hy
    have H := W.base
    apply le_antisymm _ (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
    change max (max (max 0 (saW l * (y - ydag l))) (h2v l + sbW l * (y - yA l 2)))
      (epsW l + kapP l * (y - yC l)) ≤ 0
    have hsa := W.sa_pos; have hss := W.sa_le_sb; have hsk := W.sb_le_kap
    have hd2 := W.ydag_lt_y2; have h2c := W.y2_lt_yc
    have h1 : saW l * (y - ydag l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsa.le (by linarith)
    have h2 : h2v l + sbW l * (y - yA l 2) ≤ 0 := by
      have : sbW l * (y - yA l 2) ≤ saW l * (y - yA l 2) := mul_le_mul_of_nonpos_right hss (by linarith)
      have e := W.sa_mul
      nlinarith
    have h3 : epsW l + kapP l * (y - yC l) ≤ 0 := by
      have : kapP l * (y - yC l) ≤ sbW l * (y - yC l) := mul_le_mul_of_nonpos_right hsk (by linarith)
      have e := W.sb_mul
      nlinarith
    exact max_le (max_le (max_le le_rfl h1) h2) h3
  up := by
    intro y
    have H := W.base
    have hsa := W.sa_pos; have hss := W.sa_le_sb; have hsk := W.sb_le_kap; have hsb := W.sb_pos
    have hk := H.kap_pos; have he := H.eps_pos
    have e1 := W.sa_mul; have e2 := W.sb_mul
    have hm := mul_nonneg hk.le (le_max_left 0 (y - yC l))
    have hpiece : ∀ a : ℝ, 0 ≤ a → a ≤ kapP l → a * (y - yC l) ≤ kapP l * max 0 (y - yC l) := by
      intro a ha hak
      rcases le_total y (yC l) with h | h
      · have : a * (y - yC l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (by linarith)
        linarith
      · rw [max_eq_right (by linarith)]; exact mul_le_mul_of_nonneg_right hak (by linarith)
    have p1 := hpiece (saW l) hsa.le (le_trans hss hsk)
    have p2 := hpiece (sbW l) hsb.le hsk
    have p3 := hpiece (kapP l) hk.le le_rfl
    have hsaC : saW l * (yC l - ydag l) ≤ epsW l := by
      have : saW l * (yC l - yA l 2) ≤ sbW l * (yC l - yA l 2) :=
        mul_le_mul_of_nonneg_right hss (by linarith [W.y2_lt_yc])
      nlinarith
    unfold hT
    refine max_le (max_le (max_le (by linarith) ?_) ?_) ?_
    · nlinarith
    · nlinarith
    · linarith
  kap_lo := fun y => le_max_right _ _
  left_lo := by
    intro y
    have e : epsW l + sbW l * (y - yC l) = h2v l + sbW l * (y - yA l 2) := by
      have := W.sb_mul; linear_combination -this
    rw [e]; exact le_max_of_le_left (le_max_right _ _)
  piece := by
    intro z
    have H := W.base
    have hsa := W.sa_pos; have hss := W.sa_le_sb; have hsk := W.sb_le_kap; have hsb := W.sb_pos
    have hk := H.kap_pos
    have l0 : ∀ y, 0 * y + 0 ≤ hT l y := fun y => by
      simp only [zero_mul, add_zero]; exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
    have l1 : ∀ y, saW l * y + -(saW l * ydag l) ≤ hT l y := fun y => by
      have : saW l * y + -(saW l * ydag l) = saW l * (y - ydag l) := by ring
      rw [this]; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    have l2 : ∀ y, sbW l * y + (h2v l - sbW l * yA l 2) ≤ hT l y := fun y => by
      have : sbW l * y + (h2v l - sbW l * yA l 2) = h2v l + sbW l * (y - yA l 2) := by ring
      rw [this]; exact le_max_of_le_left (le_max_right _ _)
    have l3 : ∀ y, kapP l * y + (epsW l - kapP l * yC l) ≤ hT l y := fun y => by
      have : kapP l * y + (epsW l - kapP l * yC l) = epsW l + kapP l * (y - yC l) := by ring
      rw [this]; exact le_max_right _ _
    have hz : hT l z = max (max (max (0 * z + 0) (saW l * z + -(saW l * ydag l)))
        (sbW l * z + (h2v l - sbW l * yA l 2))) (kapP l * z + (epsW l - kapP l * yC l)) := by
      rw [hT_eq]
    rcases max_choice (max (max (0 * z + 0) (saW l * z + -(saW l * ydag l)))
        (sbW l * z + (h2v l - sbW l * yA l 2))) (kapP l * z + (epsW l - kapP l * yC l)) with h | h
    · rw [h] at hz
      rcases max_choice (max (0 * z + 0) (saW l * z + -(saW l * ydag l)))
          (sbW l * z + (h2v l - sbW l * yA l 2)) with h' | h'
      · rw [h'] at hz
        rcases max_choice (0 * z + 0) (saW l * z + -(saW l * ydag l)) with h'' | h''
        · rw [h''] at hz; exact ⟨0, 0, le_rfl, hk.le, hz, l0⟩
        · rw [h''] at hz; exact ⟨saW l, _, hsa.le, le_trans hss hsk, hz, l1⟩
      · rw [h'] at hz; exact ⟨sbW l, _, hsb.le, hsk, hz, l2⟩
    · rw [h] at hz; exact ⟨kapP l, _, hk.le, le_rfl, hz, l3⟩

/-- h(y2) = h2 = (4/5) g(A2) <= g(A2) -/
lemma hg2 : hT l (yA l 2) ≤ gArm l 2 := by
  have H := W.base
  have hg0 := H.gArm_nonneg 2 (by norm_num)
  push_cast at hg0
  have hss := W.sa_le_sb; have hsk := W.sb_le_kap
  have e1 := W.sa_mul; have e2 := W.sb_mul
  have h2c := W.y2_lt_yc
  have hh : h2v l = 4 / 5 * gArm l 2 := rfl
  unfold hT
  refine max_le (max_le (max_le (by linarith) (by linarith)) (by linarith)) ?_
  have : kapP l * (yA l 2 - yC l) ≤ sbW l * (yA l 2 - yC l) := mul_le_mul_of_nonpos_right hsk (by linarith)
  nlinarith

/-- the node conditions of the flat tail, from (T5)-(T8) -/
lemma T5' (m : ℕ) (hm : 14 ≤ m) : l ≤ saW l * (1 + m * Real.exp (fstar l)) := by
  have H := W.base
  obtain ⟨T1, -, -, -, hh, -, -, T5, -⟩ := W.C10
  have hE := Real.exp_pos (fstar l)
  have hmR : (14:ℝ) ≤ m := by exact_mod_cast hm
  rw [W.sa_eq, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  have h1 : h2v l * (1 + 14 * Real.exp (fstar l)) ≤ h2v l * (1 + m * Real.exp (fstar l)) := by
    apply mul_le_mul_of_nonneg_left _ hh.le; nlinarith
  have := mul_le_mul_of_nonneg_left (le_trans T5 h1) H.pos.le
  nlinarith

lemma Nd (m : ℕ) (hm : m ≤ 13) : m * (Real.exp (fstar l) - 1) ≤ (m + 1) * fstar l := by
  obtain ⟨-, -, -, -, -, -, -, -, T6, -⟩ := W.C10
  have hE := Real.add_one_le_exp (fstar l)
  have hmR : (m:ℝ) ≤ 13 := by exact_mod_cast hm
  have hm0 : (0:ℝ) ≤ m := by positivity
  have : (m:ℝ) * (Real.exp (fstar l) - 1 - fstar l) ≤ 13 * (Real.exp (fstar l) - 1 - fstar l) :=
    mul_le_mul_of_nonneg_right hmR (by linarith)
  nlinarith

lemma N2 (m : ℕ) : kapP l * m / (m + 1) ≤ fstar l + m * h2v l := by
  have H := W.base
  obtain ⟨-, -, -, -, hh, -, -, -, -, T7, -⟩ := W.C10
  have hk := H.kap_pos
  have hm1 : (0:ℝ) < m + 1 := by positivity
  set s := Real.sqrt (kapP l * h2v l) with hs
  have hs2 : s ^ 2 = kapP l * h2v l := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- AM-GM: (m+1) h2 + kappa/(m+1) >= 2 s
  have amgm : 2 * s ≤ (m + 1) * h2v l + kapP l / (m + 1) := by
    rw [← sub_nonneg]
    have e : (m + 1) * h2v l + kapP l / (m + 1) - 2 * s = ((m + 1) * h2v l - s) ^ 2 / ((m + 1) * h2v l) := by
      field_simp
      linear_combination (-1 : ℝ) * hs2
    rw [e]; positivity
  have e2 : kapP l * m / (m + 1) = kapP l - kapP l / (m + 1) := by field_simp; ring
  rw [e2]
  nlinarith

lemma NC (m : ℕ) (hm : 5 ≤ m) : tC l * m / (m + 1) ≤ fstar l + m * epsW l := by
  have H := W.base
  obtain ⟨-, -, -, -, -, -, -, -, -, -, T8, T8b⟩ := W.C10
  have ht := H.t_pos
  have hmR : (5:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0:ℝ) < m + 1 := by linarith
  -- F + m eps - t m/(m+1) = [F + 5 eps - 5t/6] + (m - 5)(eps - t/(6(m+1)))
  have e : fstar l + m * epsW l - tC l * m / (m + 1)
      = (fstar l + 5 * epsW l - 5 * tC l / 6) + (m - 5) * (epsW l - tC l / (6 * (m + 1))) := by
    field_simp; ring
  have h1 : tC l / (6 * (m + 1)) ≤ tC l / 36 := by
    apply div_le_div_of_nonneg_left ht.le (by norm_num); nlinarith
  have h2 : 0 ≤ (m - 5) * (epsW l - tC l / (6 * (m + 1))) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **the witness W2 on (0, 3/20]** -/
theorem witness : Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hT l) := by
  have H := W.base
  have Sh := W.shape
  apply H.witness_of_steps Sh.conv Sh.nonneg
  · intro k m y hk hy0 hy1
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hkcase : (k : ℝ) = 1 ∨ (k : ℝ) = 2 ∨ 3 ≤ (k : ℝ) := by
      rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with e | e | e
      · left; exact_mod_cast e
      · right; left; exact_mod_cast e
      · right; right; exact_mod_cast e
    have hm0 : (0:ℝ) ≤ m := by positivity
    exact H.step_kpos Sh (k : ℝ) (m : ℝ) y hk1 hkcase hm0 (mul_nonneg hm0 hy0) (by nlinarith)
      (mul_nonneg hm0 (Sh.nonneg y))
  · intro m y hm hy0 hy1
    rcases (by omega : m = 1 ∨ (2 ≤ m ∧ m ≤ 4) ∨ 5 ≤ m) with h1 | ⟨h2, h4⟩ | h5
    · subst h1
      have := H.step_m1 Sh (PBC.cert_C4 l) (PBC.cert_C5 l H.pos.le (by have := H.hi; norm_num at this ⊢; linarith))
        (PBC.cert_C6 (tC l) H.t_pos.le H.t_le') y hy0 hy1
      simpa using this
    · apply H.step_arm Sh W.sb_le m h2 h4 _ y hy0 hy1
      rcases (by omega : m = 2 ∨ m = 3 ∨ m = 4) with e | e | e
      · subst e; push_cast; exact W.hg2
      · subst e
        rw [Sh.zero _ (by push_cast; exact H.S2)]
        have := H.gArm_nonneg 3 (by norm_num); push_cast at this ⊢; exact this
      · subst e
        have hy43 : yA l 4 ≤ yA l 3 := by
          unfold yA; apply one_div_le_one_div_of_le (by have := H.t_pos; positivity); have := H.t_pos; linarith
        rw [Sh.zero _ (by push_cast; exact le_trans hy43 H.S2)]
        have := H.gArm_nonneg 4 (by norm_num); push_cast at this ⊢; exact this
    · exact H.step_flat2 Sh (saW l) (h2v l) (sbW l)
        (fun y => le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
        (fun y => le_max_of_le_left (le_max_right _ _))
        W.ydag_lt_y2 W.y2_lt_yc W.sa_mul W.sb_mul W.T5' W.Nd W.N2 (fun m hm _ => W.NC m hm) m h5 y hy0 hy1

end W2Facts


end

end LeanCherry
