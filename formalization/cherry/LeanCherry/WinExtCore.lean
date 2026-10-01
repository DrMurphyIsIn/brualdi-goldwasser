/-
LeanCherry.WinExtCore -- the window extended to [2.35, 3.22], part 1: the window witness argument, abstracted from the window constants.

`WFacts l` collects exactly the facts about the window constants (eps, ydag, w, s1, kap at l) that the Bellman
argument of LeanCherry.WinBell consumes.  `WFacts.witness` re-runs that argument (same witness h = hW l, same
case split k >= 1 / k = 0, m <= 7 / k = 0, m >= 8) from `WFacts l` alone, so any l at which the facts can be
established -- e.g. by the box enclosures of LeanCherry.WinExtBox below 3.22 -- carries a tight witness.
The files WinArms / WinConst / WinC2 / WinBell are imported unchanged.
-/
import LeanCherry.WinBell

open Real

namespace LeanCherry

noncomputable section

open Classical Br

/-- the facts about the window constants used by the Bellman argument -/
structure WFacts (l : ℝ) : Prop where
  pos : 0 < l
  Dinf_pos : 0 < Dinf l
  w_pos : 0 < wW l
  s1_le_kap : s1W l ≤ kapW l
  kap_le_two : kapW l ≤ 2
  ydag_ge : 1 / 9 ≤ ydag l
  l_le_8kap : l ≤ 8 * kapW l
  s_cube : 1 + 2 * l / 3 ≤ sC l ^ 3
  c4 : ∀ m : ℝ, 0 ≤ m → m * s1W l * (1 + l * ydag l) < l → wW l * (1 + l * m * wW l) ≤ yC l
  c2 : ∀ m : ℝ, 1 ≤ m → m ≤ 7 → (m = 1 ∨ m = 2 ∨ 3 ≤ m) → ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
    Real.log (1 + l * m * y / (m + 1)) - InWin.F0W l + kapW l * max 0 (1 / (m + 1 + l * m * y) - yC l)
      ≤ m * kapW l * max 0 (y - yC l)

namespace WFacts

variable {l : ℝ} (H : WFacts l)
include H

lemma s_sq : sC l ^ 2 = 1 + l / 2 := sC_sq H.pos.le
lemma s_pos : 0 < sC l := sC_pos H.pos.le
lemma yc_pos : 0 < yC l := by unfold yC; have := H.pos; positivity
lemma t_pos : 0 < tC l := by unfold tC; have := H.pos; positivity
lemma s_gt_one : 1 < sC l := by
  have h := H.s_sq; have h2 := H.s_pos; have := H.pos; nlinarith
lemma fch_pos : 0 < fch l := Real.log_pos H.s_gt_one
lemma eps_nonneg : 0 ≤ epsW l := by
  unfold epsW; have := fch_le_fstar H.pos H.Dinf_pos; linarith
lemma fstar_eq : fstar l = fch l + epsW l / 2 := by unfold epsW; ring
lemma fstar_pos : 0 < fstar l := by rw [H.fstar_eq]; have := H.fch_pos; have := H.eps_nonneg; linarith
lemma kap_pos : 0 < kapW l := by unfold kapW; exact div_pos H.fstar_pos H.t_pos
lemma s1_nonneg : 0 ≤ s1W l := div_nonneg H.eps_nonneg H.w_pos.le
lemma s1_w : s1W l * wW l = epsW l := by unfold s1W; field_simp [H.w_pos.ne']
lemma ydag_lt_yc : ydag l < yC l := by have := H.w_pos; unfold wW at this; linarith
lemma ydag_nonneg : 0 ≤ ydag l := by have := H.ydag_ge; linarith
lemma log_ydag : Real.log (1 + l * ydag l) = fstar l := by
  have e : 1 + l * ydag l = Real.exp (fstar l) := by
    unfold ydag; field_simp [H.pos.ne']; ring
  rw [e, Real.log_exp]

/-! ### the hinge facts (as in WinBell) -/

lemma hW_le_eps {y : ℝ} (hy : y ≤ yC l) : hW l y ≤ epsW l := by
  unfold hW
  have hs := H.s1_nonneg; have hk := H.kap_pos; have he := H.eps_nonneg
  apply max_le
  · apply max_le he
    have : s1W l * (y - ydag l) ≤ s1W l * (yC l - ydag l) := mul_le_mul_of_nonneg_left (by linarith) hs
    have e : s1W l * (yC l - ydag l) = epsW l := H.s1_w
    linarith
  · nlinarith

lemma hW_le_hinge (y : ℝ) : hW l y ≤ epsW l + kapW l * max 0 (y - yC l) := by
  unfold hW
  have hs := H.s1_nonneg; have hk := H.kap_pos; have he := H.eps_nonneg
  have hm := mul_nonneg hk.le (le_max_left 0 (y - yC l))
  have hm2 : kapW l * (y - yC l) ≤ kapW l * max 0 (y - yC l) := mul_le_mul_of_nonneg_left (le_max_right _ _) hk.le
  have hsw := H.s1_w
  apply max_le
  · apply max_le (by linarith)
    have e : s1W l * (y - ydag l) = epsW l + s1W l * (y - yC l) := by
      unfold wW at hsw; linear_combination hsw
    rw [e]
    rcases le_total y (yC l) with h | h
    · have : s1W l * (y - yC l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs (by linarith)
      linarith
    · have : s1W l * (y - yC l) ≤ kapW l * (y - yC l) := mul_le_mul_of_nonneg_right H.s1_le_kap (by linarith)
      linarith
  · linarith

lemma hW_lower (y : ℝ) : kapW l * max 0 (y - yC l) ≤ hW l y := by
  rcases le_total (y - yC l) 0 with h | h
  · rw [max_eq_left h, mul_zero]; exact hW_nonneg l y
  · rw [max_eq_right h]; have := hW_ge3 l y; have := H.eps_nonneg; linarith

lemma hW_zero {y : ℝ} (hy : y ≤ ydag l) : hW l y = 0 := by
  apply le_antisymm _ (hW_nonneg l y)
  unfold hW
  have hs := H.s1_nonneg; have hk := H.kap_pos
  apply max_le
  · exact max_le le_rfl (mul_nonpos_of_nonneg_of_nonpos hs (by linarith))
  · have hw := H.w_pos
    have h1 : kapW l * (y - yC l) ≤ -(kapW l * wW l) := by
      unfold wW; nlinarith
    have h2 : s1W l * wW l ≤ kapW l * wW l := mul_le_mul_of_nonneg_right H.s1_le_kap hw.le
    have := H.s1_w
    linarith

/-! ### k >= 1 (as in WinBell, with s_cube taken from the facts) -/

lemma step_kpos (k m y : ℝ) (hk : 1 ≤ k) (hk3 : k = 1 ∨ k = 2 ∨ 3 ≤ k) (hm : 0 ≤ m) (hR0 : 0 ≤ m * y)
    (hR1 : m * y ≤ m / 2) (hh : 0 ≤ m * hW l y) :
    hW l (1 / (k + m + 1 + l * (k + m * y))) ≤
      fstar l + k * fstar l + m * hW l y - Real.log (1 + l * (k + m * y) / (k + m + 1)) := by
  have hl := H.pos
  have hd : 0 < k + m + 1 := by linarith
  have hR : 0 ≤ l * (k + m * y) := by positivity
  have hyv : 1 / (k + m + 1 + l * (k + m * y)) ≤ yC l := by
    unfold yC
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hk hl.le]
  have hhv := H.hW_le_eps hyv
  have hpos : 0 < 1 + l * (k + m * y) / (k + m + 1) := by positivity
  have hF := H.fstar_eq
  have hfp := H.fstar_pos
  have he := H.eps_nonneg
  rcases hk3 with h1 | h2 | h3
  · subst h1
    have hr : l * (1 + m * y) / (1 + m + 1) ≤ l / 2 := by
      rw [div_le_div_iff₀ hd (by norm_num)]; nlinarith
    have hlog : Real.log (1 + l * (1 + m * y) / (1 + m + 1)) ≤ 2 * fch l := by
      rw [← log_c_eq hl.le]; exact Real.log_le_log hpos (by linarith)
    linarith
  · subst h2
    have hr : l * (2 + m * y) / (2 + m + 1) ≤ 2 * l / 3 := by
      rw [div_le_div_iff₀ hd (by norm_num)]; nlinarith
    have hlog : Real.log (1 + l * (2 + m * y) / (2 + m + 1)) ≤ 3 * fch l := by
      have : Real.log (1 + 2 * l / 3) ≤ Real.log (sC l ^ 3) := Real.log_le_log (by positivity) H.s_cube
      rw [Real.log_pow] at this
      have h' := Real.log_le_log hpos (by linarith : 1 + l * (2 + m * y) / (2 + m + 1) ≤ 1 + 2 * l / 3)
      unfold fch; push_cast at this; linarith
    linarith
  · have hr : l * (k + m * y) / (k + m + 1) ≤ l := by
      rw [div_le_iff₀ hd]; nlinarith
    have hlog : Real.log (1 + l * (k + m * y) / (k + m + 1)) ≤ 4 * fch l := by
      have h4 : 1 + l ≤ sC l ^ 4 := by
        have : sC l ^ 4 = (1 + l / 2) ^ 2 := by rw [← H.s_sq]; ring
        rw [this]; nlinarith
      have : Real.log (1 + l) ≤ Real.log (sC l ^ 4) := Real.log_le_log (by linarith) h4
      rw [Real.log_pow] at this
      have h' := Real.log_le_log hpos (by linarith : 1 + l * (k + m * y) / (k + m + 1) ≤ 1 + l)
      unfold fch; push_cast at this; linarith
    nlinarith

/-! ### k = 0, m >= 8 (as in WinBell, with l <= 8 kap taken from the facts) -/

lemma arm_deficit (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ fstar l + m * epsW l - Real.log (1 + l * m / (m + 1) * yC l) := by
  have hg : 0 ≤ gB l (fstar l) (armB m) := by
    unfold gB
    rw [armB_size]
    have h := fArm_le_fstar H.pos hm
    unfold fArm at h
    rw [div_le_iff₀ (by positivity)] at h
    push_cast; linarith
  have hyc0 : 0 < yC l := H.yc_pos
  have hT2 : 0 < 1 + l * (m * yC l) / (m + 1) := by have := H.pos; positivity
  unfold gB at hg
  rw [armB_size, Tl_armB, Real.log_mul (by have := H.pos; positivity) hT2.ne', Real.log_pow, log_c_eq H.pos.le] at hg
  have e : l * (m * yC l) / (m + 1) = l * m / (m + 1) * yC l := by ring
  rw [e] at hg
  unfold epsW
  push_cast at hg
  nlinarith

lemma step_m8 (m : ℕ) (hm : 8 ≤ m) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    hW l (1 / (m + 1 + l * (m * y))) ≤ fstar l + m * hW l y - Real.log (1 + l * (m * y) / (m + 1)) := by
  have hl := H.pos
  have hmR : (8:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hm1 : (0:ℝ) < m + 1 := by linarith
  have hyc0 : 0 < yC l := H.yc_pos
  have hyv : 1 / (m + 1 + l * (m * y)) ≤ ydag l := by
    have h9 : 9 ≤ m + 1 + l * (m * y) := by
      have : 0 ≤ l * (m * y) := mul_nonneg hl.le (mul_nonneg hm0 hy0)
      linarith
    have : 1 / (m + 1 + l * (m * y)) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) h9
    linarith [H.ydag_ge]
  rw [H.hW_zero hyv]
  set c := l * m / (m + 1) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcl : c ≤ l := by rw [hc, div_le_iff₀ hm1]; nlinarith
  have harg : l * (m * y) / (m + 1) = c * y := by rw [hc]; ring
  rw [harg]
  have hlyd := H.log_ydag
  have hyd0 : 0 ≤ ydag l := H.ydag_nonneg
  have hyc := H.ydag_lt_yc
  have hgm := H.arm_deficit m (by omega)
  rw [← hc] at hgm
  have hhw0 := hW_nonneg l y
  have hmh0 : 0 ≤ (m:ℝ) * hW l y := mul_nonneg hm0 hhw0
  have hcy0 : 0 ≤ c * y := mul_nonneg hc0.le hy0
  have hcyc0 : 0 < c * yC l := mul_pos hc0 hyc0
  rcases le_total y (ydag l) with h1 | h1
  · have hle : c * y ≤ l * ydag l := mul_le_mul hcl h1 hy0 hl.le
    have : Real.log (1 + c * y) ≤ Real.log (1 + l * ydag l) := Real.log_le_log (by linarith) (by linarith)
    linarith
  rcases le_total (yC l) y with h2 | h2
  · have hh := hW_ge3 l y
    have htan := log_le_tangent (by linarith : 0 < 1 + c * y) (by linarith : 0 < 1 + c * yC l)
    have e : (1 + c * y - (1 + c * yC l)) / (1 + c * yC l) = (c / (1 + c * yC l)) * (y - yC l) := by
      field_simp; ring
    rw [e] at htan
    have hq : c / (1 + c * yC l) ≤ m * kapW l := by
      have h1' : c / (1 + c * yC l) ≤ c := div_le_self hc0.le (by linarith)
      have h2' : 8 * kapW l ≤ m * kapW l := mul_le_mul_of_nonneg_right hmR H.kap_pos.le
      linarith [H.l_le_8kap]
    have hp1 := mul_le_mul_of_nonneg_left hh hm0
    have hp2 := mul_nonneg (by linarith : (0:ℝ) ≤ y - yC l) (by linarith : (0:ℝ) ≤ m * kapW l - c / (1 + c * yC l))
    linarith
  · have hh2 := hW_ge2 l y
    have hs1 := H.s1_nonneg
    have hld : 0 ≤ l * ydag l := mul_nonneg hl.le hyd0
    have hcyd0 : 0 ≤ c * ydag l := mul_nonneg hc0.le hyd0
    rcases lt_or_ge (m * s1W l * (1 + l * ydag l)) l with hT | hT
    · have hc4 := H.c4 (m:ℝ) hm0 hT
      have hsw := H.s1_w
      have hwdef : wW l = yC l - ydag l := rfl
      have hhe : epsW l + s1W l * (y - yC l) ≤ hW l y := by
        have e : epsW l + s1W l * (y - yC l) = s1W l * (y - ydag l) := by
          rw [← hsw, hwdef]; ring
        linarith
      have htan := log_le_tangent (by linarith : 0 < 1 + c * y) (by linarith : 0 < 1 + c * yC l)
      have e : (1 + c * y - (1 + c * yC l)) / (1 + c * yC l) = (c / (1 + c * yC l)) * (y - yC l) := by
        field_simp; ring
      rw [e] at htan
      set q := c / (1 + c * yC l) with hqdef
      have hq0 : 0 ≤ q := by rw [hqdef]; positivity
      have hp1 := mul_le_mul_of_nonneg_left hhe hm0
      have hB : fstar l + m * epsW l - Real.log (1 + c * yC l) + (y - yC l) * (m * s1W l - q)
          ≤ fstar l + m * hW l y - Real.log (1 + c * y) := by linarith
      rcases le_total (m * s1W l) q with hmq | hmq
      · have := mul_nonneg (by linarith : (0:ℝ) ≤ yC l - y) (by linarith : (0:ℝ) ≤ q - m * s1W l)
        linarith
      · have hlow : -(wW l) * (m * s1W l - q) ≤ (y - yC l) * (m * s1W l - q) :=
          mul_le_mul_of_nonneg_right (by rw [hwdef]; linarith) (by linarith)
        have hmw : m * epsW l = wW l * (m * s1W l) := by rw [← hsw]; ring
        have hkey : Real.log (1 + c * yC l) - fstar l ≤ wW l * q := by
          rw [← hlyd]
          have ht2 := log_le_tangent (by linarith : 0 < 1 + c * yC l) (by linarith : 0 < 1 + l * ydag l)
          have hE : (c * yC l - l * ydag l) * (1 + c * yC l) ≤ wW l * c * (1 + l * ydag l) := by
            have hyd : ydag l = yC l - wW l := by rw [hwdef]; ring
            rw [hyd, hc]
            have hid : wW l * (l * m / (m + 1)) * (1 + l * (yC l - wW l))
                - (l * m / (m + 1) * yC l - l * (yC l - wW l)) * (1 + l * m / (m + 1) * yC l)
                = l / (m + 1) * (yC l - wW l * (1 + l * m * wW l) + l * m / (m + 1) * yC l ^ 2) := by
              field_simp; ring
            have hnn : 0 ≤ l / (m + 1) * (yC l - wW l * (1 + l * m * wW l) + l * m / (m + 1) * yC l ^ 2) := by
              apply mul_nonneg (by positivity)
              have : 0 ≤ l * m / (m + 1) * yC l ^ 2 := by positivity
              have e3 : l * (m:ℝ) * wW l = l * m * wW l := rfl
              linarith
            linarith
          have hfrac : (1 + c * yC l - (1 + l * ydag l)) / (1 + l * ydag l) ≤ wW l * q := by
            rw [div_le_iff₀ (by linarith)]
            have e2 : wW l * q * (1 + l * ydag l) = wW l * c * (1 + l * ydag l) / (1 + c * yC l) := by
              rw [hqdef]; ring
            rw [e2, le_div_iff₀ (by linarith)]
            linarith
          linarith
        linarith
    · have htan := log_le_tangent (by linarith : 0 < 1 + c * y) (by linarith : 0 < 1 + c * ydag l)
      have e : (1 + c * y - (1 + c * ydag l)) / (1 + c * ydag l) = (c / (1 + c * ydag l)) * (y - ydag l) := by
        field_simp; ring
      rw [e] at htan
      have hq : c / (1 + c * ydag l) ≤ m * s1W l := by
        rw [div_le_iff₀ (by linarith)]
        have hid : m * s1W l * (1 + c * ydag l) - c = m / (m + 1) * ((m * s1W l * (1 + l * ydag l) - l) + s1W l) := by
          rw [hc]; field_simp; ring
        have : 0 ≤ m / (m + 1) * ((m * s1W l * (1 + l * ydag l) - l) + s1W l) :=
          mul_nonneg (by positivity) (by linarith)
        linarith
      have hlog0 : Real.log (1 + c * ydag l) ≤ fstar l := by
        rw [← hlyd]
        have : c * ydag l ≤ l * ydag l := mul_le_mul_of_nonneg_right hcl hyd0
        exact Real.log_le_log (by linarith) (by linarith)
      have hp1 := mul_le_mul_of_nonneg_left hh2 hm0
      have hp2 := mul_nonneg (by linarith : (0:ℝ) ≤ y - ydag l) (by linarith : (0:ℝ) ≤ m * s1W l - c / (1 + c * ydag l))
      linarith

/-! ### k = 0, 1 <= m <= 7 -/

lemma step_c2 (m : ℕ) (hm : 1 ≤ m) (hm7 : m ≤ 7) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    hW l (1 / (m + 1 + l * (m * y))) ≤ fstar l + m * hW l y - Real.log (1 + l * (m * y) / (m + 1)) := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm7R : (m:ℝ) ≤ 7 := by exact_mod_cast hm7
  have hcase : (m:ℝ) = 1 ∨ (m:ℝ) = 2 ∨ 3 ≤ (m:ℝ) := by
    rcases (by omega : m = 1 ∨ m = 2 ∨ 3 ≤ m) with e | e | e
    · left; exact_mod_cast e
    · right; left; exact_mod_cast e
    · right; right; exact_mod_cast e
  have hc2 := H.c2 (m:ℝ) hmR hm7R hcase y hy0 hy1
  have e1 : l * (m * y) = l * m * y := by ring
  rw [e1]
  have hup := H.hW_le_hinge (1 / (m + 1 + l * m * y))
  have hlo := H.hW_lower y
  have hF0 : InWin.F0W l = fstar l - epsW l := rfl
  rw [hF0] at hc2
  have hk := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ m)
  have e2 : (m:ℝ) * kapW l * max 0 (y - yC l) = (m:ℝ) * (kapW l * max 0 (y - yC l)) := by ring
  linarith

/-! ### the witness -/

theorem witness : Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hW l) where
  lam_pos := H.pos
  I_ord := Set.ordConnected_Icc
  I_lo := Set.Ioc_subset_Icc_self
  I_hi := Set.Icc_subset_Icc le_rfl (by norm_num)
  HA_type := by
    intro b b' h
    simp only [Set.mem_singleton_iff, ← typeOf_leaf_iff {Br.node []}, h]
  HA_m := by
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [(typeOf_leaf_iff {Br.node []} b).mpr hb]
  H0 := by
    intro a ha; rw [Set.mem_singleton_iff] at ha; rw [ha, gB_leaf]; exact H.fstar_pos.le
  convex := hW_convex l
  bdd := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hW_nonneg l y⟩
  leaf := fun h => absurd rfl h
  bell := by
    intro E m hE hcard _ ybar hy
    have hErep : E = Multiset.replicate E.card (Br.node []) :=
      Multiset.eq_replicate.mpr ⟨rfl, fun a ha => by simpa using hE a ha⟩
    set k := E.card with hk
    rw [hErep]
    unfold Bellman
    simp only [Multiset.map_replicate, Multiset.sum_replicate, Multiset.card_replicate, msgl_node, gB_leaf]
    simp only [List.length_nil, Nat.cast_zero, zero_add, sumYl, mul_zero, add_zero, div_one, nsmul_eq_mul, mul_one]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hm : 0 < m := by omega
      obtain ⟨ht0, ht1⟩ := hy hm
      rw [hk0]; push_cast
      simp only [zero_add, zero_mul, mul_zero, add_zero]
      rcases (by omega : m ≤ 7 ∨ 8 ≤ m) with h7 | h8
      · have := H.step_c2 m hm h7 ybar ht0 ht1
        simpa [add_comm, add_left_comm, add_assoc] using this
      · have := H.step_m8 m h8 ybar ht0 ht1
        simpa [add_comm, add_left_comm, add_assoc] using this
    · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have hkcase : (k : ℝ) = 1 ∨ (k : ℝ) = 2 ∨ 3 ≤ (k : ℝ) := by
        rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with e | e | e
        · left; exact_mod_cast e
        · right; left; exact_mod_cast e
        · right; right; exact_mod_cast e
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · have hstep := H.step_kpos (k : ℝ) 0 0 hk1 hkcase le_rfl (by norm_num) (by norm_num) (by norm_num)
        rw [hm0]; push_cast
        simp only [zero_mul, mul_zero, add_zero] at hstep ⊢
        linarith
      · obtain ⟨ht0, ht1⟩ := hy hm
        have hmR : (0:ℝ) ≤ m := by positivity
        have hstep := H.step_kpos (k : ℝ) (m : ℝ) ybar hk1 hkcase hmR (mul_nonneg hmR ht0)
          (by nlinarith) (mul_nonneg hmR (hW_nonneg l ybar))
        linarith

/-- the witness and a best arm, from the facts -/
theorem witness_and_arm : (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧
    ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l :=
  ⟨⟨_, _, _, H.witness⟩, fstar_attained H.pos H.Dinf_pos⟩

end WFacts

end

end LeanCherry
