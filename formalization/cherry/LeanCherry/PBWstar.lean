/-
LeanCherry.PBWstar -- part (B), the witness W* on [3/20, 1 + sqrt 5):
  h(y) = max(0, s1 (y - ydag), eps + kappa (y - y_ch)),  kappa = lam y(A_2) = lam/(3 + 2t),  A = {leaf},  I = [0, 1/2].
The scalar conditions (S2), (S3), (S4), (S5), (S6) are reduced by hand (enclosures of eps, tangent and Taylor bounds) to the
certificates of LeanCherry.PBCerts / PBCertsFix (all proved there), and (S1) is by hand.
-/
import LeanCherry.PBFlat
import LeanCherry.PBCertsFix

open Real

namespace LeanCherry

noncomputable section

/-! ### cubic bounds for log -/

lemma log_one_add_le3 {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3)
  have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (1 / (1 + x) - (1 - x + x ^ 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x :=
      ((hasDerivAt_id' x).const_add 1).log (ne_of_gt (by linarith))
    have h2 := (((hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 3 x).div_const 3))
    have h3 : HasDerivAt f (1 / (1 + x) - (1 - 2 * x ^ (2 - 1) / 2 + 3 * x ^ (3 - 1) / 3)) x := by
      have := h1.sub h2
      push_cast at this
      exact this
    refine h3.congr_deriv ?_
    norm_num
  have hanti : AntitoneOn f (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hd x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : (0:ℝ) < x := hx
      rw [(hd x hx'.le).deriv]
      have e : 1 / (1 + x) - (1 - x + x ^ 2) = -(x ^ 3 / (1 + x)) := by field_simp; ring
      rw [e]; have : 0 ≤ x ^ 3 / (1 + x) := by positivity
      linarith
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [f] at this
  norm_num at this
  linarith

lemma log_one_sub_le3 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 - x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun x => Real.log (1 - x) + (x + x ^ 2 / 2 + x ^ 3 / 3)
  have hd : ∀ x : ℝ, x < 1 → HasDerivAt f (-(1 / (1 - x)) + (1 + x + x ^ 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - x)) x :=
      ((hasDerivAt_id' x).const_sub 1).log (ne_of_gt (by linarith))
    have h2 := (((hasDerivAt_id' x).add ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 3 x).div_const 3))
    have h3 : HasDerivAt f (-1 / (1 - x) + (1 + 2 * x ^ (2 - 1) / 2 + 3 * x ^ (3 - 1) / 3)) x := by
      have := h1.add h2
      push_cast at this
      exact this
    refine h3.congr_deriv ?_
    norm_num; ring
  have hanti : AntitoneOn f (Set.Ico 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
    · intro x hx; exact (hd x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (hd x hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hd x hx.2).deriv]
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have e : -(1 / (1 - x)) + (1 + x + x ^ 2) = -(x ^ 3 / (1 - x)) := by field_simp; ring
      rw [e]; have : 0 ≤ x ^ 3 / (1 - x) := by have := hx.1; positivity
      linarith
  have := hanti ⟨le_rfl, by norm_num⟩ ⟨hx0, hx1⟩ hx0
  simp only [f] at this
  norm_num at this
  linarith

namespace PB

variable {l : ℝ} (H : PB l)
include H

/-! ### the bridge to the certificate variables (t = tC l) -/

lemma htl : tC l * (2 + l) = l := by unfold tC; have := H.pos; field_simp
lemma hl1 : l * (1 - tC l) = 2 * tC l := by linear_combination (-1 : ℝ) * H.htl
lemma t_le' : tC l ≤ 6181 / 10000 := by have := H.t_le; norm_num at this ⊢; linarith
lemma ell_eq : PBC.ell (tC l) = 2 * fch l := by unfold PBC.ell; rw [H.fch_eq]; ring
lemma f3_eq : PBC.f3 (tC l) = fArm l 3 := by
  rw [fArm_eq H.pos.le]; unfold PBC.f3 Dj; rw [H.ell_eq]; push_cast
  have : tC l * 3 / (3 + 1) = 3 * tC l / 4 := by ring
  rw [this]; ring
lemma kap_eq : PBC.kap (tC l) = kapP l := by
  unfold PBC.kap kapP
  have h1t : 0 < 1 - tC l := by linarith [H.t_lt_one]
  have ht := H.t_pos
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(3 + 2 * tC l)) * H.hl1
lemma y4_eq : PBC.y4 (tC l) = yA l 4 := by unfold PBC.y4 yA; ring
lemma q3_eq : tC l * PBC.q3 (tC l) = l * yA l 3 := by
  unfold PBC.q3 yA
  have h1t : 0 < 1 - tC l := by linarith [H.t_lt_one]
  have ht := H.t_pos
  push_cast
  rw [mul_div_assoc', mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(4 + 3 * tC l)) * H.hl1
lemma D2_eq : PBC.D2 (tC l) = Dj l 2 := by
  unfold PBC.D2 Dj; rw [H.ell_eq]; push_cast
  have : tC l * 2 / (2 + 1) = 2 * tC l / 3 := by ring
  rw [this]; ring
lemma E3_eq : PBC.E3 (tC l) = Real.exp (fArm l 3) := by unfold PBC.E3; rw [H.f3_eq]
lemma eps3_eq : PBC.eps3 (tC l) = 2 * (fArm l 3 - fch l) := by
  unfold PBC.eps3; rw [H.f3_eq, H.ell_eq]; ring
lemma sqrt_eq : 1 / Real.sqrt (1 - tC l) = sC l := by
  have h := H.s_sq_t
  have hs := H.s_pos
  have e : 1 - tC l = (1 / sC l) ^ 2 := by field_simp; linarith
  rw [e, Real.sqrt_sq (by positivity)]; field_simp
lemma fArm3_le : fArm l 3 ≤ fstar l := fArm_le_fstar H.pos (by norm_num)

/-! ### (S2) and (S3) -/

/-- (S2): y(A_3) <= ydag, from C1 -/
lemma S2 : yA l 3 ≤ ydag l := by
  have c := PBC.cert_C1 (tC l) H.t_pos H.t_le'
  rw [H.q3_eq, H.f3_eq] at c
  have hy3 : 0 < yA l 3 := by unfold yA; have := H.t_pos; positivity
  have hpos : 0 < 1 + l * yA l 3 := by have := H.pos; positivity
  have h1 := lt_of_lt_of_le c H.fArm3_le
  have h1' : 1 + l * yA l 3 < Real.exp (fstar l) := (Real.log_lt_iff_lt_exp hpos).mp h1
  have := H.l_ydag
  have h2 : l * yA l 3 < l * ydag l := by linarith
  exact (lt_of_mul_lt_mul_left h2 H.pos.le).le

/-- (S3): s1 <= lam y4 (1 - kappa y4), from C2 and the enclosures of eps -/
lemma S3 : s1W l ≤ l * yA l 4 * (1 - kapP l * yA l 4) := by
  have c := PBC.cert_C2 (tC l) H.t_pos.le H.t_le'
  rw [H.sqrt_eq, H.kap_eq, H.y4_eq] at c
  have hD := H.Dinf_pos
  have he6 := H.eps_le_D6
  have hu := H.u_ge
  have hs := H.s_pos
  have hy4 : yA l 4 = 1 / (5 + 4 * tC l) := by unfold yA; ring
  have ht := H.t_pos
  have h54 : 0 < 5 + 4 * tC l := by linarith
  have hk : 0 < 1 - kapP l * yA l 4 := by
    by_contra hcon; push Not at hcon
    have : 11 / 12 * sC l * (1 - kapP l * yA l 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
    linarith
  -- (5 + 4t) eps <= u (1 - kappa y4)
  have key : (5 + 4 * tC l) * epsW l ≤ uP l * (1 - kapP l * yA l 4) := by
    have h1 : (5 + 4 * tC l) * epsW l ≤ (5 + 4 * tC l) * (Dinf l / 6) := mul_le_mul_of_nonneg_left he6 h54.le
    have h2 : 11 / 12 * sC l * Dinf l ≤ uP l := by
      have : sC l * (Dinf l - epsW l / 2) ≥ sC l * (11 / 12 * Dinf l) :=
        mul_le_mul_of_nonneg_left (by linarith) hs.le
      linarith
    have h3 : (5 + 4 * tC l) * (Dinf l / 6) ≤ 11 / 12 * sC l * Dinf l * (1 - kapP l * yA l 4) := by
      have := mul_le_mul_of_nonneg_right c.le hD.le
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right h2 hk.le
    linarith
  rw [H.s1_eq, div_le_iff₀ H.u_pos, hy4]
  rw [hy4] at key
  have hl := H.pos
  have : l * (1 / (5 + 4 * tC l)) * (1 - kapP l * (1 / (5 + 4 * tC l))) * uP l
      = l * (uP l * (1 - kapP l * (1 / (5 + 4 * tC l)))) / (5 + 4 * tC l) := by field_simp
  rw [this, le_div_iff₀ h54]
  have := mul_le_mul_of_nonneg_left key hl.le
  linarith

omit H in
/-- **psi_mono**: Psi = eps (3/2 + delta/u) - D(2) is monotone in F, in the form used for (S6): if delta >= 0,
    0 < u <= u3 (u = 1 + t - e^F, u3 = 1 + t - e^{f3}, F >= f3) and eps3 <= eps with eps >= 0, then
    Psi(f3) <= Psi(F).  No sign of eps3 is needed. -/
lemma psi_mono {e e3 d u u3 D2 : ℝ} (hd : 0 ≤ d) (hu : 0 < u) (huu : u ≤ u3) (he : e3 ≤ e) (he0 : 0 ≤ e) :
    e3 * (3 / 2 + d / u3) - D2 ≤ e * (3 / 2 + d / u) - D2 := by
  have hq : d / u3 ≤ d / u := div_le_div_of_nonneg_left hd hu huu
  have hb : 0 ≤ 3 / 2 + d / u3 := by
    have : 0 ≤ d / u3 := div_nonneg hd (by linarith)
    linarith
  have h1 : e3 * (3 / 2 + d / u3) ≤ e * (3 / 2 + d / u3) := mul_le_mul_of_nonneg_right he hb
  have h2 : e * (3 / 2 + d / u3) ≤ e * (3 / 2 + d / u) := mul_le_mul_of_nonneg_left (by linarith) he0
  linarith

/-! ### (S4) -/

lemma D_eq_logs : Dinf l = Real.log (1 + tC l) + Real.log (1 - tC l) / 2 := by
  unfold Dinf; rw [H.fch_eq]; ring

lemma D_le_Dmax : Dinf l ≤ PBC.Dmax := by
  rw [H.D_eq_logs]; unfold PBC.Dmax
  have ht := H.t_pos; have ht1 := H.t_lt_one
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 3 * (1 + tC l) / 4)
  have h2 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 3 * (1 - tC l) / 2)
  have e1 : Real.log (3 * (1 + tC l) / 4) = Real.log (1 + tC l) - Real.log (4 / 3) := by
    rw [show 3 * (1 + tC l) / 4 = (1 + tC l) / (4 / 3) by ring, Real.log_div (by linarith) (by norm_num)]
  have e2 : Real.log (3 * (1 - tC l) / 2) = Real.log (1 - tC l) - Real.log (2 / 3) := by
    rw [show 3 * (1 - tC l) / 2 = (1 - tC l) / (2 / 3) by ring, Real.log_div (by linarith) (by norm_num)]
  rw [e1] at h1; rw [e2] at h2
  linarith

lemma exp3D_le : Real.exp (3 * Dinf l) ≤ 1291 / 1000 := by
  obtain ⟨he, hlt⟩ := PBC.cert_Dmax
  have h1 : Real.exp (3 * Dinf l) ≤ Real.exp (3 * PBC.Dmax) := Real.exp_le_exp.mpr (by linarith [H.D_le_Dmax])
  have h2 : Real.exp (3 * PBC.Dmax) ^ 2 = 32768 / 19683 := by
    rw [← Real.exp_nat_mul, ← he]; norm_num; ring_nf
  have h3 : Real.exp (3 * PBC.Dmax) < 1291 / 1000 := by
    have := Real.exp_pos (3 * PBC.Dmax)
    nlinarith
  linarith

lemma D_le_cubic : Dinf l ≤ tC l / 2 - 3 * tC l ^ 2 / 4 + tC l ^ 3 / 6 := by
  rw [H.D_eq_logs]
  have h1 := log_one_add_le3 H.t_pos.le
  have h2 := log_one_sub_le3 H.t_pos.le H.t_lt_one
  linarith

lemma rho_le : Dinf l / sig l ≤ PBC.rhohat (tC l) := by
  have ht := H.t_pos
  rw [PB.sig_eq, div_div_eq_mul_div, div_le_iff₀ ht]
  unfold PBC.rhohat
  have := H.D_le_cubic
  have h1 : Dinf l * (1 + tC l) ≤ (tC l / 2 - 3 * tC l ^ 2 / 4 + tC l ^ 3 / 6) * (1 + tC l) :=
    mul_le_mul_of_nonneg_right this (by linarith)
  nlinarith

lemma rho_pos : 0 < Dinf l / sig l := div_pos H.Dinf_pos H.sig_pos

lemma rhohat_le : PBC.rhohat (tC l) ≤ 1 / 2 := by
  unfold PBC.rhohat; have ht := H.t_pos; have ht1 := H.t_lt_one
  nlinarith [mul_pos ht ht, mul_pos (mul_pos ht ht) ht]

omit H in
lemma gS_nonneg {r : ℝ} (h0 : 0 ≤ r) : 0 ≤ PBC.gS r := by
  unfold PBC.gS
  have h1 : 0 ≤ 1 - r / (8 + 6 * r) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  positivity

/-- the threshold inequality behind (S4): e^{3D} g(rho) t (1 + sqrt c) <= (1 + t)^2, from C3 -/
lemma S4key : Real.exp (3 * Dinf l) * PBC.gS (Dinf l / sig l) * tC l * (1 + sC l) ≤ (1 + tC l) ^ 2 := by
  have c := PBC.cert_C3 (tC l) H.t_pos H.t_le'
  rw [H.sqrt_eq] at c
  have hr := H.rho_le; have hr0 := H.rho_pos; have hrh := H.rhohat_le
  have hg : PBC.gS (Dinf l / sig l) ≤ PBC.gS (PBC.rhohat (tC l)) :=
    PBC.mono_g ⟨hr0.le, le_trans hr hrh⟩ ⟨le_trans hr0.le hr, hrh⟩ hr
  have hg0 := gS_nonneg hr0.le
  have hX := H.exp3D_le
  have hX0 := Real.exp_pos (3 * Dinf l)
  have ht := H.t_pos
  have hs := H.s_pos
  have hp : 0 ≤ tC l * (1 + sC l) := by positivity
  have h1 : Real.exp (3 * Dinf l) * PBC.gS (Dinf l / sig l) ≤ 1291 / 1000 * PBC.gS (PBC.rhohat (tC l)) := by
    have := mul_le_mul hX hg hg0 (by norm_num)
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hp
  have e1 : Real.exp (3 * Dinf l) * PBC.gS (Dinf l / sig l) * tC l * (1 + sC l)
      = Real.exp (3 * Dinf l) * PBC.gS (Dinf l / sig l) * (tC l * (1 + sC l)) := by ring
  have e2 : 1291 / 1000 * PBC.gS (PBC.rhohat (tC l)) * tC l * (1 + sC l)
      = 1291 / 1000 * PBC.gS (PBC.rhohat (tC l)) * (tC l * (1 + sC l)) := by ring
  rw [e1]; rw [e2] at c
  linarith

/-- (S4): u^2 (u - eps) <= eps E (E - 1) -/
lemma S4 : uP l ^ 2 * (uP l - epsW l) ≤ epsW l * Real.exp (fstar l) * (Real.exp (fstar l) - 1) := by
  have hD := H.Dinf_pos; have hσ := H.sig_pos; have hs := H.s_pos; have hs1 := H.s_gt_one
  have heps := H.eps_pos; have hU := H.u_pos; have hEs := H.E_ge
  have hE0 := Real.exp_pos (fstar l)
  set E := Real.exp (fstar l) with hEdef
  set em := Dinf l ^ 2 / (4 * sig l + 3 * Dinf l) with hemdef
  have hem := H.eps_lower
  have hem0 : 0 < em := by rw [hemdef]; positivity
  have hRHS : em * sC l * (sC l - 1) ≤ epsW l * E * (E - 1) := by
    have a1 : em * sC l ≤ epsW l * E := mul_le_mul hem.le hEs hs.le heps.le
    exact mul_le_mul a1 (by linarith) (by linarith) (by positivity)
  rcases le_total (uP l) (epsW l) with hue | hue
  · have : uP l ^ 2 * (uP l - epsW l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    have : 0 ≤ em * sC l * (sC l - 1) := by
      have : 0 ≤ sC l - 1 := by linarith
      positivity
    linarith
  -- u^2 (u - eps) <= u^3 <= W^3 <= em sqrt c (sqrt c - 1)
  set ρ := Dinf l / sig l with hρ
  set B := 1 - ρ / (8 + 6 * ρ) with hB
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hDem : Dinf l - em / 2 = Dinf l * B := by
    rw [hemdef, hB, hρ]; field_simp; ring
  have hB0 : 0 < B := by
    rw [hB, sub_pos, div_lt_one (by positivity)]; linarith
  set W := sC l * Real.exp (Dinf l) * (Dinf l * B) with hW
  have hUW : uP l ≤ W := by
    have := H.u_le
    have h2 : Dinf l - epsW l / 2 ≤ Dinf l * B := by rw [← hDem]; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ sC l * Real.exp (Dinf l))
    linarith
  have h1 : uP l ^ 2 * (uP l - epsW l) ≤ uP l ^ 3 := by
    have := mul_le_mul_of_nonneg_left (by linarith : uP l - epsW l ≤ uP l) (sq_nonneg (uP l))
    nlinarith
  have h2 : uP l ^ 3 ≤ W ^ 3 := pow_le_pow_left₀ hU.le hUW 3
  -- W^3 (4 sigma + 3 D) = D^2 sqrt c (sqrt c^2 X sigma^2 g(rho))
  set X := Real.exp (3 * Dinf l) with hX
  set G := PBC.gS ρ with hG
  have hX3 : Real.exp (Dinf l) ^ 3 = X := by rw [hX, ← Real.exp_nat_mul]; norm_num
  have hGdef : G = ρ * B ^ 3 * (4 + 3 * ρ) := by rw [hG]; unfold PBC.gS; rw [hB]
  have hid : W ^ 3 * (4 * sig l + 3 * Dinf l) = Dinf l ^ 2 * sC l * (sC l ^ 2 * X * sig l ^ 2 * G) := by
    rw [hW, hGdef, ← hX3, hρ]; field_simp
  -- sqrt c^2 X sigma^2 g(rho) <= sqrt c - 1, from S4key
  have hkey := H.S4key
  rw [← hX, ← hρ, ← hG] at hkey
  have ht := H.t_pos; have ht1 := H.t_lt_one
  have hsq := H.s_sq_t
  have hsig : sig l = tC l / (1 + tC l) := PB.sig_eq
  have hmain : sC l ^ 2 * X * sig l ^ 2 * G ≤ sC l - 1 := by
    have hX0 : 0 < X := Real.exp_pos _
    have hG0 : 0 ≤ G := gS_nonneg hρ0.le
    -- multiply both sides by (1 - t) (1 + t)^2 (1 + sqrt c) > 0
    have hpos : 0 < (1 - tC l) * (1 + tC l) ^ 2 * (1 + sC l) := by
      have : 0 < 1 - tC l := by linarith
      positivity
    have hsig2 : sig l ^ 2 * (1 + tC l) ^ 2 = tC l ^ 2 := by
      rw [hsig]; have h1t : (1 + tC l) ≠ 0 := by linarith
      field_simp
    have eL : sC l ^ 2 * X * sig l ^ 2 * G * ((1 - tC l) * (1 + tC l) ^ 2 * (1 + sC l))
        = X * G * tC l * (1 + sC l) * tC l := by
      calc sC l ^ 2 * X * sig l ^ 2 * G * ((1 - tC l) * (1 + tC l) ^ 2 * (1 + sC l))
          = (sC l ^ 2 * (1 - tC l)) * X * G * (1 + sC l) * (sig l ^ 2 * (1 + tC l) ^ 2) := by ring
        _ = X * G * tC l * (1 + sC l) * tC l := by rw [hsq, hsig2]; ring
    have eR : (sC l - 1) * ((1 - tC l) * (1 + tC l) ^ 2 * (1 + sC l)) = tC l * (1 + tC l) ^ 2 := by
      linear_combination ((1 + tC l) ^ 2) * hsq
    have := mul_le_mul_of_nonneg_right hkey ht.le
    have hfin : sC l ^ 2 * X * sig l ^ 2 * G * ((1 - tC l) * (1 + tC l) ^ 2 * (1 + sC l))
        ≤ (sC l - 1) * ((1 - tC l) * (1 + tC l) ^ 2 * (1 + sC l)) := by
      rw [eL, eR]; nlinarith
    exact le_of_mul_le_mul_right hfin hpos
  have hW3 : W ^ 3 * (4 * sig l + 3 * Dinf l) ≤ Dinf l ^ 2 * sC l * (sC l - 1) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hmain (by positivity)
  have hW3' : W ^ 3 ≤ em * sC l * (sC l - 1) := by
    rw [hemdef, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  linarith


/-! ### the witness W* -/

lemma s1_le_kap : s1W l ≤ kapP l := by
  have h := H.S3
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

end PB

/-- the witness W* -/
def hS (l y : ℝ) : ℝ := max (max 0 (s1W l * (y - ydag l))) (epsW l + kapP l * (y - yC l))

namespace PB

variable {l : ℝ} (H : PB l)
include H

lemma hS_shape : PShape l (s1W l) (hS l) where
  conv := by
    refine ⟨convex_Icc _ _, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hx3 : epsW l + kapP l * (x - yC l) ≤ hS l x := le_max_right _ _
    have hy3 : epsW l + kapP l * (y - yC l) ≤ hS l y := le_max_right _ _
    have hx2 : s1W l * (x - ydag l) ≤ hS l x := le_max_of_le_left (le_max_right _ _)
    have hy2 : s1W l * (y - ydag l) ≤ hS l y := le_max_of_le_left (le_max_right _ _)
    have hx1 : 0 ≤ hS l x := le_max_of_le_left (le_max_left _ _)
    have hy1 : 0 ≤ hS l y := le_max_of_le_left (le_max_left _ _)
    unfold hS
    apply max_le
    · apply max_le
      · positivity
      · have e : s1W l * (a * x + b * y - ydag l) = a * (s1W l * (x - ydag l)) + b * (s1W l * (y - ydag l)) := by
          linear_combination (s1W l * ydag l) * hab
        rw [e]
        exact add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
    · have e : epsW l + kapP l * (a * x + b * y - yC l)
          = a * (epsW l + kapP l * (x - yC l)) + b * (epsW l + kapP l * (y - yC l)) := by
        linear_combination (-(epsW l - kapP l * yC l)) * hab
      rw [e]
      exact add_le_add (mul_le_mul_of_nonneg_left hx3 ha) (mul_le_mul_of_nonneg_left hy3 hb)
  nonneg := fun y => le_max_of_le_left (le_max_left _ _)
  zero := by
    intro y hy
    apply le_antisymm _ (le_max_of_le_left (le_max_left _ _))
    change max (max 0 (s1W l * (y - ydag l))) (epsW l + kapP l * (y - yC l)) ≤ 0
    have hs := H.s1_pos; have hk := H.s1_le_kap; have hw := H.w_pos; have hsw := H.s1_w
    apply max_le
    · exact max_le le_rfl (mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith))
    · have h1 : kapP l * (y - yC l) ≤ -(kapP l * wW l) := by
        have : y - yC l ≤ -wW l := by unfold wW; linarith
        nlinarith [H.kap_pos]
      have h2 : s1W l * wW l ≤ kapP l * wW l := mul_le_mul_of_nonneg_right hk hw.le
      linarith
  up := by
    intro y
    unfold hS
    have hs := H.s1_pos; have hk := H.kap_pos; have he := H.eps_pos; have hsk := H.s1_le_kap
    have hm := mul_nonneg hk.le (le_max_left 0 (y - yC l))
    have hm2 : kapP l * (y - yC l) ≤ kapP l * max 0 (y - yC l) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hk.le
    have hsw := H.s1_w
    apply max_le
    · apply max_le (by linarith)
      have e : s1W l * (y - ydag l) = epsW l + s1W l * (y - yC l) := by
        unfold wW at hsw; linear_combination hsw
      rw [e]
      rcases le_total y (yC l) with h | h
      · have : s1W l * (y - yC l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)
        linarith
      · have : s1W l * (y - yC l) ≤ kapP l * (y - yC l) := mul_le_mul_of_nonneg_right hsk (by linarith)
        rw [max_eq_right (by linarith)]; linarith
    · linarith
  kap_lo := fun y => le_max_right _ _
  left_lo := by
    intro y
    have hsw := H.s1_w
    have e : epsW l + s1W l * (y - yC l) = s1W l * (y - ydag l) := by
      unfold wW at hsw; linear_combination -hsw
    rw [e]; exact le_max_of_le_left (le_max_right _ _)
  piece := by
    intro z
    have hs := H.s1_pos; have hk := H.kap_pos; have hsk := H.s1_le_kap
    by_cases h3 : max 0 (s1W l * (z - ydag l)) ≤ epsW l + kapP l * (z - yC l)
    · refine ⟨kapP l, epsW l - kapP l * yC l, hk.le, le_rfl, ?_, fun y => ?_⟩
      · unfold hS; rw [max_eq_right h3]; ring
      · have : kapP l * y + (epsW l - kapP l * yC l) = epsW l + kapP l * (y - yC l) := by ring
        rw [this]; exact le_max_right _ _
    · push Not at h3
      by_cases h2 : 0 ≤ s1W l * (z - ydag l)
      · refine ⟨s1W l, -(s1W l * ydag l), hs.le, hsk, ?_, fun y => ?_⟩
        · unfold hS; rw [max_eq_left h3.le, max_eq_right h2]; ring
        · have : s1W l * y + -(s1W l * ydag l) = s1W l * (y - ydag l) := by ring
          rw [this]; exact le_max_of_le_left (le_max_right _ _)
      · push Not at h2
        refine ⟨0, 0, le_rfl, hk.le, ?_, fun y => ?_⟩
        · unfold hS; rw [max_eq_left h3.le, max_eq_left h2.le]; ring
        · simp only [zero_mul, add_zero]; exact le_max_of_le_left (le_max_left _ _)

/-- (S6): g(A_2) >= h(y_2), on [3/20, lam_c); the C7 regime uses that Psi is increasing in F (F >= f3) -/
lemma S6 (h3 : 3 / 20 ≤ l) : hS l (yA l 2) ≤ gArm l 2 := by
  have hl := H.pos; have ht := H.t_pos; have ht1 := H.t_lt_one
  have ht43 : 3 / 43 ≤ tC l := by
    unfold tC; rw [le_div_iff₀ (by linarith)]; linarith
  have hc := PBC.cert_S6_full (tC l) ht43 H.t_le'
  rw [H.kap_eq, H.D2_eq] at hc
  have heps := H.eps_pos; have hu := H.u_pos; have hk := H.kap_pos; have hsk := H.s1_le_kap
  have hs1 := H.s1_pos
  -- g(A_2) = (5/2) eps - D(2)
  have hg : gArm l 2 = 5 / 2 * epsW l - Dj l 2 := by
    unfold gArm Dj; rw [PB.fstar_eq]; push_cast
    have : tC l * 2 / (2 + 1) = tC l * 2 / (2 + 1) := rfl
    ring
  have hlyc := H.l_yc
  have hly2 : l * yA l 2 = kapP l := (PB.kap_eq_y2).symm
  have hyc2 : yC l = (1 - tC l) / 2 := by rw [H.one_sub_t]; unfold yC; field_simp
  have hy2 : yA l 2 = 1 / (3 + 2 * tC l) := by unfold yA; ring
  have hshape := H.hS_shape
  -- for t <= 1/2 (y2 <= y_ch): h(y2) = max(0, eps - eps delta/u)
  have low : tC l ≤ 1 / 2 → 0 < epsW l * (3 / 2 + (tC l - kapP l) / uP l) - Dj l 2 → hS l (yA l 2) ≤ gArm l 2 := by
    intro htt hpsi
    have hy2c : yA l 2 ≤ yC l := by
      rw [hy2, hyc2, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hval : s1W l * (yA l 2 - ydag l) = epsW l - epsW l * (tC l - kapP l) / uP l := by
      rw [H.s1_eq]
      have e1 : yA l 2 - ydag l = (yC l - ydag l) - (yC l - yA l 2) := by ring
      rw [e1]
      have hw : yC l - ydag l = uP l / l := H.w_eq
      rw [hw]
      have e2 : l * (yC l - yA l 2) = tC l - kapP l := by linarith
      have hu0 := H.u_pos.ne'
      have hl0 := H.pos.ne'
      calc l * epsW l / uP l * (uP l / l - (yC l - yA l 2))
          = epsW l - epsW l * (l * (yC l - yA l 2)) / uP l := by field_simp
        _ = epsW l - epsW l * (tC l - kapP l) / uP l := by rw [e2]
    have hgA0 := H.gArm_nonneg 2 (by norm_num)
    push_cast at hgA0
    unfold hS
    apply max_le
    · apply max_le hgA0
      rw [hval, hg]
      have : epsW l * (3 / 2 + (tC l - kapP l) / uP l) = 3 / 2 * epsW l + epsW l * (tC l - kapP l) / uP l := by
        ring
      linarith
    · have h1 : kapP l * (yA l 2 - yC l) ≤ s1W l * (yA l 2 - yC l) :=
        mul_le_mul_of_nonpos_right hsk (by linarith)
      have h2 : epsW l + s1W l * (yA l 2 - yC l) = s1W l * (yA l 2 - ydag l) := by
        have hsw := H.s1_w; unfold wW at hsw; linear_combination -hsw
      rw [hval] at h2
      rw [hg]
      have : epsW l * (3 / 2 + (tC l - kapP l) / uP l) = 3 / 2 * epsW l + epsW l * (tC l - kapP l) / uP l := by
        ring
      linarith
  rcases hc with ⟨hle, hu3, hpsi3⟩ | ⟨_, hle, hall⟩ | ⟨hge, hc8⟩
  · -- C7 regime: Psi is increasing in F, and F >= f3
    apply low (by linarith)
    rw [H.E3_eq] at hu3
    rw [H.E3_eq, H.eps3_eq] at hpsi3
    have hf3 := H.fArm3_le
    have hEle : Real.exp (fArm l 3) ≤ Real.exp (fstar l) := Real.exp_le_exp.mpr hf3
    have huu : uP l ≤ 1 + tC l - Real.exp (fArm l 3) := by unfold uP; linarith
    have hd : 0 ≤ tC l - kapP l := by rw [← H.kap_eq]; exact PBC.delta_nonneg ht.le (by linarith)
    have he3 : 2 * (fArm l 3 - fch l) ≤ epsW l := by unfold epsW; linarith
    have := psi_mono (D2 := Dj l 2) hd hu huu he3 heps.le
    linarith
  · -- the hand step on [t_D2, 1/2]
    apply low hle
    have := hall (epsW l) (Real.exp (fstar l)) heps (by unfold uP at hu; linarith)
    unfold uP; exact this
  · -- C8 regime, lam >= 2: h(y2) = eps + kappa (y2 - y_ch)
    have hup := hshape.up (yA l 2)
    have hy2c : yC l ≤ yA l 2 := by
      rw [hy2, hyc2, div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    rw [max_eq_right (by linarith)] at hup
    rw [hg]
    rw [← hy2, ← hyc2] at hc8
    linarith

/-- **the witness W* on [3/20, 1 + sqrt 5)** -/
theorem wstar_witness (h3 : 3 / 20 ≤ l) :
    Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hS l) := by
  have Sh := H.hS_shape
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
    · apply H.step_arm Sh H.S3 m h2 h4 _ y hy0 hy1
      rcases (by omega : m = 2 ∨ m = 3 ∨ m = 4) with e | e | e
      · subst e; push_cast; exact H.S6 h3
      · subst e
        rw [Sh.zero _ (by push_cast; exact H.S2)]
        have := H.gArm_nonneg 3 (by norm_num); push_cast at this ⊢; exact this
      · subst e
        have hy43 : yA l 4 ≤ yA l 3 := by
          unfold yA; apply one_div_le_one_div_of_le (by have := H.t_pos; positivity); have := H.t_pos; linarith
        rw [Sh.zero _ (by push_cast; exact le_trans hy43 H.S2)]
        have := H.gArm_nonneg 4 (by norm_num); push_cast at this ⊢; exact this
    · exact H.step_flat Sh (fun y => le_max_of_le_left (le_max_right _ _)) H.S4 m h5 y hy0 hy1

end PB

end

end LeanCherry
