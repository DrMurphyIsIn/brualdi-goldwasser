/-
LeanCherry.WitnessExamples -- the witness definition is not vacuous.
 (i)  the trivial plain witness: A = ∅, I = [0,1], h ≡ 0, F = log(1 + l), for every l > 0;
 (ii) the leaf-exempt hinge at lam_c: A = {leaf}, I = [0, 1/2], h y = (phi log phi) max 0 (y - y_ch), F = log phi, tight at the
      cherry; through mt_main it re-derives the anchor (T_b <= phi^|b|) and rho(lam_c) = phi.
-/
import LeanCherry.Witness

open Finset

namespace LeanCherry

noncomputable section

open Classical

open Br

/-! ### (i) the trivial witness -/

theorem trivial_witness {l : ℝ} (hl : 0 < l) :
    Witness l (Real.log (1 + l)) ∅ (Set.Icc 0 1) (fun _ => 0) where
  lam_pos := hl
  I_ord := Set.ordConnected_Icc
  I_lo := fun y hy => ⟨hy.1.le, by linarith [hy.2]⟩
  I_hi := le_rfl
  HA_type := fun _ _ _ => by simp
  HA_m := fun _ hb => absurd hb (Set.notMem_empty _)
  H0 := fun _ ha => absurd ha (Set.notMem_empty _)
  convex := convexOn_const 0 (convex_Icc 0 1)
  bdd := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact le_rfl⟩
  leaf := fun _ => ⟨⟨by norm_num, le_rfl⟩, Real.log_nonneg (by linarith)⟩
  bell := by
    intro E m hE hcard _ ybar hy
    have hE0 : E = 0 := Multiset.eq_zero_of_forall_notMem (fun a ha => hE a ha)
    subst hE0
    simp only [Multiset.card_zero, Nat.cast_zero, zero_add] at hcard ⊢
    have hm : 0 < m := by omega
    obtain ⟨hy0, hy1⟩ := hy hm
    unfold Bellman
    simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero, Nat.cast_zero, zero_add, mul_zero, add_zero]
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hR0 : 0 ≤ l * ((m : ℝ) * ybar) / ((m : ℝ) + 1) := by positivity
    have hR1 : l * ((m : ℝ) * ybar) / ((m : ℝ) + 1) ≤ l := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hy1 hmR.le]
    have := Real.log_le_log (by linarith) (by linarith : 1 + l * ((m : ℝ) * ybar) / ((m : ℝ) + 1) ≤ 1 + l)
    linarith

/-! ### (ii) the hinge at lam_c -/

/-- the hinge potential h = -U -/
def hinge (y : ℝ) : ℝ := kap * max 0 (y - ych)

lemma U_eq_neg_hinge (y : ℝ) : U y = -hinge y := by
  unfold U hinge
  have hk := kap_pos
  rcases le_total y ych with h | h
  · rw [min_eq_left (by nlinarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right (by nlinarith), max_eq_right (by linarith)]; ring

lemma hinge_convex : ConvexOn ℝ (Set.Icc (0:ℝ) (1 / 2)) hinge := by
  refine ⟨convex_Icc _ _, fun x _ y _ a b ha hb hab => ?_⟩
  unfold hinge
  simp only [smul_eq_mul]
  have hk := kap_pos
  have h1 : a * x + b * y - ych = a * (x - ych) + b * (y - ych) := by linear_combination ych * hab
  have hmx : max 0 (a * x + b * y - ych) ≤ a * max 0 (x - ych) + b * max 0 (y - ych) := by
    apply max_le
    · positivity
    · rw [h1]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha) (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
  nlinarith [mul_le_mul_of_nonneg_left hmx hk.le]

lemma hinge_nonneg (y : ℝ) : 0 ≤ hinge y := mul_nonneg kap_pos.le (le_max_left _ _)

lemma typeOf_leaf_iff (A : Set Br) (b : Br) : typeOf A b = (0, 0) ↔ b = .node [] := by
  cases b with
  | node cs =>
    simp only [typeOf, Prod.mk.injEq, exE, nonE, Multiset.coe_eq_zero, Br.node.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      have := length_split (fun c => decide (c ∈ A)) cs
      rw [h1, List.length_nil, zero_add] at this
      have h2' : (cs.filter (fun c => !decide (c ∈ A))).length = 0 := by
        rw [← h2]; congr 2; funext c; simp
      rw [h2'] at this
      exact List.length_eq_zero_iff.mp this
    · rintro rfl; simp

lemma gB_cherry_lam : gB lam L cherry = 0 := by
  have h := ell_cherry
  unfold ell at h
  unfold gB
  rw [Tl_lam]; linarith

theorem hinge_witness : Witness lam L {Br.node []} (Set.Icc 0 (1 / 2)) hinge where
  lam_pos := lam_pos
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
    intro a ha; rw [Set.mem_singleton_iff] at ha; rw [ha, gB_leaf]; exact L_pos.le
  convex := hinge_convex
  bdd := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hinge_nonneg y⟩
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
    -- translate to the anchor step lemmas (U = -hinge)
    have hU : ∀ y, hinge y = -U y := fun y => by rw [U_eq_neg_hinge]; ring
    simp only [hU]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0, m >= 1
      have hm : 0 < m := by omega
      obtain ⟨ht0, ht1⟩ := hy hm
      have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hmcase : (m : ℝ) = 1 ∨ (m : ℝ) = 2 ∨ 3 ≤ (m : ℝ) := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ 3 ≤ m) with e | e | e
        · left; exact_mod_cast e
        · right; left; exact_mod_cast e
        · right; right; exact_mod_cast e
      have hstep := step_k_zero (m : ℝ) ybar hm1 hmcase ht0 ht1
      rw [hk0]; push_cast
      simp only [zero_add, zero_mul] at hstep ⊢
      linarith
    · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have hkcase : (k : ℝ) = 1 ∨ 2 ≤ (k : ℝ) := by
        rcases (by omega : k = 1 ∨ 2 ≤ k) with e | e
        · left; exact_mod_cast e
        · right; exact_mod_cast e
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · have hstep := step_k_pos (k : ℝ) 0 0 hk1 le_rfl le_rfl (by norm_num) hkcase
        rw [hm0]; push_cast
        simp only [zero_mul, mul_zero, add_zero] at hstep ⊢
        linarith
      · obtain ⟨ht0, ht1⟩ := hy hm
        have hstep := step_k_pos (k : ℝ) (m : ℝ) ybar hk1 (by positivity) ht0 ht1 hkcase
        linarith

theorem hinge_tight : Tight lam L := ⟨cherry, gB_cherry_lam⟩

lemma exp_L : Real.exp L = φ := by unfold L; exact Real.exp_log φ_pos

/-- the anchor re-derived through the witness theorem (a) -/
theorem ceiling_at_lam_c_via_witness (b : Br) : T b ≤ φ ^ size b := by
  have h := hinge_witness.mt_main_a.2.2.2 b
  rw [Tl_lam, show L * (size b : ℝ) = (size b : ℝ) * L by ring, Real.exp_nat_mul, exp_L] at h
  exact h

/-- rho(lam_c) = phi through the witness theorem (c) -/
theorem rho_lam_c_via_witness : rhoB lam = φ := by
  rw [(hinge_witness.mt_main_c gB_cherry_lam).1, exp_L]

end

end LeanCherry
