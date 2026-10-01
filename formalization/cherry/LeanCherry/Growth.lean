/-
LeanCherry.Growth -- the bounds on M_n, and rho and the growth rate, in the cherry regime.
  Mn l n := max over trees G on Fin n of piL l G   (Finset.sup' over Finset.univ.filter IsTree; 0 if there is no tree)
  Mn_le : 1 + sqrt 5 <= l -> 1 <= n -> Mn l n <= (1 + l) (1 + l/2)^((n-1)/2)
  Mn_ge : 0 <= l -> 1 <= n -> (1 + l/2)^⌊(n-1)/2⌋ <= Mn l n          (witness: a root with ⌊(n-1)/2⌋ cherry legs, + a leaf if n even)
  rho_isGreatest : 1 + sqrt 5 <= l -> sqrt(1 + l/2) is the greatest element of {Tl l b ^ (1/|b|)} (attained by the cherry)
  Mn_rate : 1 + sqrt 5 <= l -> Mn l n ^ (1/n) -> sqrt(1 + l/2)
-/
import LeanCherry.Realize

open Finset Filter Topology

namespace LeanCherry

noncomputable section

open Classical in
/-- M_n(l): the largest lambda-weighted matching sum over trees on n labelled vertices -/
def Mn (l : ℝ) (n : ℕ) : ℝ :=
  if h : (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).Nonempty then
    (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).sup' h (fun G => piL l G)
  else 0

namespace Br

lemma sizeL_append : ∀ L1 L2 : List Br, sizeL (L1 ++ L2) = sizeL L1 + sizeL L2
  | [], L2 => by simp [sizeL]
  | c :: L1, L2 => by simp only [List.cons_append, sizeL]; rw [sizeL_append L1 L2]; omega

lemma sizeL_replicate (k : ℕ) (c : Br) : sizeL (List.replicate k c) = k * size c := by
  induction k with
  | zero => simp [sizeL]
  | succ k ih => rw [List.replicate_succ, sizeL, ih]; ring

lemma prodTl_append (l : ℝ) : ∀ L1 L2 : List Br, prodTl l (L1 ++ L2) = prodTl l L1 * prodTl l L2
  | [], L2 => by simp [prodTl]
  | c :: L1, L2 => by simp only [List.cons_append, prodTl]; rw [prodTl_append l L1 L2]; ring

lemma prodTl_replicate (l : ℝ) (k : ℕ) (c : Br) : prodTl l (List.replicate k c) = Tl l c ^ k := by
  induction k with
  | zero => simp [prodTl]
  | succ k ih => rw [List.replicate_succ, prodTl, ih]; ring

lemma Tl_leaf (l : ℝ) : Tl l (.node []) = 1 := by rw [Tl_node]; simp [prodTl, sumYl]

/-- the lower-bound witness: a root with j cherry legs and r extra leaves -/
def wit (j r : ℕ) : Br := .node (List.replicate j cherry ++ List.replicate r (.node []))

lemma wit_size (j r : ℕ) : size (wit j r) = 2 * j + r + 1 := by
  simp only [wit, size, sizeL_append, sizeL_replicate]
  simp [cherry, size, sizeL]; ring

lemma wit_ZTl {l : ℝ} (hl : 0 ≤ l) (j r : ℕ) : (1 + l / 2) ^ j ≤ ZTl l (wit j r) := by
  rw [wit, ZTl_node hl, prodTl_append, prodTl_replicate, prodTl_replicate, Tl_cherry, Tl_leaf, one_pow, mul_one]
  have hb : 0 ≤ (1 + l / 2) ^ j := pow_nonneg (by linarith) _
  have hf : 0 ≤ l * sumYl l (List.replicate j cherry ++ List.replicate r (Br.node [])) /
      ((List.replicate j cherry ++ List.replicate r (Br.node [])).length : ℝ) :=
    div_nonneg (mul_nonneg hl (sumYl_nonneg hl _)) (by positivity)
  nlinarith

end Br

open Classical in
lemma trees_nonempty {n : ℕ} (hn : 1 ≤ n) :
    (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).Nonempty := by
  obtain ⟨b, hb⟩ : ∃ b : Br, Br.size b = n := ⟨Br.wit 0 (n - 1), by rw [Br.wit_size]; omega⟩
  subst hb
  exact ⟨Br.HB b, mem_filter.mpr ⟨mem_univ _, Br.HB_isTree b⟩⟩

/-- upper bound -/
theorem Mn_le {l : ℝ} (hl : 1 + √5 ≤ l) {n : ℕ} (hn : 1 ≤ n) :
    Mn l n ≤ (1 + l) * (1 + l / 2) ^ (((n : ℝ) - 1) / 2) := by
  classical
  unfold Mn
  rw [dif_pos (trees_nonempty hn)]
  apply sup'_le
  intro G hG
  have := pi_lam_le_tree G hl (mem_filter.mp hG).2
  rwa [Fintype.card_fin] at this

/-- lower bound (floor exponent) -/
theorem Mn_ge {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) : (1 + l / 2) ^ ((n - 1) / 2) ≤ Mn l n := by
  classical
  set j := (n - 1) / 2
  set r := (n - 1) % 2
  have hsize : Br.size (Br.wit j r) = n := by rw [Br.wit_size]; omega
  have hle := Br.wit_ZTl hl j r
  have key : ∀ (b : Br) (hb : Br.size b = n), Br.ZTl l b ≤ Mn l n := by
    intro b hb
    subst hb
    unfold Mn
    rw [dif_pos (trees_nonempty hn)]
    obtain ⟨htree, hpi⟩ := Br.realize_br b
    rw [← hpi l]
    exact le_sup' (fun G => piL l G) (mem_filter.mpr ⟨mem_univ _, htree⟩)
  exact hle.trans (key _ hsize)

/-! ### rho and the growth rate -/

/-- rho at every l >= 1 + sqrt 5: sup over planted branches of T_b^(1/|b|) is sqrt(1 + l/2), attained by the cherry -/
theorem rho_isGreatest {l : ℝ} (hl : 1 + √5 ≤ l) :
    IsGreatest {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))} (√(1 + l / 2)) := by
  have hl0 : 0 ≤ l := by have := Real.sqrt_nonneg 5; linarith
  have hb : 0 < 1 + l / 2 := by linarith
  constructor
  · refine ⟨Br.cherry, ?_⟩
    rw [Br.Tl_cherry, Real.sqrt_eq_rpow]
    simp [Br.cherry, Br.size, Br.sizeL]
  · rintro x ⟨b, rfl⟩
    have hs : (0:ℝ) < Br.size b := by cases b; simp [Br.size]; positivity
    have h := Br.ceiling_cherry_regime l hl b
    calc Br.Tl l b ^ (1 / (Br.size b : ℝ))
        ≤ ((1 + l / 2) ^ ((Br.size b : ℝ) / 2)) ^ (1 / (Br.size b : ℝ)) :=
          Real.rpow_le_rpow (Br.Tl_pos hl0 b).le h (by positivity)
      _ = √(1 + l / 2) := by
          rw [← Real.rpow_mul hb.le, Real.sqrt_eq_rpow]; congr 1; field_simp

theorem rho_isLUB {l : ℝ} (hl : 1 + √5 ≤ l) :
    IsLUB {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))} (√(1 + l / 2)) :=
  (rho_isGreatest hl).isLUB

theorem rho_eq {l : ℝ} (hl : 1 + √5 ≤ l) :
    sSup {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))} = √(1 + l / 2) :=
  (rho_isGreatest hl).csSup_eq

/-- the growth rate of M_n -/
theorem Mn_rate {l : ℝ} (hl : 1 + √5 ≤ l) :
    Tendsto (fun n : ℕ => Mn l n ^ (1 / (n : ℝ))) atTop (𝓝 (√(1 + l / 2))) := by
  have hl0 : 0 ≤ l := by have := Real.sqrt_nonneg 5; linarith
  have hb : 0 < 1 + l / 2 := by linarith
  have hb1 : 0 < 1 + l := by linarith
  rw [Real.sqrt_eq_rpow]
  -- exponent sequences
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hup_e : Tendsto (fun n : ℕ => (((n : ℝ) - 1) / 2) * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
    have : (fun n : ℕ => (((n : ℝ) - 1) / 2) * (1 / (n : ℝ))) =ᶠ[atTop] (fun n : ℕ => 1 / 2 - (1 / 2) * (1 / (n : ℝ))) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [tendsto_congr' this]
    have := (tendsto_const_nhds (x := (1/2 : ℝ))).sub (hinv.const_mul (1 / 2))
    rw [mul_zero, sub_zero] at this; exact this
  have hlo_e : Tendsto (fun n : ℕ => (((n - 1) / 2 : ℕ) : ℝ) * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
    have hlow : Tendsto (fun n : ℕ => 1 / 2 - 1 * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
      have := (tendsto_const_nhds (x := (1/2 : ℝ))).sub (hinv.const_mul 1)
      rw [mul_zero, sub_zero] at this; exact this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup_e
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hfl : ((n : ℝ) - 2) / 2 ≤ (((n - 1) / 2 : ℕ) : ℝ) := by
        have h1 : n - 1 ≤ 2 * ((n - 1) / 2) + 1 := by omega
        have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
        have : ((n - 1 : ℕ) : ℝ) ≤ 2 * (((n - 1) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
        linarith
      rw [show (1 : ℝ) / 2 - 1 * (1 / (n : ℝ)) = (((n : ℝ) - 2) / 2) * (1 / (n : ℝ)) by field_simp]
      exact mul_le_mul_of_nonneg_right hfl (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hfl : (((n - 1) / 2 : ℕ) : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
        have h1 : 2 * ((n - 1) / 2) ≤ n - 1 := Nat.mul_div_le _ _
        have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
        have : 2 * (((n - 1) / 2 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
      exact mul_le_mul_of_nonneg_right hfl (by positivity)
  -- limits of the bounding sequences
  have hlower : Tendsto (fun n : ℕ => (1 + l / 2) ^ ((((n - 1) / 2 : ℕ) : ℝ) * (1 / (n : ℝ)))) atTop
      (𝓝 ((1 + l / 2) ^ (1 / 2 : ℝ))) :=
    tendsto_const_nhds.rpow hlo_e (Or.inl hb.ne')
  have hupper : Tendsto (fun n : ℕ => (1 + l) ^ (1 / (n : ℝ)) * (1 + l / 2) ^ ((((n : ℝ) - 1) / 2) * (1 / (n : ℝ))))
      atTop (𝓝 ((1 + l / 2) ^ (1 / 2 : ℝ))) := by
    have h1 : Tendsto (fun n : ℕ => (1 + l) ^ (1 / (n : ℝ))) atTop (𝓝 ((1 + l) ^ (0 : ℝ))) :=
      tendsto_const_nhds.rpow hinv (Or.inl hb1.ne')
    have h2 : Tendsto (fun n : ℕ => (1 + l / 2) ^ ((((n : ℝ) - 1) / 2) * (1 / (n : ℝ)))) atTop
        (𝓝 ((1 + l / 2) ^ (1 / 2 : ℝ))) := tendsto_const_nhds.rpow hup_e (Or.inl hb.ne')
    simpa using h1.mul h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hg := Mn_ge hl0 hn
    rw [Real.rpow_mul hb.le, Real.rpow_natCast]
    exact Real.rpow_le_rpow (pow_nonneg hb.le _) hg (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hg := Mn_le hl hn
    have hM0 : 0 ≤ Mn l n := le_trans (pow_nonneg hb.le _) (Mn_ge hl0 hn)
    calc Mn l n ^ (1 / (n : ℝ)) ≤ ((1 + l) * (1 + l / 2) ^ (((n : ℝ) - 1) / 2)) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hM0 hg (by positivity)
      _ = (1 + l) ^ (1 / (n : ℝ)) * (1 + l / 2) ^ ((((n : ℝ) - 1) / 2) * (1 / (n : ℝ))) := by
          rw [Real.mul_rpow hb1.le (Real.rpow_nonneg hb.le _), ← Real.rpow_mul hb.le]

end

end LeanCherry
