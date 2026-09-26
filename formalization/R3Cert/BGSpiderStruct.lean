/-
  R3Cert.BGSpiderStruct -- `StructProp 492`: every F-maximizer of the two-level spider family on at least
  492 vertices lies in the candidate set `Cand` (<= 8 cherries, arms in {4,5,6}, never both 4 and 6,
  <= 10 fours, <= 10 sixes).  Part L1 of the spider certificate (2026-09-25).

  Method (proof/docs/BG_SPIDER_STRUCT_2026-09-25.md).  Two tools:
    * local exchanges `old -> new` of equal cost inside `old ++ rest`: the product factor of `rest`
      cancels, and the move wins iff  No * Ln < gamma * Nn * Lo , a quadratic inequality in
      D0 = |rest| and R0 = sum_rest r (every exchange first checked in exact arithmetic);
    * a global comparison with the rule winner `W n`:  F(l)^2 <= (1+hi)^2 (3/2)^(n-1) K^(#arms)
      against  F(W n)^2 >= (10/9)^2 (3/2)^(n-1) (529/486)^37 .
  Steps, for an F-maximizer l with nv l >= 492:
    1. |l| >= 3                      (global, K = 32/27, hi = 1, #arms <= 2);
    2. no arm A_j with j >= 13        (split A_{u+13} -> A_{u+2} + 2 A_5, any rest with r <= 1/3);
    3. no arm A_j with 7 <= j <= 12   (11 A_j -> (2j+1) A_5 bounds each size by 10, balance leaves two
                                       sizes, so #arms <= 20; then global with K = h(A_12), hi = 1/3);
    4. at most 8 cherries             (9 P -> 2 A_4, needs |rest| >= 27; |l| >= 38 since costs <= 13);
    5. no arm A_j with j <= 3         (then |l| >= 55 from costs <= 9, but counts give |l| <= 49);
    6. count A_4 <= 10 (11 A_4 -> 9 A_5, |rest| >= 27, r >= 1/9) and count A_6 <= 10 (11 A_6 -> 13 A_5).
  No `sorry`, no `native_decide`; axioms: propext, Classical.choice, Quot.sound.
  `conjecture1_proved = False` (this is the optimization inside one explicit family).
-/
import Mathlib
import R3Cert.BGSpiderRule

namespace R3Cert
namespace BGSpiderStruct

open BGSpiderOpt BGSpiderRule

/-! ### Exchange framework -/

theorem F_append (x rest : List Child) :
    F (x ++ rest) = (x.map Child.g).prod * (rest.map Child.g).prod *
      (1 + ((x.map Child.r).sum + (rest.map Child.r).sum) / ((x.length : ℚ) + rest.length)) := by
  simp only [F, List.map_append, List.prod_append, List.sum_append, List.length_append]
  push_cast
  ring

/-- An exchange `old → new` (inside `old ++ rest`) raises `F` once the product gains a factor `γ` and the
bracket inequality holds. -/
theorem F_exchange_lt (old new rest : List Child) (γ : ℚ)
    (hg : γ * (old.map Child.g).prod ≤ (new.map Child.g).prod) (ho : old ≠ []) (hn : new ≠ [])
    (h : ((old.length : ℚ) + rest.length + (old.map Child.r).sum + (rest.map Child.r).sum) *
          ((new.length : ℚ) + rest.length) <
        γ * ((new.length : ℚ) + rest.length + (new.map Child.r).sum + (rest.map Child.r).sum) *
          ((old.length : ℚ) + rest.length)) :
    F (old ++ rest) < F (new ++ rest) := by
  rw [F_append, F_append]
  set Go := (old.map Child.g).prod
  set Gn := (new.map Child.g).prod
  set P := (rest.map Child.g).prod
  set Ro := (old.map Child.r).sum
  set Rn := (new.map Child.r).sum
  set R0 := (rest.map Child.r).sum
  set L := (rest.length : ℚ)
  have hGo : 0 < Go := prod_g_pos old
  have hP : 0 < P := prod_g_pos rest
  have hR0 : 0 ≤ R0 := sum_r_nonneg rest
  have hRn : 0 ≤ Rn := sum_r_nonneg new
  have hL : 0 ≤ L := by positivity
  have hlo : (1 : ℚ) ≤ old.length := by exact_mod_cast List.length_pos_iff.mpr ho
  have hln : (1 : ℚ) ≤ new.length := by exact_mod_cast List.length_pos_iff.mpr hn
  have hLo : 0 < (old.length : ℚ) + L := by linarith
  have hLn : 0 < (new.length : ℚ) + L := by linarith
  have e1 : Go * P * (1 + (Ro + R0) / ((old.length : ℚ) + L)) =
      Go * P * (((old.length : ℚ) + L + Ro + R0) / ((old.length : ℚ) + L)) := by
    field_simp; ring
  have e2 : Gn * P * (1 + (Rn + R0) / ((new.length : ℚ) + L)) =
      Gn * P * (((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L)) := by
    field_simp; ring
  rw [e1, e2]
  have hNn : 0 ≤ ((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L) := by positivity
  have step : γ * Go * P * (((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L)) ≤
      Gn * P * (((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L)) := by
    have := mul_le_mul_of_nonneg_right hg (mul_nonneg hP.le hNn)
    nlinarith [this]
  refine lt_of_lt_of_le ?_ step
  have key : ((old.length : ℚ) + L + Ro + R0) / ((old.length : ℚ) + L) <
      γ * (((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L)) := by
    rw [div_lt_iff₀ hLo, mul_div_assoc', div_mul_eq_mul_div, lt_div_iff₀ hLn]
    nlinarith [h]
  have hGP : 0 < Go * P := mul_pos hGo hP
  calc Go * P * (((old.length : ℚ) + L + Ro + R0) / ((old.length : ℚ) + L))
      < Go * P * (γ * (((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L))) :=
        mul_lt_mul_of_pos_left key hGP
    _ = γ * Go * P * (((new.length : ℚ) + L + Rn + R0) / ((new.length : ℚ) + L)) := by ring

/-- If `old` is a sub-multiset of `l` and replacing it by `new` (same total cost) raises `F` for every
possible remainder, then `l` is not a maximizer. -/
theorem not_isMax_of_exch {l old new : List Child} (hsub : old.Sublist l)
    (hcost : (old.map Child.cost).sum = (new.map Child.cost).sum)
    (hlt : ∀ rest : List Child, (∀ c ∈ rest, c ∈ l) → rest.length + old.length = l.length →
      F (old ++ rest) < F (new ++ rest)) : ¬ IsMax l := by
  intro hmax
  obtain ⟨rest, hp⟩ := hsub.exists_perm_append
  have hmem : ∀ c ∈ rest, c ∈ l := fun c hc => hp.symm.subset (List.mem_append_right _ hc)
  have hlen : rest.length + old.length = l.length := by
    rw [hp.length_eq, List.length_append]; omega
  have hnv : nv (new ++ rest) = nv l := by
    rw [nv_perm hp]
    simp only [nv, List.map_append, List.sum_append, hcost]
  have h1 := hmax _ hnv
  rw [F_perm hp] at h1
  exact absurd (hlt rest hmem hlen) (not_lt.mpr h1)

theorem r_le_one (c : Child) : c.r ≤ 1 := by
  cases c with
  | cherry => norm_num [Child.r]
  | arm j =>
    simp only [Child.r, bb]
    rw [div_le_one (by positivity)]
    have : (0 : ℚ) ≤ j := by positivity
    linarith

/-- Bounds on the `r`-sum of a list from elementwise bounds. -/
theorem sum_r_bounds (rest : List Child) (lo hi : ℚ)
    (h : ∀ c ∈ rest, lo ≤ c.r ∧ c.r ≤ hi) :
    lo * rest.length ≤ (rest.map Child.r).sum ∧ (rest.map Child.r).sum ≤ hi * rest.length := by
  induction rest with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    constructor <;> nlinarith [ha.1, ha.2, ht.1, ht.2]

/-- Replicate form of an exchange: `a` copies of `c` become `b` copies of `d`. -/
theorem rep_exch_lt (c d : Child) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (γ : ℚ)
    (hg : γ * c.g ^ a ≤ d.g ^ b) (rest : List Child)
    (h : ((a : ℚ) + rest.length + a * c.r + (rest.map Child.r).sum) * ((b : ℚ) + rest.length) <
      γ * ((b : ℚ) + rest.length + b * d.r + (rest.map Child.r).sum) * ((a : ℚ) + rest.length)) :
    F (List.replicate a c ++ rest) < F (List.replicate b d ++ rest) := by
  apply F_exchange_lt _ _ _ γ
  · simpa [List.map_replicate, List.prod_replicate] using hg
  · simp; omega
  · simp; omega
  · simpa [List.map_replicate, List.sum_replicate, nsmul_eq_mul] using h

/-- Counting form: a maximizer contains fewer than `k` copies of `c` when `k` copies can be exchanged
profitably for `new`. -/
theorem count_lt_of_exch {l : List Child} (hmax : IsMax l) (c : Child) (k : ℕ) (new : List Child)
    (hcost : k * c.cost = (new.map Child.cost).sum)
    (hlt : ∀ rest : List Child, (∀ x ∈ rest, x ∈ l) → rest.length + k = l.length →
      F (List.replicate k c ++ rest) < F (new ++ rest)) : l.count c < k := by
  by_contra hcon
  have hsub : (List.replicate k c).Sublist l := List.replicate_sublist_iff.mpr (by omega)
  refine not_isMax_of_exch (new := new) hsub ?_ ?_ hmax
  · rw [cost_sum_replicate, hcost]
  · intro rest hm hl
    simp only [List.length_replicate] at hl
    exact hlt rest hm hl

/-! ### The exchange inequalities (validated in exact arithmetic first) -/

/-- `11 A_j → (2j+1) A_5` for `j ∈ {1,2,3,7,…,12}`: profitable for every remainder. -/
theorem exch_arm_lt (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12)
    (rest : List Child) :
    F (List.replicate 11 (Child.arm j) ++ rest) < F (List.replicate (2 * j + 1) (Child.arm 5) ++ rest) := by
  have hb := sum_r_bounds rest 0 1 (fun c _ => ⟨r_nonneg c, r_le_one c⟩)
  set X := (rest.length : ℚ)
  set Y := (rest.map Child.r).sum
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by linarith [hb.1]
  have hYX : Y ≤ X := by linarith [hb.2]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine rep_exch_lt _ _ 11 3 (by norm_num) (by norm_num) (1937 / 1000)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 5 (by norm_num) (by norm_num) (158 / 125)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 7 (by norm_num) (by norm_num) (537 / 500)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 15 (by norm_num) (by norm_num) (1051 / 1000)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 17 (by norm_num) (by norm_num) (11 / 10)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 19 (by norm_num) (by norm_num) (1161 / 1000)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 21 (by norm_num) (by norm_num) (1231 / 1000)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 23 (by norm_num) (by norm_num) (164 / 125)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]
  · refine rep_exch_lt _ _ 11 25 (by norm_num) (by norm_num) (1403 / 1000)
      (by norm_num [Child.g, alpha]) rest ?_
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]

/-- `11 A_6 → 13 A_5` when every remaining child has `r ≤ 1/3`. -/
theorem exch_six_lt (rest : List Child) (hr : ∀ c ∈ rest, c.r ≤ 1 / 3) :
    F (List.replicate 11 (Child.arm 6) ++ rest) < F (List.replicate 13 (Child.arm 5) ++ rest) := by
  have hb := sum_r_bounds rest 0 (1 / 3) (fun c hc => ⟨r_nonneg c, hr c hc⟩)
  set X := (rest.length : ℚ)
  set Y := (rest.map Child.r).sum
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by linarith [hb.1]
  have hYX : 3 * Y ≤ X := by linarith [hb.2]
  refine rep_exch_lt _ _ 11 13 (by norm_num) (by norm_num) (1271 / 1250)
    (by norm_num [Child.g, alpha]) rest ?_
  norm_num [Child.r, bb]
  nlinarith [mul_nonneg hX hY, mul_nonneg hX (sub_nonneg.2 hYX), mul_nonneg hX hX]

/-- `11 A_4 → 9 A_5` when the remainder has at least 27 children, all with `r ≥ 1/9`. -/
theorem exch_four_lt (rest : List Child) (hr : ∀ c ∈ rest, 1 / 9 ≤ c.r) (hlen : 27 ≤ rest.length) :
    F (List.replicate 11 (Child.arm 4) ++ rest) < F (List.replicate 9 (Child.arm 5) ++ rest) := by
  have hb := sum_r_bounds rest (1 / 9) 1 (fun c hc => ⟨hr c hc, r_le_one c⟩)
  set X := (rest.length : ℚ)
  set Y := (rest.map Child.r).sum
  have hX : 27 ≤ X := by simp only [X]; exact_mod_cast hlen
  have hY : X ≤ 9 * Y := by linarith [hb.1]
  have hYX : Y ≤ X := by linarith [hb.2]
  refine rep_exch_lt _ _ 11 9 (by norm_num) (by norm_num) (10113 / 10000)
    (by norm_num [Child.g, alpha]) rest ?_
  norm_num [Child.r, bb]
  nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hY), mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hYX),
    mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hX)]

/-- `9 P → 2 A_4` when the remainder has at least 27 children, all with `r ≥ 1/9`. -/
theorem exch_cherry_lt (rest : List Child) (hr : ∀ c ∈ rest, 1 / 9 ≤ c.r) (hlen : 27 ≤ rest.length) :
    F (List.replicate 9 Child.cherry ++ rest) < F (List.replicate 2 (Child.arm 4) ++ rest) := by
  have hb := sum_r_bounds rest (1 / 9) 1 (fun c hc => ⟨hr c hc, r_le_one c⟩)
  set X := (rest.length : ℚ)
  set Y := (rest.map Child.r).sum
  have hX : 27 ≤ X := by simp only [X]; exact_mod_cast hlen
  have hY : X ≤ 9 * Y := by linarith [hb.1]
  have hYX : Y ≤ X := by linarith [hb.2]
  refine rep_exch_lt _ _ 9 2 (by norm_num) (by norm_num) (1069 / 1000)
    (by norm_num [Child.g, alpha]) rest ?_
  norm_num [Child.r, bb]
  nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hY), mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hYX),
    mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hX)]

/-! ### Splitting a long arm: `A_{u+13} → A_{u+2} + 2 A_5` -/

/-- The split polynomial at `Y = 0` (all coefficients positive). -/
theorem split_D0_pos (u m : ℕ) :
    0 < 15824*(m:ℚ)^2*(u:ℚ)^3 + 308568*(m:ℚ)^2*(u:ℚ)^2 + 846285*(m:ℚ)^2*(u:ℚ) + 322828*(m:ℚ)^2 +
      114080*(m:ℚ)*(u:ℚ)^3 + 2236428*(m:ℚ)*(u:ℚ)^2 + 9353847*(m:ℚ)*(u:ℚ) + 11182600*(m:ℚ) +
      98256*(u:ℚ)^3 + 1659588*(u:ℚ)^2 + 6964998*(u:ℚ) + 8646528 := by
  positivity

/-- The split polynomial at `Y = X/3`. -/
theorem split_E_pos (u : ℕ) (X : ℚ) (hX : 0 ≤ X) :
    0 < 63296*X^2*(u:ℚ)^3/3 + 411424*X^2*(u:ℚ)^2 + 1128380*X^2*(u:ℚ) + 1291312*X^2/3 +
      368*X*(u:ℚ)^3/3 + 14260*X*(u:ℚ)^2 - 774502*X*(u:ℚ) - 6705512*X/3 + 98256*(u:ℚ)^3 +
      1659588*(u:ℚ)^2 + 6964998*(u:ℚ) + 8646528 := by
  have hu : (0 : ℚ) ≤ u := by positivity
  have h1 : 0 ≤ (u : ℚ) * (1128380 * X ^ 2 - 774502 * X + 6964998) := by
    apply mul_nonneg hu; nlinarith [sq_nonneg (X - 1 / 3)]
  have h2 : 0 < 1291312 * X ^ 2 / 3 - 6705512 * X / 3 + 8646528 := by nlinarith [sq_nonneg (X - 13 / 5)]
  have h3 : 0 ≤ 63296*X^2*(u:ℚ)^3/3 + 411424*X^2*(u:ℚ)^2 + 368*X*(u:ℚ)^3/3 + 14260*X*(u:ℚ)^2 +
      98256*(u:ℚ)^3 + 1659588*(u:ℚ)^2 := by positivity
  nlinarith [h1, h2, h3]

/-- **Split.**  A long arm `A_{u+13}` is always worse than `A_{u+2}` plus two `A_5`, provided every other
child has `r ≤ 1/3`. -/
theorem exch_split_lt (u : ℕ) (rest : List Child) (hr : ∀ c ∈ rest, c.r ≤ 1 / 3) :
    F ([Child.arm (u + 13)] ++ rest) < F ([Child.arm (u + 2), Child.arm 5, Child.arm 5] ++ rest) := by
  have hb := sum_r_bounds rest 0 (1 / 3) (fun c hc => ⟨r_nonneg c, hr c hc⟩)
  have hXm : (0 : ℚ) ≤ rest.length := by positivity
  have hu : (0 : ℚ) ≤ u := by positivity
  set X := (rest.length : ℚ) with hXdef
  set Y := (rest.map Child.r).sum
  have hY : 0 ≤ Y := by linarith [hb.1]
  have hYX : 3 * Y ≤ X := by linarith [hb.2]
  set γ : ℚ := 529 / 486 * ((4 * (u : ℚ) + 11) * ((u : ℚ) + 14)) / (((u : ℚ) + 3) * (4 * (u : ℚ) + 55))
    with hγ
  have hg : γ * (Child.arm (u + 13)).g = (Child.arm (u + 2)).g * ((Child.arm 5).g * (Child.arm 5).g) := by
    simp only [Child.g, alpha, hγ]
    rw [show u + 13 = (u + 2) + 11 by ring, pow_add]
    push_cast
    field_simp
    ring
  -- the polynomial inequality
  set Dd : ℚ := (15824*X^2*(u:ℚ)^3 + 308568*X^2*(u:ℚ)^2 + 846285*X^2*(u:ℚ) + 322828*X^2 +
      114080*X*(u:ℚ)^3 + 2236428*X*(u:ℚ)^2 + 9353847*X*(u:ℚ) + 11182600*X +
      98256*(u:ℚ)^3 + 1659588*(u:ℚ)^2 + 6964998*(u:ℚ) + 8646528) +
    Y * (15824*X*(u:ℚ)^3 + 308568*X*(u:ℚ)^2 + 846285*X*(u:ℚ) + 322828*X - 341872*(u:ℚ)^3 -
      6666504*(u:ℚ)^2 - 30385047*(u:ℚ) - 40253312) with hDd
  have hD0 := split_D0_pos u rest.length
  have hE := split_E_pos u X hXm
  rw [← hXdef] at hD0
  have hDd : 0 < Dd := by
    rcases eq_or_lt_of_le hXm with h0 | hpos
    · have hY0 : Y = 0 := by linarith
      rw [hDd, hY0, ← h0]; rw [← h0] at hD0; linarith
    · have key : X * Dd = (X - 3 * Y) *
          (15824*X^2*(u:ℚ)^3 + 308568*X^2*(u:ℚ)^2 + 846285*X^2*(u:ℚ) + 322828*X^2 +
            114080*X*(u:ℚ)^3 + 2236428*X*(u:ℚ)^2 + 9353847*X*(u:ℚ) + 11182600*X +
            98256*(u:ℚ)^3 + 1659588*(u:ℚ)^2 + 6964998*(u:ℚ) + 8646528) +
          3 * Y * (63296*X^2*(u:ℚ)^3/3 + 411424*X^2*(u:ℚ)^2 + 1128380*X^2*(u:ℚ) + 1291312*X^2/3 +
            368*X*(u:ℚ)^3/3 + 14260*X*(u:ℚ)^2 - 774502*X*(u:ℚ) - 6705512*X/3 + 98256*(u:ℚ)^3 +
            1659588*(u:ℚ)^2 + 6964998*(u:ℚ) + 8646528) := by
        rw [hDd]; ring
      have hA : 0 ≤ X - 3 * Y := by linarith
      have hsum : 0 < X * Dd := by
        rw [key]
        rcases eq_or_lt_of_le hA with hA0 | hA1
        · have hYp : 0 < Y := by linarith
          nlinarith [mul_pos hYp hE, mul_nonneg hA hD0.le]
        · nlinarith [mul_pos hA1 hD0, mul_nonneg hY hE.le]
      exact pos_of_mul_pos_right hsum hpos.le
  have hineq : (1 + X + bb (u + 13) + Y) * (3 + X) <
      γ * (3 + X + (bb (u + 2) + (bb 5 + bb 5)) + Y) * (1 + X) := by
    rw [← sub_pos]
    have hN : 0 < 486 * 23 * ((u : ℚ) + 3) * (4 * (u : ℚ) + 55) * (4 * (u : ℚ) + 11) := by positivity
    have hid : (γ * (3 + X + (bb (u + 2) + (bb 5 + bb 5)) + Y) * (1 + X) -
        (1 + X + bb (u + 13) + Y) * (3 + X)) *
        (486 * 23 * ((u : ℚ) + 3) * (4 * (u : ℚ) + 55) * (4 * (u : ℚ) + 11)) = Dd := by
      simp only [hγ, bb]
      push_cast
      field_simp
      ring
    by_contra hneg
    rw [not_lt] at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hN.le
    rw [hid] at this
    linarith
  refine F_exchange_lt _ _ _ γ ?_ (by simp) (by simp) ?_
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hg]
  · simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Child.r]
    push_cast
    nlinarith [hineq]

/-! ### Global comparison with the rule winner -/

/-- `h(c) = g(c)^2 / (3/2)^cost(c)`: `1` for a cherry, `(2/3) α_j^2` for an arm. -/
def hh : Child → ℚ
  | Child.cherry => 1
  | Child.arm j => alpha j ^ 2 * (2 / 3)

theorem hh_nonneg (c : Child) : 0 ≤ hh c := by
  cases c with
  | cherry => norm_num [hh]
  | arm j => simp only [hh]; positivity

theorem g_sq (c : Child) : c.g ^ 2 = (3 / 2 : ℚ) ^ c.cost * hh c := by
  cases c with
  | cherry => norm_num [Child.g, Child.cost, hh]
  | arm j =>
    simp only [Child.g, Child.cost, hh]
    rw [mul_pow, ← pow_mul, pow_succ]
    ring

theorem prod_g_sq (l : List Child) :
    (l.map Child.g).prod ^ 2 = (3 / 2 : ℚ) ^ (l.map Child.cost).sum * (l.map hh).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, mul_pow, ih, g_sq, pow_add]
    ring

theorem prod_hh_nonneg (l : List Child) : 0 ≤ (l.map hh).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.prod_cons]; exact mul_nonneg (hh_nonneg a) ih

theorem prod_hh_le (K : ℚ) (hK : 1 ≤ K) (l : List Child)
    (h : ∀ j, Child.arm j ∈ l → hh (Child.arm j) ≤ K) :
    (l.map hh).prod ≤ K ^ (l.length - l.count Child.cherry) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have hct := List.count_le_length (a := Child.cherry) (l := t)
    cases a with
    | cherry =>
      simp only [List.map_cons, List.prod_cons, hh, one_mul, List.length_cons, List.count_cons_self]
      rwa [show t.length + 1 - (t.count Child.cherry + 1) = t.length - t.count Child.cherry by omega]
    | arm j =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [List.count_cons_of_ne (by simp)]
      rw [show t.length + 1 - t.count Child.cherry = (t.length - t.count Child.cherry) + 1 by omega,
        pow_succ]
      have hj := h j (by simp)
      have hK0 : 0 ≤ K ^ (t.length - t.count Child.cherry) := by positivity
      calc hh (Child.arm j) * (t.map hh).prod ≤ K * K ^ (t.length - t.count Child.cherry) :=
            mul_le_mul hj ih' (prod_hh_nonneg t) (by linarith)
        _ = K ^ (t.length - t.count Child.cherry) * K := by ring

theorem F_pos (l : List Child) : 0 < F l := by
  unfold F
  apply mul_pos (prod_g_pos l)
  have := sum_r_nonneg l
  positivity

theorem F_sq_le (l : List Child) (hi : ℚ) (hhi : 0 ≤ hi) (h : ∀ c ∈ l, c.r ≤ hi) :
    F l ^ 2 ≤ (1 + hi) ^ 2 * (l.map Child.g).prod ^ 2 := by
  have hb := sum_r_bounds l 0 hi (fun c hc => ⟨r_nonneg c, h c hc⟩)
  have hR := sum_r_nonneg l
  unfold F
  set P := (l.map Child.g).prod
  set R := (l.map Child.r).sum
  set L := (l.length : ℚ)
  have hB0 : 0 ≤ R / L := by positivity
  have hB1 : R / L ≤ hi := by
    rcases eq_or_lt_of_le (show (0 : ℚ) ≤ L by positivity) with h0 | hpos
    · rw [← h0, div_zero]; exact hhi
    · rw [div_le_iff₀ hpos]; linarith [hb.2]
  rw [mul_pow, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by linarith) (by linarith)

theorem w5_ge (n : ℕ) (hn : 492 ≤ n) : 37 ≤ w5 n := by
  have hs : sres n < 11 := Nat.mod_lt _ (by norm_num)
  unfold w5 w4 w6
  simp only
  split_ifs <;> omega

theorem hh_W_ge (n : ℕ) (hn : 492 ≤ n) : (529 / 486 : ℚ) ^ 37 ≤ ((W n).map hh).prod := by
  have e4 : hh (Child.arm 4) = 722 / 675 := by norm_num [hh, alpha]
  have e5 : hh (Child.arm 5) = 529 / 486 := by norm_num [hh, alpha]
  have e6 : hh (Child.arm 6) = 54 / 49 := by norm_num [hh, alpha]
  simp only [W, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, e4, e5, e6]
  have h1 : (1 : ℚ) ≤ (722 / 675) ^ w4 n := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℚ) ≤ (54 / 49) ^ w6 n := one_le_pow₀ (by norm_num)
  have h3 : (529 / 486 : ℚ) ^ 37 ≤ (529 / 486) ^ w5 n := pow_le_pow_right₀ (by norm_num) (w5_ge n hn)
  have h4 : (0 : ℚ) ≤ (529 / 486) ^ w5 n := by positivity
  calc (529 / 486 : ℚ) ^ 37 ≤ 1 * 1 * (529 / 486) ^ w5 n := by linarith
    _ ≤ (722 / 675) ^ w4 n * (54 / 49) ^ w6 n * (529 / 486) ^ w5 n := by
      apply mul_le_mul_of_nonneg_right _ h4
      exact mul_le_mul h1 h2 (by norm_num) (by positivity)

theorem F_W_sq (n : ℕ) (hn : 492 ≤ n) :
    (10 / 9 : ℚ) ^ 2 * ((3 / 2 : ℚ) ^ (n - 1) * (529 / 486) ^ 37) ≤ F (W n) ^ 2 := by
  have hnv := nv_W n hn
  have hcost : ((W n).map Child.cost).sum = n - 1 := by simp only [nv] at hnv; omega
  have hrW : ∀ c ∈ W n, 1 / 9 ≤ c.r := by
    intro c hc
    simp only [W, List.mem_append, List.mem_replicate] at hc
    rcases hc with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> norm_num [Child.r, bb]
  have hne : (W n).length ≠ 0 := by
    intro h0
    rw [List.length_eq_zero_iff] at h0
    rw [h0] at hnv; simp [nv] at hnv; omega
  have hb := sum_r_bounds (W n) (1 / 9) 1 (fun c hc => ⟨hrW c hc, r_le_one c⟩)
  have hL : (0 : ℚ) < (W n).length := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hB : (10 / 9 : ℚ) ≤ 1 + ((W n).map Child.r).sum / (W n).length := by
    rw [show (10 / 9 : ℚ) = 1 + 1 / 9 by norm_num]
    have : (1 / 9 : ℚ) ≤ ((W n).map Child.r).sum / (W n).length := by
      rw [le_div_iff₀ hL]; linarith [hb.1]
    linarith
  have hP := prod_g_sq (W n)
  rw [hcost] at hP
  have hH := hh_W_ge n hn
  unfold F
  rw [mul_pow, hP]
  have hpow : (0 : ℚ) < (3 / 2) ^ (n - 1) := by positivity
  have hB2 : (10 / 9 : ℚ) ^ 2 ≤ (1 + ((W n).map Child.r).sum / (W n).length) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hB 2
  calc (10 / 9 : ℚ) ^ 2 * ((3 / 2) ^ (n - 1) * (529 / 486) ^ 37)
      ≤ (1 + ((W n).map Child.r).sum / (W n).length) ^ 2 * ((3 / 2) ^ (n - 1) * ((W n).map hh).prod) := by
        apply mul_le_mul hB2 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hH hpow.le
    _ = (3 / 2) ^ (n - 1) * ((W n).map hh).prod * (1 + ((W n).map Child.r).sum / (W n).length) ^ 2 := by
        ring

/-- **Global comparison.**  A configuration whose product and bracket are too small cannot be a maximizer. -/
theorem global_contra {l : List Child} (hmax : IsMax l) (hn : 492 ≤ nv l) (hi K : ℚ) (hhi : 0 ≤ hi)
    (hK : 1 ≤ K) (m : ℕ) (hr : ∀ c ∈ l, c.r ≤ hi) (hhK : ∀ j, Child.arm j ∈ l → hh (Child.arm j) ≤ K)
    (hm : l.length - l.count Child.cherry ≤ m)
    (hnum : (1 + hi) ^ 2 * K ^ m < (10 / 9) ^ 2 * (529 / 486) ^ 37) : False := by
  set n := nv l with hndef
  have hWle : F (W n) ≤ F l := hmax _ (nv_W n hn)
  have hW := F_W_sq n hn
  have hFl := F_sq_le l hi hhi hr
  have hP := prod_g_sq l
  have hcost : (l.map Child.cost).sum = n - 1 := by simp only [hndef, nv]; omega
  rw [hcost] at hP
  have hH := prod_hh_le K hK l hhK
  have hKm : K ^ (l.length - l.count Child.cherry) ≤ K ^ m := pow_le_pow_right₀ hK hm
  have hpow : (0 : ℚ) < (3 / 2) ^ (n - 1) := by positivity
  have h1 : F l ^ 2 ≤ (1 + hi) ^ 2 * ((3 / 2) ^ (n - 1) * K ^ m) := by
    rw [hP] at hFl
    refine hFl.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (hH.trans hKm) hpow.le
  have h2 : (1 + hi) ^ 2 * ((3 / 2) ^ (n - 1) * K ^ m) <
      (10 / 9 : ℚ) ^ 2 * ((3 / 2 : ℚ) ^ (n - 1) * (529 / 486) ^ 37) := by
    have := mul_lt_mul_of_pos_left hnum hpow
    nlinarith [this]
  have h3 : F (W n) ^ 2 ≤ F l ^ 2 := pow_le_pow_left₀ (F_pos _).le hWle 2
  linarith

/-! ### Small facts -/

theorem sum_cost_le (l : List Child) (B : ℕ) (h : ∀ c ∈ l, c.cost ≤ B) :
    (l.map Child.cost).sum ≤ B * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem len_le_three (l : List Child) (a b : ℕ)
    (h : ∀ c ∈ l, c = Child.cherry ∨ c = Child.arm a ∨ c = Child.arm b) :
    l.length ≤ l.count Child.cherry + l.count (Child.arm a) + l.count (Child.arm b) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have e1 := List.count_le_count_cons (a := Child.cherry) (b := x) (l := t)
    have e2 := List.count_le_count_cons (a := Child.arm a) (b := x) (l := t)
    have e3 := List.count_le_count_cons (a := Child.arm b) (b := x) (l := t)
    rw [List.length_cons]
    rcases h x (by simp) with rfl | rfl | rfl
    · rw [List.count_cons_self] at e1 ⊢; omega
    · rw [List.count_cons_self] at e2 ⊢; omega
    · rw [List.count_cons_self] at e3 ⊢; omega

theorem len_le_five (l : List Child) (h : ∀ c ∈ l, c = Child.cherry ∨ ∃ k, k ≤ 4 ∧ c = Child.arm k) :
    l.length ≤ l.count Child.cherry + l.count (Child.arm 0) + l.count (Child.arm 1) +
      l.count (Child.arm 2) + l.count (Child.arm 3) + l.count (Child.arm 4) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    rcases h x (by simp) with rfl | ⟨k, hk, rfl⟩
    · simp only [List.count_cons, List.length_cons, beq_iff_eq]; simp; omega
    · interval_cases k <;> simp only [List.count_cons, List.length_cons, beq_iff_eq] <;> simp <;> omega

theorem alpha_mono {a b : ℕ} (h : a ≤ b) : alpha a ≤ alpha b := by
  unfold alpha
  have ha : (a : ℚ) ≤ b := by exact_mod_cast h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem alpha_le (j : ℕ) : alpha j ≤ 4 / 3 := by
  unfold alpha
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem bb_le_ninth {k : ℕ} (h : 6 ≤ k) : bb k ≤ 1 / 9 := by
  unfold bb
  have hk : (6 : ℚ) ≤ k := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem bb_ge_ninth {k : ℕ} (h : k ≤ 6) : 1 / 9 ≤ bb k := by
  unfold bb
  have hk : (k : ℚ) ≤ 6 := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem bb_le_third {k : ℕ} (h : 2 ≤ k) : bb k ≤ 1 / 3 := by
  unfold bb
  have hk : (2 : ℚ) ≤ k := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### The structure of a maximizer on `≥ 492` vertices -/

section Struct

set_option linter.unusedSectionVars false

variable {l : List Child} (hmax : IsMax l) (hn : 492 ≤ nv l)
include hmax hn

/-- Step 1: the centre has at least three children (global comparison with `W n`). -/
theorem three_le_length : 3 ≤ l.length := by
  by_contra hcon
  refine global_contra hmax hn 1 (32 / 27) (by norm_num) (by norm_num) 2 (fun c _ => r_le_one c) ?_
    (by omega) (by norm_num)
  intro j _
  simp only [hh]
  have h1 := alpha_le j
  have h0 := (alpha_pos j).le
  nlinarith

/-- Step 2: no arm has 13 or more cherries (split). -/
theorem arm_le_twelve : ∀ j, Child.arm j ∈ l → j ≤ 12 := by
  intro j hj
  by_contra hcon
  obtain ⟨u, rfl⟩ : ∃ u, j = u + 13 := ⟨j - 13, by omega⟩
  have h3 := three_le_length hmax hn
  have hr : ∀ c ∈ l, c.r ≤ 1 / 3 := by
    intro c hc
    cases c with
    | cherry => norm_num [Child.r]
    | arm k =>
      have := balanced_of_isMax l hmax h3 (u + 13) k hj hc
      exact bb_le_third (by omega)
  refine not_isMax_of_exch (new := [Child.arm (u + 2), Child.arm 5, Child.arm 5])
    (List.singleton_sublist.mpr hj) ?_ ?_ hmax
  · simp [Child.cost]; omega
  · intro rest hm _
    exact exch_split_lt u rest (fun c hc => hr c (hm c hc))

/-- Counting via `11 A_k → (2k+1) A_5`. -/
theorem count_arm_le_ten (k : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12) :
    l.count (Child.arm k) ≤ 10 := by
  have := count_lt_of_exch hmax (Child.arm k) 11 (List.replicate (2 * k + 1) (Child.arm 5))
    (by rw [cost_sum_replicate]; simp only [Child.cost]; ring)
    (fun rest _ _ => exch_arm_lt k hk rest)
  omega

theorem count_six_le_ten (hr : ∀ c ∈ l, c.r ≤ 1 / 3) : l.count (Child.arm 6) ≤ 10 := by
  have := count_lt_of_exch hmax (Child.arm 6) 11 (List.replicate 13 (Child.arm 5))
    (by rw [cost_sum_replicate]; simp only [Child.cost])
    (fun rest hm _ => exch_six_lt rest (fun c hc => hr c (hm c hc)))
  omega

theorem count_four_le_ten (hr : ∀ c ∈ l, 1 / 9 ≤ c.r) (hlen : 38 ≤ l.length) :
    l.count (Child.arm 4) ≤ 10 := by
  have := count_lt_of_exch hmax (Child.arm 4) 11 (List.replicate 9 (Child.arm 5))
    (by rw [cost_sum_replicate]; simp only [Child.cost])
    (fun rest hm hl => exch_four_lt rest (fun c hc => hr c (hm c hc)) (by omega))
  omega

/-- Step 3: no arm has 7 or more cherries (counting + global comparison). -/
theorem arm_le_six : ∀ j, Child.arm j ∈ l → j ≤ 6 := by
  intro J hJ
  by_contra hcon
  have h3 := three_le_length hmax hn
  have h12 := arm_le_twelve hmax hn
  have hJ12 := h12 J hJ
  have hbal := balanced_of_isMax l hmax h3
  have hr : ∀ c ∈ l, c.r ≤ 1 / 3 := by
    intro c hc
    cases c with
    | cherry => norm_num [Child.r]
    | arm k =>
      have := hbal J k hJ hc
      exact bb_le_third (by omega)
  have hcnt : ∀ k, 6 ≤ k → l.count (Child.arm k) ≤ 10 := by
    intro k hk
    by_cases hk12 : k ≤ 12
    · by_cases hk6 : k = 6
      · subst hk6; exact count_six_le_ten hmax hn hr
      · exact count_arm_le_ten hmax hn k (by omega)
    · have : Child.arm k ∉ l := fun hm => hk12 (h12 k hm)
      rw [List.count_eq_zero_of_not_mem this]; omega
  -- all arms lie in {m, m+1}
  obtain ⟨m, hm6, hm12, hmem⟩ : ∃ m, 6 ≤ m ∧ m ≤ 12 ∧
      ∀ c ∈ l, c = Child.cherry ∨ c = Child.arm m ∨ c = Child.arm (m + 1) := by
    by_cases hJ1 : Child.arm (J - 1) ∈ l
    · refine ⟨J - 1, by omega, by omega, ?_⟩
      intro c hc
      cases c with
      | cherry => exact Or.inl rfl
      | arm k =>
        have a1 := hbal J k hJ hc
        have a2 := hbal k (J - 1) hc hJ1
        right
        rcases (show k = J - 1 ∨ k = J - 1 + 1 by omega) with h | h
        · left; rw [h]
        · right; rw [h]
    · refine ⟨J, by omega, hJ12, ?_⟩
      intro c hc
      cases c with
      | cherry => exact Or.inl rfl
      | arm k =>
        have a1 := hbal J k hJ hc
        have a2 := hbal k J hc hJ
        right
        have hk1 : k ≠ J - 1 := fun h => hJ1 (h ▸ hc)
        rcases (show k = J ∨ k = J + 1 by omega) with h | h
        · left; rw [h]
        · right; rw [h]
  have hlen := len_le_three l m (m + 1) hmem
  have c1 := hcnt m hm6
  have c2 := hcnt (m + 1) (by omega)
  refine global_contra hmax hn (1 / 3) (hh (Child.arm 12)) (by norm_num)
    (by norm_num [hh, alpha]) 20 hr ?_ (by omega) (by norm_num [hh, alpha])
  intro j hj
  simp only [hh]
  have hmono := alpha_mono (h12 j hj)
  have h0 := (alpha_pos j).le
  nlinarith

theorem r_ge_ninth_of_le_six (h6 : ∀ j, Child.arm j ∈ l → j ≤ 6) : ∀ c ∈ l, 1 / 9 ≤ c.r := by
  intro c hc
  cases c with
  | cherry => norm_num [Child.r]
  | arm k => exact bb_ge_ninth (h6 k hc)

theorem length_ge_of_cost (B : ℕ) (hB : ∀ c ∈ l, c.cost ≤ B) : 491 ≤ B * l.length := by
  have := sum_cost_le l B hB
  simp only [nv] at hn
  omega

/-- Step 4: at most 8 cherries (`9 P → 2 A_4`). -/
theorem count_cherry_le_eight : l.count Child.cherry ≤ 8 := by
  have h6 := arm_le_six hmax hn
  have hr := r_ge_ninth_of_le_six hmax hn h6
  have hlen := length_ge_of_cost hmax hn 13 (by
    intro c hc
    cases c with
    | cherry => simp [Child.cost]
    | arm k => have := h6 k hc; simp only [Child.cost]; omega)
  have := count_lt_of_exch hmax Child.cherry 9 (List.replicate 2 (Child.arm 4))
    (by rw [cost_sum_replicate]; simp only [Child.cost])
    (fun rest hm hl => exch_cherry_lt rest (fun c hc => hr c (hm c hc)) (by omega))
  omega

/-- Step 5: no arm has 3 or fewer cherries. -/
theorem four_le_arm : ∀ j, Child.arm j ∈ l → 4 ≤ j := by
  intro s hs
  by_contra hcon
  have h3 := three_le_length hmax hn
  have hbal := balanced_of_isMax l hmax h3
  have h6 := arm_le_six hmax hn
  have hr := r_ge_ninth_of_le_six hmax hn h6
  have hmem : ∀ c ∈ l, c = Child.cherry ∨ ∃ k, k ≤ 4 ∧ c = Child.arm k := by
    intro c hc
    cases c with
    | cherry => exact Or.inl rfl
    | arm k => exact Or.inr ⟨k, by have := hbal k s hc hs; omega, rfl⟩
  have hlen := length_ge_of_cost hmax hn 9 (by
    intro c hc
    rcases hmem c hc with rfl | ⟨k, hk, rfl⟩
    · simp [Child.cost]
    · simp only [Child.cost]; omega)
  have hL := len_le_five l hmem
  have c0 := leaf_count_le_one_of_isMax l hmax h3
  have c1 := count_arm_le_ten hmax hn 1 (by omega)
  have c2 := count_arm_le_ten hmax hn 2 (by omega)
  have c3 := count_arm_le_ten hmax hn 3 (by omega)
  have c4 := count_four_le_ten hmax hn hr (by omega)
  have cP := count_cherry_le_eight hmax hn
  omega

/-- **The structure theorem.** -/
theorem cand_of_isMax : Cand l := by
  have h3 := three_le_length hmax hn
  have hbal := balanced_of_isMax l hmax h3
  have h6 := arm_le_six hmax hn
  have h4 := four_le_arm hmax hn
  have hr := r_ge_ninth_of_le_six hmax hn h6
  have hlen := length_ge_of_cost hmax hn 13 (by
    intro c hc
    cases c with
    | cherry => simp [Child.cost]
    | arm k => have := h6 k hc; simp only [Child.cost]; omega)
  have hr3 : ∀ c ∈ l, c.r ≤ 1 / 3 := by
    intro c hc
    cases c with
    | cherry => norm_num [Child.r]
    | arm k => exact bb_le_third (by have := h4 k hc; omega)
  refine ⟨count_cherry_le_eight hmax hn, ?_, ?_, count_four_le_ten hmax hn hr (by omega),
    count_six_le_ten hmax hn hr3⟩
  · intro c hc
    cases c with
    | cherry => exact Or.inl rfl
    | arm k =>
      have a := h4 k hc
      have b := h6 k hc
      right
      rcases (show k = 4 ∨ k = 5 ∨ k = 6 by omega) with rfl | rfl | rfl <;> simp
  · rintro ⟨h4m, h6m⟩
    have := hbal 6 4 h6m h4m
    omega

end Struct

/-- **StructProp 492**: every `F`-maximizer on at least 492 vertices lies in the candidate set. -/
theorem structProp_492 : StructProp 492 := fun _ hn hmax => cand_of_isMax hmax hn

end BGSpiderStruct
end R3Cert
