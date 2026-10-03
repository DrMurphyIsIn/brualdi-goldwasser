import Mathlib
import R3Cert.BGSpiderTableData

namespace R3Cert
namespace SpiderStrict

open BGSpiderOpt BGSpiderRule BGSpiderTable

/-- `x < y` for exact values given as numerator/denominator pairs. -/
def ltND (x y : ℕ × ℕ) : Bool := Nat.blt (x.1 * y.2) (y.1 * x.2)

/-- Every canonical configuration with ≥ 3 children on `n` vertices, other than the one with `C0`
    cherries and `m0` arms, is `< T`. -/
def checkBalS (n C0 m0 : ℕ) (T : ℕ × ℕ) : Bool :=
  (List.range ((n - 1) / 2 + 1)).all fun C =>
    (List.range (n - 1 - 2 * C + 1)).all fun m =>
      if 3 ≤ C + m ∧ (n - 1 - 2 * C - m) % 2 = 0 then
        if C = C0 ∧ m = m0 then true
        else if m = 0 then ltND (fnum C 0 0 0, fden C 0 0 0) T
        else
          let p := balOf n C m
          ltND (fnum C p.1 p.2.1 p.2.2, fden C p.1 p.2.1 p.2.2) T
      else true

/-- Every configuration with one or two children on `n` vertices is `< T`. -/
def checkSmallS (n : ℕ) (T : ℕ × ℕ) : Bool :=
  (kids n).all (fun c => if c.cost = n - 1 then ltND (f1 c) T else true) &&
  (kids n).all fun c => (kids n).all fun d =>
    if c.cost + d.cost = n - 1 then ltND (f2 c d) T else true

/-- The strict per-`n` kernel check. -/
def checkNS (n : ℕ) : Bool :=
  Nat.blt 0 ((row n).2.2.1 + (row n).2.2.2) &&
  checkBalS n (row n).1 ((row n).2.2.1 + (row n).2.2.2) (tabV n) && checkSmallS n (tabV n)

theorem ltND_sound {x y : ℕ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) (h : ltND x y = true) :
    (x.1 : ℚ) / x.2 < (y.1 : ℚ) / y.2 := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  exact_mod_cast Nat.blt_eq.mp h

theorem small_lt (n : ℕ) (T : ℕ × ℕ) (hT : 0 < T.2) (hc : checkSmallS n T = true)
    (l : List Child) (hl : nv l = n) (hlen : l.length ≤ 2) (hne : l ≠ []) :
    F l < (T.1 : ℚ) / T.2 := by
  simp only [checkSmallS, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨h1, h2⟩ := hc
  rcases l with _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩
  · exact absurd rfl hne
  · have hcost : c.cost = n - 1 := by simp [nv] at hl; omega
    have := h1 c (mem_kids (by omega))
    rw [if_pos hcost] at this
    rw [F_one]; exact ltND_sound (f1_pos c) hT this
  · have hcost : c.cost + d.cost = n - 1 := by simp [nv] at hl; omega
    have := h2 c (mem_kids (by have := cost_pos' d; omega)) d (mem_kids (by have := cost_pos' c; omega))
    rw [if_pos hcost] at this
    rw [F_two]; exact ltND_sound (f2_pos c d) hT this
  · simp at hlen

theorem bal_lt (n C0 m0 : ℕ) (T : ℕ × ℕ) (hT : 0 < T.2) (hc : checkBalS n C0 m0 T = true)
    (C s a b : ℕ) (hn : nv (canon C s a b) = n) (h3 : 3 ≤ C + a + b) (hne : ¬ (C = C0 ∧ a + b = m0)) :
    F (canon C s a b) < (T.1 : ℚ) / T.2 := by
  have hn' := hn
  rw [nv_canon] at hn'
  have e : n = 1 + 2 * C + (a + b) + 2 * (s * (a + b) + b) := by rw [← hn']; ring
  unfold checkBalS at hc
  rw [List.all_eq_true] at hc
  have hC0 := hc C (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hC0
  have hC := hC0 (a + b) (List.mem_range.mpr (by omega))
  have hcond : 3 ≤ C + (a + b) ∧ (n - 1 - 2 * C - (a + b)) % 2 = 0 := ⟨by omega, by omega⟩
  rw [if_pos hcond, if_neg hne] at hC
  by_cases hm0 : a + b = 0
  · rw [if_pos hm0] at hC
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have heq : canon C s 0 0 = canon C 0 0 0 := by
      simp only [canon, List.replicate_zero, List.append_nil]
    rw [heq, F_canon_eq _ _ _ _ (by omega)]
    exact ltND_sound (x := (fnum C 0 0 0, fden C 0 0 0)) (fden_pos _ _ _ _ (by omega)) hT hC
  · rw [if_neg hm0] at hC
    have hm : 0 < a + b := Nat.pos_of_ne_zero hm0
    rw [canon_eq_balOf n C s a b hn hm]
    have hsum : 0 < C + (balOf n C (a + b)).2.1 + (balOf n C (a + b)).2.2 := by
      have := balOf_sum n C (a + b) hm; omega
    rw [F_canon_eq _ _ _ _ hsum]
    exact ltND_sound (x := (fnum C (balOf n C (a + b)).1 (balOf n C (a + b)).2.1 (balOf n C (a + b)).2.2,
      fden C (balOf n C (a + b)).1 (balOf n C (a + b)).2.1 (balOf n C (a + b)).2.2))
      (fden_pos _ _ _ _ hsum) hT hC

/-- **Strict spider-family optimum from the per-`n` checks**: a configuration on `n` vertices whose value
    reaches the table spider's is a rearrangement of it. -/
theorem spider_unique_of_check (n : ℕ) (hn : 2 ≤ n) (hcN : checkN n = true) (hcS : checkNS n = true)
    (l : List Child) (hl : nv l = n) (hge : F (tab n) ≤ F l) : l.Perm (tab n) := by
  obtain ⟨hnvT, hopt⟩ := spider_opt_of_checkN n hn hcN
  simp only [checkNS, Bool.and_eq_true] at hcS
  obtain ⟨⟨hpos, hb⟩, hs⟩ := hcS
  unfold tab at hnvT hopt hge ⊢
  unfold tabV at hb hs
  generalize row n = r at *
  obtain ⟨C0, s0, a0, b0⟩ := r
  simp only at hnvT hopt hge hb hs hpos ⊢
  have hm0 : 0 < a0 + b0 := Nat.blt_eq.mp hpos
  have hposT : 0 < C0 + a0 + b0 := by omega
  have hT : 0 < fden C0 s0 a0 b0 := fden_pos _ _ _ _ hposT
  have hFT : F (canon C0 s0 a0 b0) = ((fnum C0 s0 a0 b0 : ℕ) : ℚ) / (fden C0 s0 a0 b0 : ℕ) :=
    F_canon_eq _ _ _ _ hposT
  have hmax : IsMax l := by
    intro l' hl'
    exact le_trans (hopt l' (by rw [hl', hl])) hge
  by_cases h3 : 3 ≤ l.length
  · have hbal : ∀ j k : ℕ, Child.arm j ∈ l → Child.arm k ∈ l → j ≤ k + 1 :=
      fun j k hj hk => balanced_of_isMax l hmax h3 j k hj hk
    obtain ⟨C, s, a, b, hp⟩ := canon_of_balanced l hbal
    have hlen := hp.length_eq
    simp only [canon, List.length_append, List.length_replicate] at hlen
    have hnc : nv (canon C s a b) = n := by rw [← nv_perm hp, hl]
    by_cases heq : C = C0 ∧ a + b = a0 + b0
    · obtain ⟨hC, hab⟩ := heq
      have hm : 0 < a + b := by omega
      have e1 := canon_eq_balOf n C s a b hnc hm
      have e2 := canon_eq_balOf n C0 s0 a0 b0 hnvT hm0
      rw [e2, ← hab, ← hC, ← e1]
      exact hp
    · have := bal_lt n C0 (a0 + b0) (fnum C0 s0 a0 b0, fden C0 s0 a0 b0) hT hb C s a b hnc (by omega) heq
      rw [← hFT, ← F_perm hp] at this
      exact absurd hge (not_le.mpr this)
  · have hne : l ≠ [] := by
      intro h; rw [h] at hl; simp [nv] at hl; omega
    have := small_lt n (fnum C0 s0 a0 b0, fden C0 s0 a0 b0) hT hs l hl (by omega) hne
    rw [← hFT] at this
    exact absurd hge (not_le.mpr this)

theorem checkNS_of_all {lo len : ℕ} (h : (List.range' lo len).all checkNS = true) (n : ℕ)
    (h1 : lo ≤ n) (h2 : n < lo + len) : checkNS n = true := by
  rw [List.all_eq_true] at h
  exact h n (List.mem_range'_1.mpr ⟨h1, h2⟩)

end SpiderStrict
end R3Cert
