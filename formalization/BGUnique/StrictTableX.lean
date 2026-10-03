import Mathlib
import BGUnique.StrictTable

namespace R3Cert
namespace SpiderStrict

open BGSpiderOpt BGSpiderRule BGSpiderTable

/-- The balanced configuration with `C` cherries and `m` arms on `n` vertices. -/
def canonB (n : ℕ) (p : ℕ × ℕ) : List Child :=
  if p.2 = 0 then List.replicate p.1 Child.cherry
  else canon p.1 (balOf n p.1 p.2).1 (balOf n p.1 p.2).2.1 (balOf n p.1 p.2).2.2

/-- Every balanced configuration with ≥ 3 children, other than the listed `(C, m)`, is `< T`. -/
def checkBalX (n : ℕ) (ex : List (ℕ × ℕ)) (T : ℕ × ℕ) : Bool :=
  (List.range ((n - 1) / 2 + 1)).all fun C =>
    (List.range (n - 1 - 2 * C + 1)).all fun m =>
      if 3 ≤ C + m ∧ (n - 1 - 2 * C - m) % 2 = 0 then
        if ex.contains (C, m) then true
        else if m = 0 then ltND (fnum C 0 0 0, fden C 0 0 0) T
        else
          let p := balOf n C m
          ltND (fnum C p.1 p.2.1 p.2.2, fden C p.1 p.2.1 p.2.2) T
      else true

/-- Every configuration with one or two children, other than the listed ones, is `< T`. -/
def checkSmallX (n : ℕ) (ex1 : List Child) (ex2 : List (Child × Child)) (T : ℕ × ℕ) : Bool :=
  (kids n).all (fun c => if c.cost = n - 1 then ex1.contains c || ltND (f1 c) T else true) &&
  (kids n).all fun c => (kids n).all fun d =>
    if c.cost + d.cost = n - 1 then ex2.contains (c, d) || ltND (f2 c d) T else true

/-- The strict check at `n` with explicit exceptions. -/
def checkX (n : ℕ) (exB : List (ℕ × ℕ)) (ex1 : List Child) (ex2 : List (Child × Child)) : Bool :=
  checkBalX n exB (tabV n) && checkSmallX n ex1 ex2 (tabV n)

theorem bal_ltX (n : ℕ) (ex : List (ℕ × ℕ)) (T : ℕ × ℕ) (hT : 0 < T.2) (hc : checkBalX n ex T = true)
    (C s a b : ℕ) (hn : nv (canon C s a b) = n) (h3 : 3 ≤ C + a + b) (hne : (C, a + b) ∉ ex) :
    F (canon C s a b) < (T.1 : ℚ) / T.2 := by
  have hn' := hn
  rw [nv_canon] at hn'
  have e : n = 1 + 2 * C + (a + b) + 2 * (s * (a + b) + b) := by rw [← hn']; ring
  unfold checkBalX at hc
  rw [List.all_eq_true] at hc
  have hC0 := hc C (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hC0
  have hC := hC0 (a + b) (List.mem_range.mpr (by omega))
  have hcond : 3 ≤ C + (a + b) ∧ (n - 1 - 2 * C - (a + b)) % 2 = 0 := ⟨by omega, by omega⟩
  have hne' : ex.contains (C, a + b) = false := by simpa using hne
  rw [if_pos hcond, hne'] at hC
  simp only [Bool.false_eq_true, if_false] at hC
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

/-- **Spider-family maximizers from the check with exceptions**: a configuration on `n` vertices whose
    value reaches the table spider's is a rearrangement of a listed balanced configuration, or is a
    listed one- or two-child configuration. -/
theorem spider_cases_of_checkX (n : ℕ) (hn : 2 ≤ n) (hcN : checkN n = true)
    (exB : List (ℕ × ℕ)) (ex1 : List Child) (ex2 : List (Child × Child))
    (hc : checkX n exB ex1 ex2 = true)
    (l : List Child) (hl : nv l = n) (hge : F (tab n) ≤ F l) :
    (∃ p ∈ exB, l.Perm (canonB n p)) ∨ (∃ c ∈ ex1, l = [c]) ∨ (∃ q ∈ ex2, l = [q.1, q.2]) := by
  obtain ⟨hnvT, hopt⟩ := spider_opt_of_checkN n hn hcN
  have hcN' := hcN
  simp only [checkN, Bool.and_eq_true] at hcN'
  have hposT : 0 < (row n).1 + (row n).2.2.1 + (row n).2.2.2 := Nat.blt_eq.mp hcN'.1.1.2
  have hT : 0 < (tabV n).2 := fden_pos _ _ _ _ hposT
  have hFT : F (tab n) = ((tabV n).1 : ℚ) / (tabV n).2 := by rw [tab, F_canon_eq _ _ _ _ hposT]; rfl
  simp only [checkX, Bool.and_eq_true] at hc
  obtain ⟨hb, hs⟩ := hc
  have hmax : IsMax l := by
    intro l' hl'
    exact le_trans (hopt l' (by rw [hl', hl])) hge
  by_cases h3 : 3 ≤ l.length
  · left
    have hbal : ∀ j k : ℕ, Child.arm j ∈ l → Child.arm k ∈ l → j ≤ k + 1 :=
      fun j k hj hk => balanced_of_isMax l hmax h3 j k hj hk
    obtain ⟨C, s, a, b, hp⟩ := canon_of_balanced l hbal
    have hlen := hp.length_eq
    simp only [canon, List.length_append, List.length_replicate] at hlen
    have hnc : nv (canon C s a b) = n := by rw [← nv_perm hp, hl]
    by_cases hin : (C, a + b) ∈ exB
    · refine ⟨(C, a + b), hin, ?_⟩
      unfold canonB
      by_cases hm0 : a + b = 0
      · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
        simp only [if_pos hm0]
        simpa [canon] using hp
      · simp only [if_neg hm0]
        rw [← canon_eq_balOf n C s a b hnc (Nat.pos_of_ne_zero hm0)]
        exact hp
    · have := bal_ltX n exB (tabV n) hT hb C s a b hnc (by omega) hin
      rw [← hFT, ← F_perm hp] at this
      exact absurd hge (not_le.mpr this)
  · right
    simp only [checkSmallX, Bool.and_eq_true, List.all_eq_true] at hs
    obtain ⟨h1, h2⟩ := hs
    rcases l with _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩
    · simp [nv] at hl; omega
    · left
      have hcost : c.cost = n - 1 := by simp [nv] at hl; omega
      have := h1 c (mem_kids (by omega))
      rw [if_pos hcost, Bool.or_eq_true] at this
      rcases this with hm | hlt
      · exact ⟨c, by simpa using hm, rfl⟩
      · have := ltND_sound (f1_pos c) hT hlt
        rw [← F_one, ← hFT] at this
        exact absurd hge (not_le.mpr this)
    · right
      have hcost : c.cost + d.cost = n - 1 := by simp [nv] at hl; omega
      have := h2 c (mem_kids (by have := cost_pos' d; omega)) d (mem_kids (by have := cost_pos' c; omega))
      rw [if_pos hcost, Bool.or_eq_true] at this
      rcases this with hm | hlt
      · exact ⟨(c, d), by simpa using hm, rfl⟩
      · have := ltND_sound (f2_pos c d) hT hlt
        rw [← F_two, ← hFT] at this
        exact absurd hge (not_le.mpr this)
    · simp at h3

end SpiderStrict
end R3Cert
