/-
  R3Cert.BGSpiderTable -- the spider-family optimum for every n <= 491, by a kernel-checked sweep.

  A spider-family maximizer with >= 3 centre children is balanced (`balanced_of_isMax`), so it is a
  permutation of a canonical configuration `canon C s a b` (C cherries, a arms of size s, b arms of
  size s+1).  Its value has an exact integer closed form (`F_canon_eq`).  `checkBal n` compares every
  canonical configuration on n vertices, and `checkSmall n` every configuration with <= 2 children,
  against the table maximizer `tab n`, by cross-multiplied natural-number inequalities.  The checks are
  evaluated by the kernel (`decide +kernel`) in the generated chunk files BGSpiderTableChunk*.lean.
  This file proves the soundness lemmas: `spider_opt_of_check`.
  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGSpiderOpt
import R3Cert.BGSpiderRule

namespace R3Cert
namespace BGSpiderTable

open BGSpiderOpt BGSpiderRule

/-! ### Canonical balanced configurations and their exact value -/

/-- `C` cherries, `a` arms of size `s`, `b` arms of size `s+1`. -/
def canon (C s a b : ℕ) : List Child :=
  List.replicate C Child.cherry ++ List.replicate a (Child.arm s) ++ List.replicate b (Child.arm (s + 1))

/-- Numerator of `F (canon C s a b)`. -/
def fnum (C s a b : ℕ) : ℕ :=
  let A := 4 * s + 3
  let B := 4 * s + 7
  let D := C + a + b
  3 ^ C * (3 ^ s * A) ^ a * (3 ^ (s + 1) * B) ^ b * (D * (3 * A * B) + (C * A * B + 9 * a * B + 9 * b * A))

/-- Denominator of `F (canon C s a b)`. -/
def fden (C s a b : ℕ) : ℕ :=
  let A := 4 * s + 3
  let B := 4 * s + 7
  let D := C + a + b
  2 ^ C * (2 ^ s * (3 * (s + 1))) ^ a * (2 ^ (s + 1) * (3 * (s + 2))) ^ b * (D * (3 * A * B))

theorem fden_pos (C s a b : ℕ) (hD : 0 < C + a + b) : 0 < fden C s a b := by
  unfold fden; positivity

theorem g_arm_eq (j : ℕ) :
    (Child.arm j).g = ((3 ^ j * (4 * j + 3) : ℕ) : ℚ) / ((2 ^ j * (3 * (j + 1)) : ℕ) : ℚ) := by
  simp only [Child.g, alpha, div_pow]
  have : (0 : ℚ) < (j : ℚ) + 1 := by positivity
  push_cast
  field_simp

theorem F_canon_eq (C s a b : ℕ) (hD : 0 < C + a + b) :
    F (canon C s a b) = (fnum C s a b : ℚ) / (fden C s a b : ℚ) := by
  simp only [F, canon, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, List.sum_append, List.sum_replicate, List.length_append, List.length_replicate,
    nsmul_eq_mul, g_arm_eq]
  simp only [Child.g, Child.r, bb, fnum, fden, div_pow]
  have hD' : (0 : ℚ) < (C : ℚ) + a + b := by exact_mod_cast hD
  push_cast
  field_simp
  ring

/-- Cross-multiplication. -/
theorem le_of_cross {p q r t : ℕ} (hq : 0 < q) (ht : 0 < t) (h : p * t ≤ r * q) :
    (p : ℚ) / q ≤ (r : ℚ) / t := by
  rw [div_le_div_iff₀ (by exact_mod_cast hq) (by exact_mod_cast ht)]
  exact_mod_cast h

/-! ### Exact value of an arbitrary (short) configuration -/

def gnd : Child → ℕ × ℕ
  | Child.cherry => (3, 2)
  | Child.arm j => (3 ^ j * (4 * j + 3), 2 ^ j * (3 * (j + 1)))

def rnd : Child → ℕ × ℕ
  | Child.cherry => (1, 3)
  | Child.arm j => (3, 4 * j + 3)

theorem gnd_eq (c : Child) : (c.g : ℚ) = ((gnd c).1 : ℚ) / (gnd c).2 := by
  cases c with
  | cherry => norm_num [Child.g, gnd]
  | arm j =>
    rw [g_arm_eq]; simp [gnd]

theorem rnd_eq (c : Child) : (c.r : ℚ) = ((rnd c).1 : ℚ) / (rnd c).2 := by
  cases c with
  | cherry => norm_num [Child.r, rnd]
  | arm j => simp only [Child.r, rnd, bb]; push_cast; ring

theorem gnd_pos (c : Child) : 0 < (gnd c).2 := by cases c <;> simp [gnd]
theorem rnd_pos (c : Child) : 0 < (rnd c).2 := by cases c <;> simp [rnd]

/-- Numerator/denominator of `F [c]`. -/
def f1 (c : Child) : ℕ × ℕ :=
  ((gnd c).1 * ((rnd c).2 + (rnd c).1), (gnd c).2 * (rnd c).2)

/-- Numerator/denominator of `F [c, d]`. -/
def f2 (c d : Child) : ℕ × ℕ :=
  let rs := (rnd c).1 * (rnd d).2 + (rnd d).1 * (rnd c).2
  let rd := (rnd c).2 * (rnd d).2
  ((gnd c).1 * (gnd d).1 * (2 * rd + rs), (gnd c).2 * (gnd d).2 * (2 * rd))

theorem F_one (c : Child) : F [c] = ((f1 c).1 : ℚ) / (f1 c).2 := by
  simp only [F, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil, f1, gnd_eq, rnd_eq]
  have h1 : (0 : ℚ) < (gnd c).2 := by exact_mod_cast gnd_pos c
  have h2 : (0 : ℚ) < (rnd c).2 := by exact_mod_cast rnd_pos c
  push_cast; field_simp; ring

theorem F_two (c d : Child) : F [c, d] = ((f2 c d).1 : ℚ) / (f2 c d).2 := by
  simp only [F, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil, f2, gnd_eq, rnd_eq]
  have h1 : (0 : ℚ) < (gnd c).2 := by exact_mod_cast gnd_pos c
  have h2 : (0 : ℚ) < (rnd c).2 := by exact_mod_cast rnd_pos c
  have h3 : (0 : ℚ) < (gnd d).2 := by exact_mod_cast gnd_pos d
  have h4 : (0 : ℚ) < (rnd d).2 := by exact_mod_cast rnd_pos d
  push_cast; field_simp; ring

theorem f1_pos (c : Child) : 0 < (f1 c).2 := by
  simp only [f1]; exact Nat.mul_pos (gnd_pos c) (rnd_pos c)
theorem f2_pos (c d : Child) : 0 < (f2 c d).2 := by
  simp only [f2]
  have := gnd_pos c; have := gnd_pos d; have := rnd_pos c; have := rnd_pos d
  positivity

/-! ### The checker -/

/-- Balanced parameters from `(C, m)` at size `n`: arm vertex budget `V`, total arm cherries `J`. -/
def balOf (n C m : ℕ) : ℕ × ℕ × ℕ :=
  let V := n - 1 - 2 * C
  let J := (V - m) / 2
  (J / m, m - J % m, J % m)

/-- `x ≤ y` for exact values given as numerator/denominator pairs. -/
def leND (x y : ℕ × ℕ) : Bool := Nat.ble (x.1 * y.2) (y.1 * x.2)

/-- Every canonical configuration with ≥ 3 children on `n` vertices is `≤` the value `T`. -/
def checkBal (n : ℕ) (T : ℕ × ℕ) : Bool :=
  (List.range ((n - 1) / 2 + 1)).all fun C =>
    (List.range (n - 1 - 2 * C + 1)).all fun m =>
      if 3 ≤ C + m ∧ (n - 1 - 2 * C - m) % 2 = 0 then
        if m = 0 then leND (fnum C 0 0 0, fden C 0 0 0) T
        else
          let p := balOf n C m
          leND (fnum C p.1 p.2.1 p.2.2, fden C p.1 p.2.1 p.2.2) T
      else true

/-- Children of cost at most `B`. -/
def kids (B : ℕ) : List Child := Child.cherry :: (List.range (B + 1)).map Child.arm

/-- Every configuration with one or two children on `n` vertices is `≤` the value `T`. -/
def checkSmall (n : ℕ) (T : ℕ × ℕ) : Bool :=
  (kids n).all (fun c => if c.cost = n - 1 then leND (f1 c) T else true) &&
  (kids n).all fun c => (kids n).all fun d =>
    if c.cost + d.cost = n - 1 then leND (f2 c d) T else true

/-! ### Soundness -/

theorem leND_sound {x y : ℕ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) (h : leND x y = true) :
    (x.1 : ℚ) / x.2 ≤ (y.1 : ℚ) / y.2 :=
  le_of_cross hx hy (Nat.le_of_ble_eq_true h)

theorem cost_pos' (c : Child) : 1 ≤ c.cost := by cases c <;> simp [Child.cost]

theorem mem_kids {c : Child} {B : ℕ} (h : c.cost ≤ B) : c ∈ kids B := by
  cases c with
  | cherry => simp [kids]
  | arm j =>
    simp only [kids, List.mem_cons, List.mem_map, List.mem_range]
    right; exact ⟨j, by simp only [Child.cost] at h; omega, rfl⟩

/-- A configuration with at most two children is covered by `checkSmall`. -/
theorem small_le (n : ℕ) (T : ℕ × ℕ) (hT : 0 < T.2) (hc : checkSmall n T = true)
    (l : List Child) (hl : nv l = n) (hlen : l.length ≤ 2) (hne : l ≠ []) :
    F l ≤ (T.1 : ℚ) / T.2 := by
  simp only [checkSmall, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨h1, h2⟩ := hc
  rcases l with _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩
  · exact absurd rfl hne
  · have hcost : c.cost = n - 1 := by simp [nv] at hl; omega
    have := h1 c (mem_kids (by omega))
    rw [if_pos hcost] at this
    rw [F_one]; exact leND_sound (f1_pos c) hT this
  · have hcost : c.cost + d.cost = n - 1 := by simp [nv] at hl; omega
    have := h2 c (mem_kids (by have := cost_pos' d; omega)) d (mem_kids (by have := cost_pos' c; omega))
    rw [if_pos hcost] at this
    rw [F_two]; exact leND_sound (f2_pos c d) hT this
  · simp at hlen

/-! ### Balanced lists are canonical -/

theorem count_rep (k : ℕ) (c x : Child) : (List.replicate k c).count x = if x = c then k else 0 := by
  by_cases h : x = c
  · subst h; simp
  · rw [if_neg h]; exact List.count_eq_zero_of_not_mem (by simp [List.mem_replicate]; intro _; exact h)

theorem count_canon (C s a b : ℕ) (x : Child) :
    (canon C s a b).count x =
      (if x = Child.cherry then C else 0) + (if x = Child.arm s then a else 0) +
      (if x = Child.arm (s + 1) then b else 0) := by
  simp only [canon, List.count_append, count_rep]

theorem canon_of_balanced (l : List Child)
    (hbal : ∀ j k : ℕ, Child.arm j ∈ l → Child.arm k ∈ l → j ≤ k + 1) :
    ∃ C s a b, l.Perm (canon C s a b) := by
  classical
  by_cases hex : ∃ j, Child.arm j ∈ l
  · let s := Nat.find hex
    have hs : Child.arm s ∈ l := Nat.find_spec hex
    have hmin : ∀ j, Child.arm j ∈ l → s ≤ j := fun j hj => Nat.find_min' hex hj
    refine ⟨l.count Child.cherry, s, l.count (Child.arm s), l.count (Child.arm (s + 1)), ?_⟩
    rw [List.perm_iff_count]
    intro x
    rw [count_canon]
    cases x with
    | cherry => simp
    | arm j =>
      by_cases h1 : j = s
      · subst h1; simp
      · by_cases h2 : j = s + 1
        · subst h2; simp
        · have hj : Child.arm j ∉ l := by
            intro hj
            have := hmin j hj
            have := hbal j s hj hs
            omega
          simp [List.count_eq_zero_of_not_mem hj, h1, h2]
  · push Not at hex
    refine ⟨l.length, 0, 0, 0, ?_⟩
    have hall : ∀ c ∈ l, c = Child.cherry := by
      intro c hc
      cases c with
      | cherry => rfl
      | arm j => exact absurd hc (hex j)
    rw [List.eq_replicate_iff.mpr ⟨rfl, hall⟩]
    simp [canon]

theorem nv_canon (C s a b : ℕ) :
    nv (canon C s a b) = 1 + 2 * C + a * (2 * s + 1) + b * (2 * s + 3) := by
  simp only [nv, canon, List.map_append, List.sum_append, cost_sum_replicate, Child.cost]
  ring

/-- Normal form of the balanced parameters: `canon C s a b` equals the configuration the checker
    builds from `(C, m)`, `m = a + b`. -/
theorem canon_eq_balOf (n C s a b : ℕ) (hn : nv (canon C s a b) = n) (hm : 0 < a + b) :
    canon C s a b = canon C (balOf n C (a + b)).1 (balOf n C (a + b)).2.1 (balOf n C (a + b)).2.2 := by
  rw [nv_canon] at hn
  have e : n = 1 + 2 * C + (a + b) + 2 * (s * (a + b) + b) := by rw [← hn]; ring
  have hJ : (n - 1 - 2 * C - (a + b)) / 2 = s * (a + b) + b := by omega
  simp only [balOf, hJ]
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have h1 : (s * (0 + b) + b) / (0 + b) = s + 1 := by
      rw [show s * (0 + b) + b = (s + 1) * b by ring, zero_add, Nat.mul_div_cancel _ (by omega)]
    have h2 : (s * (0 + b) + b) % (0 + b) = 0 := by
      rw [show s * (0 + b) + b = (s + 1) * b by ring, zero_add, Nat.mul_mod_left]
    rw [h1, h2]
    simp [canon]
  · have h1 : (s * (a + b) + b) / (a + b) = s := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega)]; simp
    have h2 : (s * (a + b) + b) % (a + b) = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h2, show a + b - b = a by omega]

theorem balOf_sum (n C m : ℕ) (hm : 0 < m) : (balOf n C m).2.1 + (balOf n C m).2.2 = m := by
  unfold balOf
  simp only
  have := Nat.mod_lt ((n - 1 - 2 * C - m) / 2) hm
  omega

/-- **Balanced soundness**: every canonical configuration with `≥ 3` children on `n` vertices is `≤ T`
    once `checkBal n T` holds. -/
theorem bal_le (n : ℕ) (T : ℕ × ℕ) (hT : 0 < T.2) (hc : checkBal n T = true)
    (C s a b : ℕ) (hn : nv (canon C s a b) = n) (h3 : 3 ≤ C + a + b) :
    F (canon C s a b) ≤ (T.1 : ℚ) / T.2 := by
  have hn' := hn
  rw [nv_canon] at hn'
  have e : n = 1 + 2 * C + (a + b) + 2 * (s * (a + b) + b) := by rw [← hn']; ring
  unfold checkBal at hc
  rw [List.all_eq_true] at hc
  have hC0 := hc C (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hC0
  have hC := hC0 (a + b) (List.mem_range.mpr (by omega))
  have hcond : 3 ≤ C + (a + b) ∧ (n - 1 - 2 * C - (a + b)) % 2 = 0 := ⟨by omega, by omega⟩
  rw [if_pos hcond] at hC
  by_cases hm0 : a + b = 0
  · rw [if_pos hm0] at hC
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have heq : canon C s 0 0 = canon C 0 0 0 := by
      simp only [canon, List.replicate_zero, List.append_nil]
    rw [heq, F_canon_eq _ _ _ _ (by omega)]
    exact leND_sound (x := (fnum C 0 0 0, fden C 0 0 0)) (fden_pos _ _ _ _ (by omega)) hT hC
  · rw [if_neg hm0] at hC
    have hm : 0 < a + b := Nat.pos_of_ne_zero hm0
    rw [canon_eq_balOf n C s a b hn hm]
    have hsum : 0 < C + (balOf n C (a + b)).2.1 + (balOf n C (a + b)).2.2 := by
      have := balOf_sum n C (a + b) hm; omega
    rw [F_canon_eq _ _ _ _ hsum]
    exact leND_sound (x := (fnum C (balOf n C (a + b)).1 (balOf n C (a + b)).2.1 (balOf n C (a + b)).2.2,
      fden C (balOf n C (a + b)).1 (balOf n C (a + b)).2.1 (balOf n C (a + b)).2.2))
      (fden_pos _ _ _ _ hsum) hT hC

/-- **Spider-family optimum from the per-`n` check.**  If `checkBal n T` and `checkSmall n T` hold and
    `T` is the value of a configuration `t` on `n` vertices, then `t` maximizes `F` at size `n`. -/
theorem spider_opt_of_check (n : ℕ) (hn : 2 ≤ n) (t : List Child) (T : ℕ × ℕ) (hT : 0 < T.2)
    (hTt : F t = (T.1 : ℚ) / T.2) (hcb : checkBal n T = true) (hcs : checkSmall n T = true) :
    ∀ l : List Child, nv l = n → F l ≤ F t := by
  intro l hl
  obtain ⟨x, hx, hmax⟩ := exists_isMax n (by omega)
  have h1 : F l ≤ F x := hmax l (by rw [hl, hx])
  refine le_trans h1 ?_
  rw [hTt]
  by_cases h3 : 3 ≤ x.length
  · have hbal : ∀ j k : ℕ, Child.arm j ∈ x → Child.arm k ∈ x → j ≤ k + 1 :=
      fun j k hj hk => balanced_of_isMax x hmax h3 j k hj hk
    obtain ⟨C, s, a, b, hp⟩ := canon_of_balanced x hbal
    rw [F_perm hp]
    have hlen := hp.length_eq
    simp only [canon, List.length_append, List.length_replicate] at hlen
    exact bal_le n T hT hcb C s a b (by rw [← nv_perm hp, hx]) (by omega)
  · have hne : x ≠ [] := by
      intro h; rw [h] at hx; simp [nv] at hx; omega
    exact small_le n T hT hcs x hx (by omega) hne

end BGSpiderTable
end R3Cert
