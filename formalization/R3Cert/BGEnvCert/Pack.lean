/-
  R3Cert.BGEnvCert.Pack -- packed fixed-width lanes in one natural number (2026-09-25).

  `pk w n l = Σ_{i<n} l i · 2^(w·i)` stores `n` lanes of `w` bits in one `ℕ`.  The kernel does
  bignum arithmetic (GMP) on such numbers in time linear in their size, so one addition, shift or
  `&&&` acts on all lanes at once.  This file proves the lane semantics of the operations the
  envelope certificate uses: addition, subtraction without borrows, multiplication by a constant,
  shifts by whole lanes, truncation, extraction, bitwise and/or, the guarded comparison
  `(x + G) - y` (bit `w-1` of each lane says `y_i ≤ x_i`) and the lane-wise maximum `vmax`.
  No `sorry`; standard axioms only.
-/
import Mathlib

namespace R3Cert
namespace EnvCert

/-- `pk w n l = Σ_{i<n} l i * 2^(w*i)`: `n` lanes of width `w`. -/
def pk (w : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, l => l 0 + 2 ^ w * pk w n (fun i => l (i + 1))

theorem pk_zero (w : ℕ) (l : ℕ → ℕ) : pk w 0 l = 0 := rfl

theorem pk_succ (w n : ℕ) (l : ℕ → ℕ) : pk w (n + 1) l = l 0 + 2 ^ w * pk w n (fun i => l (i + 1)) := rfl

theorem pk_congr (w : ℕ) : ∀ (n : ℕ) {a b : ℕ → ℕ}, (∀ i < n, a i = b i) → pk w n a = pk w n b
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    rw [pk_succ, pk_succ, h 0 (by omega), pk_congr w n (fun i hi => h (i + 1) (by omega))]

theorem pk_add (w : ℕ) : ∀ (n : ℕ) (a b : ℕ → ℕ), pk w n a + pk w n b = pk w n (fun i => a i + b i)
  | 0, _, _ => rfl
  | n + 1, a, b => by
    rw [pk_succ, pk_succ, pk_succ, ← pk_add w n]; ring

theorem pk_mul (w : ℕ) : ∀ (n : ℕ) (a : ℕ → ℕ) (c : ℕ), pk w n a * c = pk w n (fun i => a i * c)
  | 0, _, _ => by simp [pk]
  | n + 1, a, c => by
    rw [pk_succ, pk_succ, ← pk_mul w n]; ring

theorem pk_const_zero (w : ℕ) : ∀ n : ℕ, pk w n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by rw [pk_succ, pk_const_zero w n]; simp

/-- All lanes below `2^w`. -/
def Bdd (w n : ℕ) (a : ℕ → ℕ) : Prop := ∀ i < n, a i < 2 ^ w

theorem pk_lt (w : ℕ) : ∀ (n : ℕ) (a : ℕ → ℕ), Bdd w n a → pk w n a < 2 ^ (w * n)
  | 0, _, _ => by simp [pk]
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    have ih := pk_lt w n (fun i => a (i + 1)) (fun i hi => h (i + 1) (by omega))
    rw [pk_succ, show w * (n + 1) = w + w * n by ring, pow_add]
    have : pk w n (fun i => a (i + 1)) + 1 ≤ 2 ^ (w * n) := ih
    nlinarith [Nat.one_le_two_pow (n := w)]

theorem pk_sub (w : ℕ) (n : ℕ) (a b : ℕ → ℕ) (h : ∀ i < n, b i ≤ a i) :
    pk w n a - pk w n b = pk w n (fun i => a i - b i) := by
  have := pk_add w n b (fun i => a i - b i)
  rw [pk_congr w n (a := fun i => b i + (a i - b i)) (b := a) (fun i hi => by have := h i hi; omega)] at this
  omega

/-- Concatenation: the first `m` lanes, then the rest. -/
theorem pk_append (w : ℕ) : ∀ (m n : ℕ) (a : ℕ → ℕ),
    pk w (m + n) a = pk w m a + 2 ^ (w * m) * pk w n (fun i => a (m + i))
  | 0, n, a => by simp [pk]
  | m + 1, n, a => by
    rw [show m + 1 + n = (m + n) + 1 by ring, pk_succ, pk_succ, pk_append w m n]
    simp only [show ∀ i, m + (i + 1) = (m + i) + 1 by intro i; ring, show ∀ i, m + 1 + i = (m + i) + 1 by
      intro i; ring]
    rw [show w * (m + 1) = w + w * m by ring, pow_add]; ring

private theorem add_mul_mod_aux {a b c d : ℕ} (ha : a < b) :
    (a + b * c) % (b * d) = a + b * (c % d) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  have hlt : a + b * (c % d) < b * d := by
    have : c % d + 1 ≤ d := Nat.mod_lt c hd
    nlinarith
  conv_lhs => rw [← Nat.mod_add_div c d]
  rw [show a + b * (c % d + d * (c / d)) = (a + b * (c % d)) + (b * d) * (c / d) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem add_mul_div_aux {a b c : ℕ} (ha : a < b) : (a + b * c) / b = c := by
  have hb : 0 < b := by omega
  rw [show a + b * c = a + c * b by ring, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ha, zero_add]

/-- Truncation to the first `m ≤ n` lanes. -/
theorem pk_mod (w : ℕ) (n : ℕ) (a : ℕ → ℕ) (ha : Bdd w n a) (m : ℕ) (hm : m ≤ n) :
    pk w n a % 2 ^ (w * m) = pk w m a := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [pk_append]
  have hlt := pk_lt w m a (fun i hi => ha i (by omega))
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Dropping the first `m ≤ n` lanes. -/
theorem pk_div (w : ℕ) (n : ℕ) (a : ℕ → ℕ) (ha : Bdd w n a) (m : ℕ) (hm : m ≤ n) :
    pk w n a / 2 ^ (w * m) = pk w (n - m) (fun i => a (m + i)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [pk_append, show m + k - m = k by omega]
  exact add_mul_div_aux (pk_lt w m a (fun i hi => ha i (by omega)))

/-- Lane extraction. -/
theorem pk_lane (w : ℕ) (n : ℕ) (a : ℕ → ℕ) (ha : Bdd w n a) (i : ℕ) (hi : i < n) :
    pk w n a / 2 ^ (w * i) % 2 ^ w = a i := by
  rw [pk_div w n a ha i hi.le]
  have hb : Bdd w (n - i) (fun j => a (i + j)) := fun j hj => ha (i + j) (by omega)
  have := pk_mod w (n - i) _ hb 1 (by omega)
  rw [mul_one] at this
  rw [this, pk_succ, pk_zero]; simp

/-- Two bounded packings agree iff their lanes agree. -/
theorem pk_inj (w : ℕ) (n : ℕ) (a b : ℕ → ℕ) (ha : Bdd w n a) (hb : Bdd w n b)
    (h : pk w n a = pk w n b) (i : ℕ) (hi : i < n) : a i = b i := by
  rw [← pk_lane w n a ha i hi, ← pk_lane w n b hb i hi, h]

/-- Shifting up by `m` whole lanes. -/
theorem pk_mul_pow (w : ℕ) : ∀ (m n : ℕ) (a : ℕ → ℕ),
    pk w n a * 2 ^ (w * m) = pk w (m + n) (fun i => if i < m then 0 else a (i - m))
  | 0, n, a => by simp
  | m + 1, n, a => by
    rw [show m + 1 + n = (m + n) + 1 by ring, pk_succ]
    simp only [show (0:ℕ) < m + 1 from by omega, if_true, zero_add]
    rw [show w * (m + 1) = w + w * m by ring, pow_add, ← mul_assoc, mul_comm (pk w n a) (2 ^ w),
      mul_assoc, pk_mul_pow w m n]
    congr 1
    apply pk_congr; intro i hi
    by_cases h : i < m
    · simp [h, show i + 1 < m + 1 by omega]
    · simp [h, show ¬ (i + 1 < m + 1) by omega, show i + 1 - (m + 1) = i - m by omega]

/-- Shift up by `m` lanes, then truncate to `n` lanes. -/
theorem pk_shift (w : ℕ) (n : ℕ) (a : ℕ → ℕ) (ha : Bdd w n a) (m : ℕ) :
    pk w n a * 2 ^ (w * m) % 2 ^ (w * n) = pk w n (fun i => if i < m then 0 else a (i - m)) := by
  rw [pk_mul_pow, pk_mod w (m + n) _ ?_ n (by omega)]
  intro i hi
  by_cases h : i < m
  · simp [h]
  · simp only [h, if_false]
    by_cases h2 : i - m < n
    · exact ha _ h2
    · -- lanes beyond `n` come from beyond the source; they are cut anyway, but we still need a bound
      have : i - m < n := by omega
      exact absurd this h2

/-- Every `v < 2^(w n)` is the packing of its own lanes. -/
theorem pk_self (w : ℕ) : ∀ (n v : ℕ), v < 2 ^ (w * n) → v = pk w n (fun i => v / 2 ^ (w * i) % 2 ^ w)
  | 0, v, h => by simp at h; simp [h, pk]
  | n + 1, v, h => by
    rw [pk_succ]
    have hv : v / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      rw [show w * n + w = w * (n + 1) by ring]; exact h
    have ih := pk_self w n (v / 2 ^ w) hv
    have e : (fun i => v / 2 ^ (w * (i + 1)) % 2 ^ w) = (fun i => v / 2 ^ w / 2 ^ (w * i) % 2 ^ w) := by
      funext i; rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
    simp only [mul_zero, pow_zero, Nat.div_one]
    rw [e, ← ih]
    exact (Nat.mod_add_div v (2 ^ w)).symm

theorem pk_lt_iff_bdd_lanes (w n v : ℕ) (h : v < 2 ^ (w * n)) :
    Bdd w n (fun i => v / 2 ^ (w * i) % 2 ^ w) := fun i _ => Nat.mod_lt _ (by positivity)

/-! ### Bitwise operations on packings. -/

private theorem land_split {w a b x y : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (a + 2 ^ w * x) &&& (b + 2 ^ w * y) = (a &&& b) + 2 ^ w * (x &&& y) := by
  apply Nat.eq_of_testBit_eq; intro k
  have hab : (a &&& b) < 2 ^ w := Nat.and_lt_two_pow a hb
  rw [Nat.testBit_and, add_comm a, add_comm b, add_comm (a &&& b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split_ifs <;> simp [Nat.testBit_and]

private theorem lor_split {w a b x y : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (a + 2 ^ w * x) ||| (b + 2 ^ w * y) = (a ||| b) + 2 ^ w * (x ||| y) := by
  apply Nat.eq_of_testBit_eq; intro k
  have hab : (a ||| b) < 2 ^ w := Nat.or_lt_two_pow ha hb
  rw [Nat.testBit_or, add_comm a, add_comm b, add_comm (a ||| b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split_ifs <;> simp [Nat.testBit_or]

theorem pk_land (w : ℕ) : ∀ (n : ℕ) (a b : ℕ → ℕ), Bdd w n a → Bdd w n b →
    pk w n a &&& pk w n b = pk w n (fun i => a i &&& b i)
  | 0, _, _, _, _ => by simp [pk]
  | n + 1, a, b, ha, hb => by
    rw [pk_succ, pk_succ, pk_succ, land_split (ha 0 (by omega)) (hb 0 (by omega)),
      pk_land w n _ _ (fun i hi => ha (i + 1) (by omega)) (fun i hi => hb (i + 1) (by omega))]

theorem pk_lor (w : ℕ) : ∀ (n : ℕ) (a b : ℕ → ℕ), Bdd w n a → Bdd w n b →
    pk w n a ||| pk w n b = pk w n (fun i => a i ||| b i)
  | 0, _, _, _, _ => by simp [pk]
  | n + 1, a, b, ha, hb => by
    rw [pk_succ, pk_succ, pk_succ, lor_split (ha 0 (by omega)) (hb 0 (by omega)),
      pk_lor w n _ _ (fun i hi => ha (i + 1) (by omega)) (fun i hi => hb (i + 1) (by omega))]

/-! ### Constant packings. -/

/-- `rep w n = Σ_{i<n} 2^(w i)`, computed in closed form. -/
def rep (w n : ℕ) : ℕ := (2 ^ (w * n) - 1) / (2 ^ w - 1)

theorem geom_aux (w : ℕ) : ∀ n : ℕ, (2 ^ w - 1) * pk w n (fun _ => 1) + 1 = 2 ^ (w * n)
  | 0 => by simp [pk]
  | n + 1 => by
    rw [pk_succ, show w * (n + 1) = w + w * n by ring, pow_add, ← geom_aux w n]
    have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    zify [this]
    ring

theorem rep_eq (w n : ℕ) (hw : 1 ≤ w) : rep w n = pk w n (fun _ => 1) := by
  unfold rep
  have hpos : 0 < 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    omega
  rw [← geom_aux w n, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hpos]

theorem pk_const (w n c : ℕ) (hw : 1 ≤ w) : c * rep w n = pk w n (fun _ => c) := by
  rw [rep_eq w n hw, mul_comm, pk_mul]; simp

/-! ### Guarded comparison and lane-wise maximum. -/

theorem half_lt (w : ℕ) (hw : 1 ≤ w) : 2 ^ (w - 1) * 2 = 2 ^ w := by
  rw [← pow_succ, Nat.sub_add_cancel hw]

/-- For `v < 2^w`: bit `w-1` of `v` is set iff `v ≥ 2^(w-1)`. -/
theorem testBit_top (w v : ℕ) (hw : 1 ≤ w) (hv : v < 2 ^ w) :
    v.testBit (w - 1) = decide (2 ^ (w - 1) ≤ v) := by
  have h2 := half_lt w hw
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hq : v / 2 ^ (w - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  by_cases hge : 2 ^ (w - 1) ≤ v
  · have : v / 2 ^ (w - 1) = 1 := by
      have := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ (w - 1))).mpr (by omega : 1 * 2 ^ (w - 1) ≤ v)
      omega
    simp [this, hge]
  · have : v / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, hge]

theorem land_top (w v : ℕ) (hw : 1 ≤ w) (hv : v < 2 ^ w) :
    v &&& 2 ^ (w - 1) = if 2 ^ (w - 1) ≤ v then 2 ^ (w - 1) else 0 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hk : w - 1 = k
  · subst hk
    rw [testBit_top w v hw hv]
    split_ifs with h <;> simp [h]
  · simp only [hk, decide_false, Bool.and_false]
    split_ifs <;> simp [hk]

/-- Lanes below `2^(w-1)`. -/
def Half (w n : ℕ) (a : ℕ → ℕ) : Prop := ∀ i < n, a i < 2 ^ (w - 1)

theorem Half.bdd {w n a} (hw : 1 ≤ w) (h : Half w n a) : Bdd w n a := fun i hi => by
  have := h i hi; have := half_lt w hw; omega

/-- The guard constant: every lane `2^(w-1)`. -/
def gd (w n : ℕ) : ℕ := 2 ^ (w - 1) * rep w n

/-- Guarded difference `(x + G) - y`. -/
def geD (w n x y : ℕ) : ℕ := x + gd w n - y

theorem geD_pk (w n : ℕ) (hw : 1 ≤ w) (a b : ℕ → ℕ) (ha : Half w n a) (hb : ∀ i < n, b i ≤ 2 ^ (w - 1)) :
    geD w n (pk w n a) (pk w n b) = pk w n (fun i => a i + 2 ^ (w - 1) - b i) := by
  unfold geD gd
  rw [pk_const w n _ hw, pk_add, pk_sub w n _ _ (fun i hi => by have := hb i hi; omega)]

theorem geD_bdd (w n : ℕ) (hw : 1 ≤ w) (a b : ℕ → ℕ) (ha : Half w n a) :
    Bdd w n (fun i => a i + 2 ^ (w - 1) - b i) := fun i hi => by
  have := ha i hi; have := half_lt w hw; show a i + 2 ^ (w - 1) - b i < 2 ^ w; omega

/-- Bit `w-1` of lane `i` of the guarded difference is `decide (b i ≤ a i)`. -/
theorem geD_top (w : ℕ) (hw : 1 ≤ w) (x y : ℕ) (hx : x < 2 ^ (w - 1)) (hy : y ≤ 2 ^ (w - 1)) :
    (x + 2 ^ (w - 1) - y).testBit (w - 1) = decide (y ≤ x) := by
  have := half_lt w hw
  rw [testBit_top w _ hw (by omega)]
  simp only [decide_eq_decide]; omega

/-- Lane-wise maximum of two packings with lanes `< 2^(w-1)`. -/
def vmax (w n x y : ℕ) : ℕ :=
  let s := (geD w n x y &&& gd w n) / 2 ^ (w - 1) * (2 ^ w - 1)
  (x &&& s) + (y &&& ((2 ^ w - 1) * rep w n - s))

theorem vmax_pk (w n : ℕ) (hw : 1 ≤ w) (a b : ℕ → ℕ) (ha : Half w n a) (hb : Half w n b) :
    vmax w n (pk w n a) (pk w n b) = pk w n (fun i => max (a i) (b i)) := by
  have h2 := half_lt w hw
  have hpos : 0 < 2 ^ (w - 1) := by positivity
  have hb' : ∀ i < n, b i ≤ 2 ^ (w - 1) := fun i hi => (hb i hi).le
  have hD := geD_pk w n hw a b ha hb'
  have hDb := geD_bdd w n hw a b ha
  have hG : gd w n = pk w n (fun _ => 2 ^ (w - 1)) := by unfold gd; exact pk_const w n _ hw
  have hGb : Bdd w n (fun _ => 2 ^ (w - 1)) := fun i _ => by show 2 ^ (w - 1) < 2 ^ w; omega
  -- the selector
  set sel : ℕ → ℕ := fun i => if b i ≤ a i then 1 else 0 with hsel
  have hAnd : geD w n (pk w n a) (pk w n b) &&& gd w n = pk w n (fun i => sel i * 2 ^ (w - 1)) := by
    rw [hD, hG, pk_land w n _ _ hDb hGb]
    apply pk_congr; intro i hi
    rw [land_top w _ hw (hDb i hi)]
    have := ha i hi
    by_cases h : b i ≤ a i
    · simp [hsel, h, show 2 ^ (w - 1) ≤ a i + 2 ^ (w - 1) - b i by omega]
    · simp [hsel, h, show ¬ (2 ^ (w - 1) ≤ a i + 2 ^ (w - 1) - b i) by omega]
  have hS : (geD w n (pk w n a) (pk w n b) &&& gd w n) / 2 ^ (w - 1) * (2 ^ w - 1)
      = pk w n (fun i => sel i * (2 ^ w - 1)) := by
    rw [hAnd, ← pk_mul w n sel, Nat.mul_div_cancel _ hpos, pk_mul]
  have hSb : Bdd w n (fun i => sel i * (2 ^ w - 1)) := fun i _ => by
    simp only [hsel]; split_ifs <;> omega
  have hAll : (2 ^ w - 1) * rep w n = pk w n (fun _ => 2 ^ w - 1) := pk_const w n _ hw
  have hab := Half.bdd hw ha
  have hbb := Half.bdd hw hb
  unfold vmax
  simp only
  rw [hS, hAll, pk_sub w n _ _ (fun i _ => by simp only [hsel]; split_ifs <;> omega),
    pk_land w n _ _ hab hSb, pk_land w n _ _ hbb (fun i _ => by omega), pk_add]
  apply pk_congr; intro i hi
  have hai := hab i hi
  have hbi := hbb i hi
  by_cases h : b i ≤ a i
  · simp only [hsel, h, if_true, one_mul, Nat.sub_self, Nat.and_zero, add_zero,
      Nat.and_two_pow_sub_one_of_lt_two_pow hai]
    exact (max_eq_left h).symm
  · simp only [hsel, h, if_false, zero_mul, Nat.and_zero, zero_add, Nat.sub_zero,
      Nat.and_two_pow_sub_one_of_lt_two_pow hbi]
    exact (max_eq_right (by omega)).symm

end EnvCert
end R3Cert
