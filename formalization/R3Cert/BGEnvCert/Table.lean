/-
  R3Cert.BGEnvCert.Table -- packed 2-D tables and the kernel knapsack/Bellman primitives (2026-09-25).

  A table with `R` rows (sizes `0..R-1`) and `H` columns (price grid points) is one packing of
  `H*R` lanes, lane `H*N + h` = entry `(N, h)`.  This file defines the kernel-side operations
  (row shift, row broadcast, the max-plus knapsack fold `fold2`, the Bellman lane check `bchk`)
  and proves their lane semantics.  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Pack

namespace R3Cert
namespace EnvCert

/-- `v` packs `n` lanes `a`, all `< B`. -/
def Rep (w n v B : ℕ) (a : ℕ → ℕ) : Prop := v = pk w n a ∧ ∀ i < n, a i < B

theorem Rep.bdd {w n v B a} (h : Rep w n v B a) (hB : B ≤ 2 ^ w) : Bdd w n a :=
  fun i hi => lt_of_lt_of_le (h.2 i hi) hB

theorem Rep.half {w n v B a} (h : Rep w n v B a) (hB : B ≤ 2 ^ (w - 1)) : Half w n a :=
  fun i hi => lt_of_lt_of_le (h.2 i hi) hB

theorem pow_half_le (w : ℕ) : 2 ^ (w - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### Blocks, truncation, broadcast. -/

theorem pk_block (w H : ℕ) : ∀ (R : ℕ) (a : ℕ → ℕ),
    pk (w * H) R (fun N => pk w H (fun h => a (H * N + h))) = pk w (H * R) a
  | 0, a => by simp [pk]
  | R + 1, a => by
    rw [pk_succ, show H * (R + 1) = H + H * R by ring, pk_append w H (H * R) a,
      ← pk_block w H R (fun i => a (H + i))]
    congr 1
    · apply pk_congr; intro h _; simp
    · congr 1
      apply pk_congr; intro N _
      apply pk_congr; intro h _
      congr 1; ring

theorem pk_trunc (w n : ℕ) (a : ℕ → ℕ) (ha : Bdd w n a) (m : ℕ) (hm : m ≤ n) :
    pk w n a % 2 ^ (w * m) = pk w n (fun i => if i < m then a i else 0) := by
  rw [pk_mod w n a ha m hm]
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [pk_append, pk_congr w m (a := fun i => if i < m then a i else 0) (b := a) (fun i hi => by simp [hi]),
    pk_congr w k (a := fun i => if m + i < m then a (m + i) else 0) (b := fun _ => 0) (fun i _ => by simp),
    pk_const_zero]
  ring

theorem pk_hi (w n : ℕ) (a : ℕ → ℕ) (ha : Bdd w n a) (m : ℕ) (hm : m ≤ n) :
    pk w n a / 2 ^ (w * m) * 2 ^ (w * m) = pk w n (fun i => if i < m then 0 else a i) := by
  rw [pk_div w n a ha m hm, pk_mul_pow, show m + (n - m) = n by omega]
  apply pk_congr; intro i hi
  split_ifs with h
  · rfl
  · congr 1; omega

/-- A single lane `g < H` set to one. -/
theorem unit_row (w H g : ℕ) (hg : g < H) : 2 ^ (w * g) = pk w H (fun h => if h = g then 1 else 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, H = g + (k + 1) := ⟨H - g - 1, by omega⟩
  rw [pk_append, pk_congr w g (a := fun h => if h = g then 1 else 0) (b := fun _ => 0)
    (fun i hi => by simp [show i ≠ g by omega]), pk_const_zero, pk_succ,
    pk_congr w k (a := fun i => if g + (i + 1) = g then 1 else 0) (b := fun _ => 0) (fun i _ => by simp),
    pk_const_zero]
  simp

/-- Broadcast of an `H`-lane row to all `R` rows. -/
def bcr (w H R r : ℕ) : ℕ := r * rep (w * H) R

theorem bcr_pk (w H R : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H) (rl : ℕ → ℕ) :
    bcr w H R (pk w H rl) = pk w (H * R) (fun i => rl (i % H)) := by
  unfold bcr
  rw [pk_const (w * H) R _ (by nlinarith), ← pk_block]
  apply pk_congr; intro N _
  apply pk_congr; intro h hh
  show rl h = rl ((H * N + h) % H)
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh]

/-- Row `m` of a table. -/
def rowv (w H T m : ℕ) : ℕ := T / 2 ^ (w * (H * m)) % 2 ^ (w * H)

theorem rowv_pk (w H R : ℕ) (a : ℕ → ℕ) (ha : Bdd w (H * R) a) (m : ℕ) (hm : m < R) :
    rowv w H (pk w (H * R) a) m = pk w H (fun h => a (H * m + h)) := by
  unfold rowv
  have hle : H * m ≤ H * R := Nat.mul_le_mul_left _ hm.le
  rw [pk_div w _ a ha _ hle]
  have hb : Bdd w (H * R - H * m) (fun i => a (H * m + i)) := fun i hi => ha _ (by omega)
  rw [pk_mod w _ _ hb H (by
    have : H * m + H ≤ H * R := by nlinarith
    omega)]

/-- Shift a table up by `m` rows (truncated). -/
def shR (w H R T m : ℕ) : ℕ := T * 2 ^ (w * (H * m)) % 2 ^ (w * (H * R))

/-- One knapsack term: table `A` shifted by `m` rows plus row `m` of `B` broadcast. -/
def term (w H R A B m : ℕ) : ℕ := shR w H R A m + bcr w H R (rowv w H B m)

theorem term_pk (w H R : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H) (a b : ℕ → ℕ) (ha : Bdd w (H * R) a)
    (hb : Bdd w (H * R) b) (m : ℕ) (hm : m < R) :
    term w H R (pk w (H * R) a) (pk w (H * R) b) m
      = pk w (H * R) (fun i => (if i < H * m then 0 else a (i - H * m)) + b (H * m + i % H)) := by
  unfold term shR
  rw [pk_shift w _ a ha, rowv_pk w H R b hb m hm, bcr_pk w H R hw hH, pk_add]

/-- Lane arithmetic for `i = H*N + h`. -/
theorem lane_idx {H N h m : ℕ} (hh : h < H) (hm : m ≤ N) :
    ¬ (H * N + h < H * m) ∧ H * N + h - H * m = H * (N - m) + h ∧ (H * N + h) % H = h := by
  refine ⟨?_, ?_, ?_⟩
  · have : H * m ≤ H * N := Nat.mul_le_mul_left _ hm
    omega
  · rw [Nat.mul_sub]; have : H * m ≤ H * N := Nat.mul_le_mul_left _ hm; omega
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh]

/-! ### The knapsack fold. -/

/-- `acc ← max(acc, term A1 B1 m)`, and `max(acc, term A2 B2 m)` when `use2 m`, for `m = j, ..., 1`. -/
def fold2 (w H R A1 B1 A2 B2 : ℕ) (use2 : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | j + 1, acc =>
    fold2 w H R A1 B1 A2 B2 use2 j
      (if use2 (j + 1) then
        vmax w (H * R) (vmax w (H * R) acc (term w H R A1 B1 (j + 1))) (term w H R A2 B2 (j + 1))
      else vmax w (H * R) acc (term w H R A1 B1 (j + 1)))

theorem vmax_rep {w n x y B : ℕ} {a b : ℕ → ℕ} (hw : 1 ≤ w) (hB : B ≤ 2 ^ (w - 1))
    (hx : Rep w n x B a) (hy : Rep w n y B b) :
    Rep w n (vmax w n x y) B (fun i => max (a i) (b i)) := by
  refine ⟨?_, fun i hi => max_lt (hx.2 i hi) (hy.2 i hi)⟩
  rw [hx.1, hy.1]; exact vmax_pk w n hw a b (hx.half hB) (hy.half hB)

theorem term_rep {w H R A B Ba Bb : ℕ} {a b : ℕ → ℕ} (hw : 1 ≤ w) (hH : 1 ≤ H)
    (hBa : Ba ≤ 2 ^ w) (hBb : Bb ≤ 2 ^ w) (hA : Rep w (H * R) A Ba a) (hB : Rep w (H * R) B Bb b)
    (m : ℕ) (hm : m < R) :
    Rep w (H * R) (term w H R A B m) (Ba + Bb)
      (fun i => (if i < H * m then 0 else a (i - H * m)) + b (H * m + i % H)) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hA.1, hB.1]; exact term_pk w H R hw hH a b (hA.bdd hBa) (hB.bdd hBb) m hm
  · have h2 : H * m + i % H < H * R := by
      have : i % H < H := Nat.mod_lt _ (by omega)
      have : H * m + H ≤ H * R := by nlinarith
      omega
    have := hB.2 _ h2
    dsimp only
    split_ifs with h
    · omega
    · have := hA.2 (i - H * m) (by omega); omega

theorem fold2_spec (w H R : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H) {A1 B1 A2 B2 Ba Bb : ℕ}
    {a1 b1 a2 b2 : ℕ → ℕ} (hB : Ba + Bb ≤ 2 ^ (w - 1))
    (hA1 : Rep w (H * R) A1 Ba a1) (hB1 : Rep w (H * R) B1 Bb b1)
    (hA2 : Rep w (H * R) A2 Ba a2) (hB2 : Rep w (H * R) B2 Bb b2) (use2 : ℕ → Bool) :
    ∀ (j acc : ℕ) (ac : ℕ → ℕ), j < R → Rep w (H * R) acc (Ba + Bb) ac →
      ∃ L, Rep w (H * R) (fold2 w H R A1 B1 A2 B2 use2 j acc) (Ba + Bb) L ∧
        (∀ i < H * R, ac i ≤ L i) ∧
        ∀ m, 1 ≤ m → m ≤ j → ∀ N < R, ∀ h < H, m ≤ N →
          a1 (H * (N - m) + h) + b1 (H * m + h) ≤ L (H * N + h) ∧
          (use2 m = true → a2 (H * (N - m) + h) + b2 (H * m + h) ≤ L (H * N + h)) := by
  have hBw : Ba + Bb ≤ 2 ^ w := le_trans hB (pow_half_le w)
  have hBa : Ba ≤ 2 ^ w := by omega
  have hBb : Bb ≤ 2 ^ w := by omega
  intro j
  induction j with
  | zero =>
    intro acc ac _ hacc
    exact ⟨ac, hacc, fun _ _ => le_rfl, fun m h1 h2 => by omega⟩
  | succ j ih =>
    intro acc ac hj hacc
    have ht1 := term_rep hw hH hBa hBb hA1 hB1 (j + 1) hj
    have ht2 := term_rep hw hH hBa hBb hA2 hB2 (j + 1) hj
    have h1 := vmax_rep hw hB hacc ht1
    -- the new accumulator
    set t1 : ℕ → ℕ := fun i => (if i < H * (j + 1) then 0 else a1 (i - H * (j + 1))) + b1 (H * (j + 1) + i % H)
    set t2 : ℕ → ℕ := fun i => (if i < H * (j + 1) then 0 else a2 (i - H * (j + 1))) + b2 (H * (j + 1) + i % H)
    have key : ∃ ac', Rep w (H * R)
        (if use2 (j + 1) then
          vmax w (H * R) (vmax w (H * R) acc (term w H R A1 B1 (j + 1))) (term w H R A2 B2 (j + 1))
        else vmax w (H * R) acc (term w H R A1 B1 (j + 1))) (Ba + Bb) ac' ∧
        (∀ i < H * R, ac i ≤ ac' i ∧ t1 i ≤ ac' i ∧ (use2 (j + 1) = true → t2 i ≤ ac' i)) := by
      by_cases hu : use2 (j + 1) = true
      · refine ⟨_, by rw [if_pos hu]; exact vmax_rep hw hB h1 ht2, fun i _ => ⟨?_, ?_, fun _ => ?_⟩⟩
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · exact le_trans (le_max_right _ _) (le_max_left _ _)
        · exact le_max_right _ _
      · refine ⟨_, by rw [if_neg hu]; exact h1, fun i _ => ⟨le_max_left _ _, le_max_right _ _,
          fun h => absurd h hu⟩⟩
    obtain ⟨ac', hrep', hmono'⟩ := key
    obtain ⟨L, hL, hmono, hterms⟩ := ih _ ac' (by omega) hrep'
    refine ⟨L, hL, fun i hi => le_trans (hmono' i hi).1 (hmono i hi), ?_⟩
    intro m hm1 hm2 N hN h hh hmN
    rcases Nat.lt_or_ge m (j + 1) with hlt | hge
    · exact hterms m hm1 (by omega) N hN h hh hmN
    · have hmj : m = j + 1 := by omega
      subst hmj
      have hi : H * N + h < H * R := by
        have : H * N + H ≤ H * R := by nlinarith
        omega
      obtain ⟨hn1, hn2, hn3⟩ := lane_idx (H := H) hh hmN
      refine ⟨?_, fun hu => ?_⟩
      · have := (hmono' _ hi).2.1
        simp only [t1, hn1, if_false, hn2, hn3] at this
        exact le_trans this (hmono _ hi)
      · have := (hmono' _ hi).2.2 hu
        simp only [t2, hn1, if_false, hn2, hn3] at this
        exact le_trans this (hmono _ hi)

/-! ### Rows kept / rows dropped. -/

/-- Row `2` removed (kept rows `0, 1` and `≥ 3`). -/
def dropRow2 (w H T : ℕ) : ℕ := T % 2 ^ (w * (H * 2)) + T / 2 ^ (w * (H * 3)) * 2 ^ (w * (H * 3))

/-- Rows `≥ 3` only. -/
def keepGe3 (w H T : ℕ) : ℕ := T / 2 ^ (w * (H * 3)) * 2 ^ (w * (H * 3))

theorem dropRow2_rep {w H R T B : ℕ} {a : ℕ → ℕ} (hB : B ≤ 2 ^ w) (hR : 3 ≤ R)
    (hT : Rep w (H * R) T B a) :
    Rep w (H * R) (dropRow2 w H T) B (fun i => if H * 2 ≤ i ∧ i < H * 3 then 0 else a i) := by
  have hab := hT.bdd hB
  refine ⟨?_, fun i hi => ?_⟩
  · unfold dropRow2
    rw [hT.1, pk_trunc w _ a hab _ (by nlinarith), pk_hi w _ a hab _ (by nlinarith), pk_add]
    apply pk_congr; intro i _
    by_cases h1 : i < H * 2
    · have : i < H * 3 := by omega
      simp [h1, this]
    · by_cases h2 : i < H * 3
      · simp [h1, h2]
      · simp [h1, h2]
  · have := hT.2 i hi
    dsimp only
    split_ifs <;> omega

theorem keepGe3_rep {w H R T B : ℕ} {a : ℕ → ℕ} (hB : B ≤ 2 ^ w) (hR : 3 ≤ R)
    (hT : Rep w (H * R) T B a) :
    Rep w (H * R) (keepGe3 w H T) B (fun i => if i < H * 3 then 0 else a i) := by
  have hab := hT.bdd hB
  refine ⟨?_, fun i hi => ?_⟩
  · unfold keepGe3; rw [hT.1, pk_hi w _ a hab _ (by nlinarith)]
  · have := hT.2 i hi
    dsimp only
    split_ifs <;> omega

/-! ### The Bellman lane check. -/

/-- The column-`g` indicator broadcast over all rows. -/
def colu (w H R g : ℕ) : ℕ := bcr w H R (2 ^ (w * g))

theorem colu_pk (w H R g : ℕ) (hw : 1 ≤ w) (hg : g < H) :
    colu w H R g = pk w (H * R) (fun i => if i % H = g then 1 else 0) := by
  unfold colu
  rw [unit_row w H g hg, bcr_pk w H R hw (by omega)]

/-- The guarded difference for one witness `(h, B)`: lanes of `Wt + B·[col g]` against the
    table `T` shifted by `H + g - h` lanes (so lane `(s, g)` sees `T(s-1, h)`), plus `off`. -/
def bterm (w H R off T Wt g : ℕ) (p : ℕ × ℕ) : ℕ :=
  geD w (H * R) (Wt + p.2 * colu w H R g)
    (T * 2 ^ (w * (H + g - p.1)) % 2 ^ (w * (H * R)) + off * rep w (H * R))

/-- **The Bellman lane check**: for every row `s ≥ lo`, some witness `(h, B)` has
    `T(s-1, h) + off ≤ Wt(s, g) + B`. -/
def bchk (w H R off T Wt g lo : ℕ) (hs : List (ℕ × ℕ)) : Bool :=
  let M := 2 ^ (w - 1) * (colu w H R g / 2 ^ (w * (H * lo)) * 2 ^ (w * (H * lo)))
  ((hs.foldl (fun acc p => acc ||| bterm w H R off T Wt g p) 0) &&& M) == M

theorem land_top_eq {w v : ℕ} (hw : 1 ≤ w) (hv : v < 2 ^ w) (h : v &&& 2 ^ (w - 1) = 2 ^ (w - 1)) :
    v.testBit (w - 1) = true := by
  rw [land_top w v hw hv] at h
  rw [testBit_top w v hw hv]
  split_ifs at h with h1
  · simpa using h1
  · exact absurd h.symm (by positivity)

theorem bchk_spec (w H R off : ℕ) (hw : 2 ≤ w) (hH : 1 ≤ H) {T Wt Bt Bw : ℕ} {t wt : ℕ → ℕ}
    (hT : Rep w (H * R) T Bt t) (hW : Rep w (H * R) Wt Bw wt) (hoff : Bt + off ≤ 2 ^ (w - 1))
    (g lo : ℕ) (hg : g < H) (hlo : 1 ≤ lo) (hs : List (ℕ × ℕ))
    (hhs : ∀ p ∈ hs, p.1 < H ∧ Bw + p.2 ≤ 2 ^ (w - 1))
    (hchk : bchk w H R off T Wt g lo hs = true) :
    ∀ s, lo ≤ s → s < R → ∃ p ∈ hs, t (H * (s - 1) + p.1) + off ≤ wt (H * s + g) + p.2 := by
  have hw1 : 1 ≤ w := by omega
  have h2 := half_lt w hw1
  set n := H * R with hn
  have hTb := hT.bdd (by have := pow_half_le w; omega)
  -- lanes of one witness term
  have hterm : ∀ p ∈ hs, ∃ d : ℕ → ℕ, bterm w H R off T Wt g p = pk w n d ∧ Bdd w n d ∧
      ∀ i < n, (d i).testBit (w - 1) = true →
        (if i < H + g - p.1 then 0 else t (i - (H + g - p.1))) + off
          ≤ wt i + p.2 * (if i % H = g then 1 else 0) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hhs p hp
    set X : ℕ → ℕ := fun i => wt i + p.2 * (if i % H = g then 1 else 0)
    set Y : ℕ → ℕ := fun i => (if i < H + g - p.1 then 0 else t (i - (H + g - p.1))) + off
    have hXh : Half w n X := fun i hi => by
      have := hW.2 i hi
      show wt i + p.2 * (if i % H = g then 1 else 0) < 2 ^ (w - 1)
      split_ifs <;> omega
    have hYb : ∀ i < n, Y i ≤ 2 ^ (w - 1) := fun i hi => by
      show (if i < H + g - p.1 then 0 else t (i - (H + g - p.1))) + off ≤ 2 ^ (w - 1)
      split_ifs with h
      · omega
      · have : i - (H + g - p.1) < n := by omega
        have := hT.2 _ this; omega
    have hX : Wt + p.2 * colu w H R g = pk w n X := by
      rw [hW.1, colu_pk w H R g hw1 hg, mul_comm, pk_mul, pk_add]
      apply pk_congr; intro i _; simp only [X]; ring
    have hY : T * 2 ^ (w * (H + g - p.1)) % 2 ^ (w * n) + off * rep w n = pk w n Y := by
      rw [hT.1, pk_shift w n t hTb, pk_const w n off hw1, pk_add]
    refine ⟨fun i => X i + 2 ^ (w - 1) - Y i, ?_, geD_bdd w n hw1 X Y hXh, fun i hi hb => ?_⟩
    · unfold bterm; rw [hX, hY]; exact geD_pk w n hw1 X Y hXh hYb
    · rw [geD_top w hw1 _ _ (hXh i hi) (hYb i hi)] at hb
      exact of_decide_eq_true hb
  -- the accumulated `|||`
  have hfold : ∀ (l : List (ℕ × ℕ)), (∀ p ∈ l, p ∈ hs) → ∀ (acc : ℕ) (ac : ℕ → ℕ),
      acc = pk w n ac → Bdd w n ac →
      ∃ d : ℕ → ℕ, l.foldl (fun acc p => acc ||| bterm w H R off T Wt g p) acc = pk w n d ∧ Bdd w n d ∧
        ∀ i < n, (d i).testBit (w - 1) = true → (ac i).testBit (w - 1) = true ∨
          ∃ p ∈ l, (if i < H + g - p.1 then 0 else t (i - (H + g - p.1))) + off
            ≤ wt i + p.2 * (if i % H = g then 1 else 0) := by
    intro l
    induction l with
    | nil => intro _ acc ac hacc hb; exact ⟨ac, hacc, hb, fun i _ h => Or.inl h⟩
    | cons p l ih =>
      intro hl acc ac hacc hb
      obtain ⟨d, hd, hdb, hdt⟩ := hterm p (hl p (by simp))
      have hor : acc ||| bterm w H R off T Wt g p = pk w n (fun i => ac i ||| d i) := by
        rw [hacc, hd, pk_lor w n _ _ hb hdb]
      obtain ⟨e, he, heb, het⟩ := ih (fun q hq => hl q (by simp [hq])) _ _ hor
        (fun i hi => Nat.or_lt_two_pow (hb i hi) (hdb i hi))
      refine ⟨e, by simpa [List.foldl_cons] using he, heb, fun i hi hbit => ?_⟩
      rcases het i hi hbit with h | ⟨q, hq, hq2⟩
      · rw [Nat.testBit_or] at h
        rcases Bool.or_eq_true_iff.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨p, by simp, hdt i hi h⟩
      · exact Or.inr ⟨q, by simp [hq], hq2⟩
  obtain ⟨d, hd, hdb, hdt⟩ := hfold hs (fun p hp => hp) 0 (fun _ => 0) (pk_const_zero w n).symm
    (fun i _ => by positivity)
  -- the mask
  have hcol := colu_pk w H R g hw1 hg
  have hcb : Bdd w n (fun i => if i % H = g then 1 else 0) := fun i _ => by
    show (if i % H = g then 1 else 0) < 2 ^ w
    split_ifs <;> [exact Nat.one_lt_two_pow (by omega); positivity]
  have hM : 2 ^ (w - 1) * (colu w H R g / 2 ^ (w * (H * lo)) * 2 ^ (w * (H * lo)))
      = pk w n (fun i => if i < H * lo then 0 else (if i % H = g then 1 else 0) * 2 ^ (w - 1)) := by
    by_cases hloR : lo ≤ R
    · rw [hcol, pk_hi w n _ hcb _ (Nat.mul_le_mul_left _ hloR), mul_comm, pk_mul]
      apply pk_congr; intro i _; split_ifs <;> simp
    · -- `lo > R`: the mask is empty on both sides
      have hlt : pk w n (fun i => if i % H = g then 1 else 0) < 2 ^ (w * (H * lo)) :=
        lt_of_lt_of_le (pk_lt w n _ hcb) (Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))))
      rw [hcol, Nat.div_eq_of_lt hlt, zero_mul, mul_zero,
        pk_congr w n (b := fun _ => 0) (fun i hi => by
          have : i < H * lo := lt_of_lt_of_le hi (Nat.mul_le_mul_left _ (by omega))
          simp [this]), pk_const_zero]
  have hMb : Bdd w n (fun i => if i < H * lo then 0 else (if i % H = g then 1 else 0) * 2 ^ (w - 1)) :=
    fun i _ => by
      show (if i < H * lo then 0 else (if i % H = g then 1 else 0) * 2 ^ (w - 1)) < 2 ^ w
      have := Nat.one_le_two_pow (n := w)
      split_ifs <;> omega
  unfold bchk at hchk
  simp only [beq_iff_eq] at hchk
  rw [hd, hM, pk_land w n _ _ hdb hMb] at hchk
  intro s hs1 hs2
  have hsR : H * s + g < n := by
    have : H * s + H ≤ H * R := by nlinarith
    omega
  have hlane := pk_inj w n _ _ (fun i hi => Nat.and_lt_two_pow _ (hMb i hi)) hMb hchk _ hsR
  have hmod : (H * s + g) % H = g := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg]
  have hge : ¬ (H * s + g < H * lo) := by
    have : H * lo ≤ H * s := Nat.mul_le_mul_left _ hs1
    omega
  simp only [hge, if_false, hmod, if_true, one_mul] at hlane
  have hbit := land_top_eq hw1 (hdb _ hsR) hlane
  rcases hdt _ hsR hbit with h0 | ⟨p, hp, hle⟩
  · simp at h0
  · refine ⟨p, hp, ?_⟩
    have hp1 := (hhs p hp).1
    have hnlt : ¬ (H * s + g < H + g - p.1) := by
      have : H ≤ H * s := by nlinarith
      omega
    have hidx : H * s + g - (H + g - p.1) = H * (s - 1) + p.1 := by
      rw [Nat.mul_sub, mul_one]
      have : H ≤ H * s := by nlinarith
      omega
    simp only [hnlt, if_false, hidx, hmod, if_true, mul_one] at hle
    exact hle

end EnvCert
end R3Cert
