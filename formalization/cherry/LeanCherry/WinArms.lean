/-
LeanCherry.WinArms -- the window [3.22, 1 + sqrt 5), part 1: the arms A_j and the best arm rate f*.

  c = 1 + l/2, s = sqrt c, y_ch = 1/(2+l), t = l y_ch = l/(2+l), sigma = t/(1+t), f_ch = log s (the cherry rate).
  T(A_j) = c^j (1 + t j/(j+1)),  f_j = f_ch + D_j/(2j+1),  D_j = log(1 + t j/(j+1)) - f_ch,  D_inf = log(1+t) - f_ch.
  Upper: f_j <= f_ch + D_inf^2/(4 sigma) (all j), so f* <= f_ch + D_inf^2/(4 sigma).
  Lower (D_inf > 0): f* > f_ch + D_inf^2/(2(4 sigma + 3 D_inf)), and the supremum f* is ATTAINED by some arm j >= 1.
-/
import LeanCherry.PartB

open Real

namespace LeanCherry

noncomputable section

open Br

def yC (l : ℝ) : ℝ := 1 / (2 + l)
def tC (l : ℝ) : ℝ := l / (2 + l)
def sC (l : ℝ) : ℝ := √(1 + l / 2)
def fch (l : ℝ) : ℝ := Real.log (sC l)
def sig (l : ℝ) : ℝ := tC l / (1 + tC l)
def Dinf (l : ℝ) : ℝ := Real.log (1 + tC l) - fch l
def Dj (l : ℝ) (j : ℕ) : ℝ := Real.log (1 + tC l * j / (j + 1)) - fch l

lemma sC_sq {l : ℝ} (hl : 0 ≤ l) : sC l ^ 2 = 1 + l / 2 := by
  unfold sC; rw [Real.sq_sqrt (by linarith)]

lemma sC_pos {l : ℝ} (hl : 0 ≤ l) : 0 < sC l := by
  unfold sC; exact Real.sqrt_pos.mpr (by linarith)

lemma tC_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ tC l := by unfold tC; positivity
lemma tC_lt_one {l : ℝ} (hl : 0 ≤ l) : tC l < 1 := by
  unfold tC; rw [div_lt_one (by linarith)]; linarith

lemma sig_pos {l : ℝ} (hl : 0 < l) : 0 < sig l := by
  unfold sig; have : 0 < tC l := by unfold tC; positivity
  positivity
lemma sig_lt_one {l : ℝ} (hl : 0 ≤ l) : sig l < 1 := by
  unfold sig; have := tC_nonneg hl
  rw [div_lt_one (by linarith)]; linarith

lemma ltC {l : ℝ} (hl : 0 ≤ l) : l * yC l = tC l := by unfold yC tC; field_simp

lemma msgl_cherry (l : ℝ) : msgl l cherry = yC l := by
  rw [cherry, msgl_node]
  simp only [sumYl, msgl_node, List.length_nil, List.length_cons, Nat.cast_zero, Nat.cast_one, mul_zero,
    add_zero, zero_add, yC]
  norm_num

lemma Tl_armB (l : ℝ) (j : ℕ) : Tl l (armB j) = (1 + l / 2) ^ j * (1 + l * (j * yC l) / (j + 1)) := by
  rw [armB, Tl_node, prodTl_eq_map, sumYl_eq_map]
  simp only [List.map_replicate, List.prod_replicate, List.sum_replicate, Tl_cherry, msgl_cherry,
    List.length_replicate, nsmul_eq_mul]

lemma msgl_armB (l : ℝ) (j : ℕ) : msgl l (armB j) = 1 / (j + 1 + l * (j * yC l)) := by
  rw [armB, msgl_node, sumYl_eq_map]
  simp only [List.map_replicate, List.sum_replicate, msgl_cherry, List.length_replicate, nsmul_eq_mul]

lemma log_c_eq {l : ℝ} (hl : 0 ≤ l) : Real.log (1 + l / 2) = 2 * fch l := by
  unfold fch; rw [← sC_sq hl, Real.log_pow]; push_cast; ring

lemma one_add_tj_pos {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : 0 < 1 + tC l * j / (j + 1) := by
  have := tC_nonneg hl; positivity

lemma fArm_eq {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : fArm l j = fch l + Dj l j / (2 * j + 1) := by
  unfold fArm Dj
  rw [Tl_armB]
  have e : l * (j * yC l) / (j + 1) = tC l * j / (j + 1) := by
    rw [← ltC hl]; ring
  rw [e, Real.log_mul (by positivity) (one_add_tj_pos hl j).ne', Real.log_pow, log_c_eq hl]
  field_simp
  ring

/-- 1 + t j/(j+1) = (1 + t)(1 - sigma/(j+1)) -/
lemma split_arm {l : ℝ} (hl : 0 ≤ l) (j : ℕ) :
    1 + tC l * j / (j + 1) = (1 + tC l) * (1 - sig l / (j + 1)) := by
  unfold sig; have := tC_nonneg hl
  field_simp; ring

lemma one_sub_sig_pos {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : 0 < 1 - sig l / (j + 1) := by
  have h1 := sig_lt_one hl
  have h2 : sig l / (j + 1) ≤ sig l := div_le_self (by unfold sig; have := tC_nonneg hl; positivity)
    (by have : (0:ℝ) ≤ j := (by positivity); linarith)
  linarith

lemma Dj_le {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : Dj l j ≤ Dinf l - sig l / (j + 1) := by
  unfold Dj Dinf
  rw [split_arm hl, Real.log_mul (by have := tC_nonneg hl; exact ne_of_gt (by linarith)) (one_sub_sig_pos hl j).ne']
  have := Real.log_le_sub_one_of_pos (one_sub_sig_pos hl j)
  linarith

lemma Dj_ge {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : Dinf l - sig l / (j + 1 - sig l) ≤ Dj l j := by
  unfold Dj Dinf
  rw [split_arm hl, Real.log_mul (by have := tC_nonneg hl; exact ne_of_gt (by linarith)) (one_sub_sig_pos hl j).ne']
  have hp := one_sub_sig_pos hl j
  have h := Real.one_sub_inv_le_log_of_pos hp
  have hX : 0 < (j : ℝ) + 1 - sig l := by have := sig_lt_one hl; have : (0:ℝ) ≤ j := (by positivity); linarith
  have e : 1 - (1 - sig l / (j + 1))⁻¹ = - (sig l / (j + 1 - sig l)) := by
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at h
  linarith

lemma Dj_le_Dinf {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : Dj l j ≤ Dinf l := by
  have := Dj_le hl j
  have : 0 ≤ sig l / (j + 1) := by unfold sig; have := tC_nonneg hl; positivity
  linarith

/-- every arm rate is at most f_ch + D_inf^2/(4 sigma) -/
lemma fArm_le {l : ℝ} (hl : 0 < l) (j : ℕ) : fArm l j ≤ fch l + Dinf l ^ 2 / (4 * sig l) := by
  rw [fArm_eq hl.le]
  have hs := sig_pos hl
  have hX : (1:ℝ) ≤ j + 1 := by have : (0:ℝ) ≤ j := (by positivity); linarith
  have hq : 0 ≤ Dinf l ^ 2 / (4 * sig l) := by positivity
  rcases le_or_gt (Dj l j) 0 with hD | hD
  · have : Dj l j / (2 * j + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hD (by positivity)
    linarith
  · have h1 : Dj l j / (2 * j + 1) ≤ Dj l j / (j + 1) :=
      div_le_div_of_nonneg_left hD.le (by positivity) (by have : (0:ℝ) ≤ j := (by positivity); linarith)
    have h2 : Dj l j / (j + 1) ≤ (Dinf l - sig l / (j + 1)) / (j + 1) :=
      div_le_div_of_nonneg_right (Dj_le hl.le j) (by positivity)
    set z : ℝ := 1 / ((j : ℝ) + 1) with hz
    have e : (Dinf l - sig l / (j + 1)) / (j + 1) = Dinf l * z - sig l * z ^ 2 := by
      rw [hz]; field_simp
    have h3 : Dinf l * z - sig l * z ^ 2 ≤ Dinf l ^ 2 / (4 * sig l) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Dinf l - 2 * sig l * z)]
    linarith

/-- tail bound: f_j <= f_ch + D_inf/(2j+1) -/
lemma fArm_le_tail {l : ℝ} (hl : 0 ≤ l) (j : ℕ) : fArm l j ≤ fch l + Dinf l / (2 * j + 1) := by
  rw [fArm_eq hl]
  have := div_le_div_of_nonneg_right (Dj_le_Dinf hl j) (by positivity : (0:ℝ) ≤ 2 * j + 1)
  linarith

/-! ### the supremum f* -/

def armSet (l : ℝ) : Set ℝ := {x | ∃ j : ℕ, 1 ≤ j ∧ x = fArm l j}

lemma armSet_bdd {l : ℝ} (hl : 0 < l) : BddAbove (armSet l) :=
  ⟨fch l + Dinf l ^ 2 / (4 * sig l), by rintro x ⟨j, _, rfl⟩; exact fArm_le hl j⟩

lemma armSet_nonempty (l : ℝ) : (armSet l).Nonempty := ⟨fArm l 1, 1, le_rfl, rfl⟩

lemma fstar_eq_sSup (l : ℝ) : fstar l = sSup (armSet l) := rfl

lemma fArm_le_fstar {l : ℝ} (hl : 0 < l) {j : ℕ} (hj : 1 ≤ j) : fArm l j ≤ fstar l :=
  le_csSup (armSet_bdd hl) ⟨j, hj, rfl⟩

lemma fstar_le {l : ℝ} (hl : 0 < l) : fstar l ≤ fch l + Dinf l ^ 2 / (4 * sig l) :=
  csSup_le (armSet_nonempty l) (by rintro x ⟨j, _, rfl⟩; exact fArm_le hl j)

/-- a good arm: f_j > f_ch + D_inf^2/(2(4 sigma + 3 D_inf)) -/
lemma exists_good_arm {l : ℝ} (hl : 0 < l) (hD : 0 < Dinf l) :
    ∃ j : ℕ, 1 ≤ j ∧ fch l + Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) < fArm l j := by
  have hs := sig_pos hl; have hs1 := sig_lt_one hl.le
  set q := 2 * sig l / Dinf l with hq
  have hq0 : 0 < q := by positivity
  set j := ⌈q⌉₊ with hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (by rw [hj]; exact (Nat.ceil_pos.mpr hq0).ne')
  have hjq : q ≤ j := Nat.le_ceil q
  have hjq' : (j : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0.le
  refine ⟨j, hj1, ?_⟩
  rw [fArm_eq hl.le]
  -- D_j > D_inf/2
  have hX : 0 < (j : ℝ) + 1 - sig l := by linarith
  have hsm : sig l / (j + 1 - sig l) < Dinf l / 2 := by
    rw [div_lt_iff₀ hX]
    have : q * Dinf l = 2 * sig l := by rw [hq]; field_simp
    nlinarith
  have hDj : Dinf l / 2 < Dj l j := by have := Dj_ge hl.le j; linarith
  -- 2j + 1 < 4 sigma/D + 3
  have h2j : (2 * j + 1 : ℝ) * Dinf l < 4 * sig l + 3 * Dinf l := by
    have : q * Dinf l = 2 * sig l := by rw [hq]; field_simp
    nlinarith
  have hpos : (0:ℝ) < 2 * j + 1 := by positivity
  have : Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) < Dj l j / (2 * j + 1) := by
    rw [div_lt_div_iff₀ (by positivity) hpos]
    nlinarith [mul_lt_mul_of_pos_left h2j (by positivity : (0:ℝ) < Dinf l)]
  linarith

/-- the supremum is attained by an arm -/
theorem fstar_attained {l : ℝ} (hl : 0 < l) (hD : 0 < Dinf l) : ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l := by
  obtain ⟨j0, hj0, hgood⟩ := exists_good_arm hl hD
  have hs := sig_pos hl
  set δ := Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) with hδ
  have hδ0 : 0 < δ := by positivity
  set J := j0 + ⌈Dinf l / δ⌉₊ with hJ
  obtain ⟨jm, hjm, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 J) (fArm l)
    ⟨j0, Finset.mem_Icc.mpr ⟨hj0, by omega⟩⟩
  have hj0m : fArm l j0 ≤ fArm l jm := hmax j0 (Finset.mem_Icc.mpr ⟨hj0, by omega⟩)
  have hall : ∀ j : ℕ, 1 ≤ j → fArm l j ≤ fArm l jm := by
    intro j hj
    by_cases hjJ : j ≤ J
    · exact hmax j (Finset.mem_Icc.mpr ⟨hj, hjJ⟩)
    · have hbig : Dinf l / δ < 2 * (j : ℝ) + 1 := by
        have h1 : Dinf l / δ ≤ ⌈Dinf l / δ⌉₊ := Nat.le_ceil _
        have h2 : (⌈Dinf l / δ⌉₊ : ℝ) ≤ J := by rw [hJ]; push_cast; linarith [(Nat.cast_nonneg j0 : (0:ℝ) ≤ j0)]
        have h3 : (J : ℝ) < j := by exact_mod_cast (not_le.mp hjJ)
        linarith
      have htail := fArm_le_tail hl.le j
      have : Dinf l / (2 * j + 1) < δ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ0] at hbig
        linarith
      linarith
  have hjm1 : 1 ≤ jm := (Finset.mem_Icc.mp hjm).1
  refine ⟨jm, hjm1, le_antisymm (fArm_le_fstar hl hjm1) ?_⟩
  exact csSup_le (armSet_nonempty l) (by rintro x ⟨j, hj, rfl⟩; exact hall j hj)

lemma fstar_gt {l : ℝ} (hl : 0 < l) (hD : 0 < Dinf l) :
    fch l + Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) < fstar l := by
  obtain ⟨j, hj, h⟩ := exists_good_arm hl hD
  exact lt_of_lt_of_le h (fArm_le_fstar hl hj)

lemma fch_le_fstar {l : ℝ} (hl : 0 < l) (hD : 0 < Dinf l) : fch l ≤ fstar l := by
  have := fstar_gt hl hD
  have : 0 ≤ Dinf l ^ 2 / (2 * (4 * sig l + 3 * Dinf l)) := by have := sig_pos hl; positivity
  linarith

end

end LeanCherry
