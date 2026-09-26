/-
  The D2 j-tail of the multi-child sweep, formalized.

  After the Jensen reduction, the j-tail (nodes with many children, j > 500) is the second explicit tail of the
  sweep (alongside the s-tail D1 in Sweep.lean).  For a node whose j children are all near-stars (child amplitude
  `g(s')`, cavity `3/(4s'+3)`), the coupling log is linearised by `log(1+x) <= x`, giving the elementary bound
  (paper's `U(s,j)`):
      Q <= (s*omega + lambda) + sum_l [ g(s'_l) + (3*mu_l - 1)/B ],    B = 4(s+j)+3,
  where `s*omega + lambda` is the j-independent node-head bound (`node_head_le`).  Each per-child bracket is
  `<= -(3/5)/B` (an exact rational once the five relevant near-star amplitudes `g(0..4)` are boxed below 0 by
  rigorous log enclosures and `g(k) <= 0` handles k >= 5), so the sum is `<= -3j/(5B)`, and the closure
      s*omega + lambda - 3j/(5B) <= omega   for s <= 64, j >= 501
  holds via the enclosure `-omega + lambda <= 1503/11315` and the EXACT integer corner
      3885 * 501 = 30060 * 64 + 22545
  (the razor-thin "+1e-4 margin" of the interval certificate is this integer equality).  All machine-checked,
  no sorry.
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.Jensen

namespace R3Cert

open Real

/-! ## Rigorous rational bounds on `log(1-x)` via its truncated Taylor series. -/

/-- Upper bound: `log(1-x) <= -S + E`, `S` the degree-`n` Taylor sum, `E` the explicit remainder. -/
theorem log_one_sub_le (x : ℝ) (n : ℕ) (hx : |x| < 1) (S E : ℝ)
    (hS : (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) = S)
    (hE : |x| ^ (n + 1) / (1 - |x|) = E) :
    Real.log (1 - x) ≤ -S + E := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [hS, hE, abs_le] at h; linarith [h.2]

/-- Lower bound: `-S - E <= log(1-x)`. -/
theorem log_one_sub_ge (x : ℝ) (n : ℕ) (hx : |x| < 1) (S E : ℝ)
    (hS : (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) = S)
    (hE : |x| ^ (n + 1) / (1 - |x|) = E) :
    -S - E ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [hS, hE, abs_le] at h; linarith [h.1]

/-! ## The base-`log` reductions (shared). -/

theorem log_three_half_id : Real.log (3 / 2) = Real.log 3 - Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num)]

theorem log_621_id : Real.log (621 / 64) = 4 * Real.log 3 - 3 * Real.log 2 + Real.log (1 - 1 / 24) := by
  rw [show (621 / 64 : ℝ) = 3 ^ 4 * (1 - 1 / 24) / 2 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast; ring

/-! ## `11*omega + lambda <= 0` (the `n >= 11` tail rate is negative), and `g(n) <= 0` for all `n`. -/

/-- `11*omega + lambda <= 0`, from the integer crux `3^41 * 2^39 <= 23^23`. -/
theorem eleven_omega_lam_nonpos : 11 * omegaVal + lambdaVal ≤ 0 := by
  have l32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := log_three_half_id
  have l43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have l621 : Real.log (621 / 64) = 3 * Real.log 3 + Real.log 23 - 6 * Real.log 2 := by
    rw [show (621 / 64 : ℝ) = 3 ^ 3 * 23 / 2 ^ 6 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have crux : (3 : ℝ) ^ 41 * 2 ^ 39 ≤ 23 ^ 23 := by
    have : (3 : ℕ) ^ 41 * 2 ^ 39 ≤ 23 ^ 23 := by norm_num
    exact_mod_cast this
  have hlog : 41 * Real.log 3 + 39 * Real.log 2 ≤ 23 * Real.log 23 := by
    have e : 41 * Real.log 3 + 39 * Real.log 2 = Real.log ((3 : ℝ) ^ 41 * 2 ^ 39) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    have e2 : (23 : ℝ) * Real.log 23 = Real.log ((23 : ℝ) ^ 23) := by rw [Real.log_pow]; push_cast; ring
    rw [e, e2]; exact Real.log_le_log (by positivity) crux
  have key : 11 * (11 * omegaVal + lambdaVal) = 41 * Real.log 3 + 39 * Real.log 2 - 23 * Real.log 23 := by
    unfold omegaVal lambdaVal Lval; rw [l32, l43, l621]; ring
  linarith [key, hlog]

/-- **`g(n) <= 0` for all `n`** (the near-star amplitude is non-positive).  Finite check for `n <= 10`
    (`Rval n <= 1`); for `n >= 11` the linear-rate bound `g(n) <= n*omega + lambda <= 11*omega + lambda <= 0`. -/
theorem gVal_nonpos (n : ℕ) : gVal n ≤ 0 := by
  rcases lt_or_ge n 11 with h | h
  · have hpos : 0 < Rval n := by unfold Rval; positivity
    have hR : Rval n ≤ 1 := by interval_cases n <;> (unfold Rval; norm_num)
    have hlog : Real.log (Rval n) ≤ 0 := Real.log_nonpos hpos.le hR
    linarith [Rval_eq n, hlog]
  · have hlin := gVal_le_linear n
    have hb := eleven_omega_lam_nonpos
    have hmono : (n : ℝ) * omegaVal ≤ 11 * omegaVal := by
      have : (11 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith [omegaVal_neg, this]
    linarith [hlin, hb, hmono]

/-! ## The five relevant near-star amplitudes are bounded strictly below `0` (rigorous log enclosures). -/

/-- `L >= 1/20` (a weak lower bound: `log(621/64) >= log 2 > 0.693`). -/
theorem Lval_ge_inv20 : (1 : ℝ) / 20 ≤ Lval := by
  have h2 : Real.log 2 ≤ Real.log (621 / 64) := Real.log_le_log (by norm_num) (by norm_num)
  have h2lo := Real.log_two_gt_d9
  unfold Lval; linarith

theorem gVal0_le : gVal 0 ≤ -1 / 20 := by
  have e : gVal 0 = -Lval := by unfold gVal; norm_num
  rw [e]; linarith [Lval_ge_inv20]

/-- Boilerplate for `g(k) <= q` (k = 1..4): express `g(k)` in `{log2, log3, T24, R_k}`, box `T24` below and the
    ratio-log `R_k` above by Taylor, and let `nlinarith` combine with the sharp `log2, log3` bounds. -/
theorem gVal1_le : gVal 1 ≤ -1 / 50 := by
  have hlog32 := log_three_half_id
  have hL621 := log_621_id
  have a1 : Real.log (4 * ((1 : ℕ) : ℝ) + 3) = Real.log 7 := by norm_num
  have a2 : Real.log (3 * (((1 : ℕ) : ℝ) + 1)) = Real.log 6 := by norm_num
  have hR : Real.log 7 - Real.log 6 = Real.log (1 - (-1 / 6)) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hid : gVal 1 = 1 * (Real.log 3 - Real.log 2)
      - 3 / 11 * (4 * Real.log 3 - 3 * Real.log 2 + Real.log (1 - 1 / 24)) + (Real.log 7 - Real.log 6) := by
    unfold gVal Lval; rw [a1, a2, hlog32, hL621]; push_cast; ring
  have hxT : |(1 / 24 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hT24lo := log_one_sub_ge (1 / 24) 4 hxT _ _ rfl rfl
  have hxR : |(-1 / 6 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  have hRup := log_one_sub_le (-1 / 6) 4 hxR _ _ rfl rfl
  rw [hR] at hid; rw [hid]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)] at hT24lo
  rw [abs_of_neg (by norm_num : (-1 / 6 : ℝ) < 0)] at hRup
  norm_num [Finset.sum_range_succ] at hT24lo hRup
  nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9,
    hT24lo, hRup]

theorem gVal2_le : gVal 2 ≤ -1 / 100 := by
  have hlog32 := log_three_half_id
  have hL621 := log_621_id
  have a1 : Real.log (4 * ((2 : ℕ) : ℝ) + 3) = Real.log 11 := by norm_num
  have a2 : Real.log (3 * (((2 : ℕ) : ℝ) + 1)) = Real.log 9 := by norm_num
  have hR : Real.log 11 - Real.log 9 = Real.log (1 - (-2 / 9)) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hid : gVal 2 = 2 * (Real.log 3 - Real.log 2)
      - 5 / 11 * (4 * Real.log 3 - 3 * Real.log 2 + Real.log (1 - 1 / 24)) + (Real.log 11 - Real.log 9) := by
    unfold gVal Lval; rw [a1, a2, hlog32, hL621]; push_cast; ring
  have hxT : |(1 / 24 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hT24lo := log_one_sub_ge (1 / 24) 4 hxT _ _ rfl rfl
  have hxR : |(-2 / 9 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  have hRup := log_one_sub_le (-2 / 9) 4 hxR _ _ rfl rfl
  rw [hR] at hid; rw [hid]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)] at hT24lo
  rw [abs_of_neg (by norm_num : (-2 / 9 : ℝ) < 0)] at hRup
  norm_num [Finset.sum_range_succ] at hT24lo hRup
  nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9,
    hT24lo, hRup]

theorem gVal3_le : gVal 3 ≤ -1 / 500 := by
  have hlog32 := log_three_half_id
  have hL621 := log_621_id
  have a1 : Real.log (4 * ((3 : ℕ) : ℝ) + 3) = Real.log 15 := by norm_num
  have a2 : Real.log (3 * (((3 : ℕ) : ℝ) + 1)) = Real.log 12 := by norm_num
  have hR : Real.log 15 - Real.log 12 = Real.log (1 - (-1 / 4)) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hid : gVal 3 = 3 * (Real.log 3 - Real.log 2)
      - 7 / 11 * (4 * Real.log 3 - 3 * Real.log 2 + Real.log (1 - 1 / 24)) + (Real.log 15 - Real.log 12) := by
    unfold gVal Lval; rw [a1, a2, hlog32, hL621]; push_cast; ring
  have hxT : |(1 / 24 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hT24lo := log_one_sub_ge (1 / 24) 4 hxT _ _ rfl rfl
  have hxR : |(-1 / 4 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  have hRup := log_one_sub_le (-1 / 4) 6 hxR _ _ rfl rfl
  rw [hR] at hid; rw [hid]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)] at hT24lo
  rw [abs_of_neg (by norm_num : (-1 / 4 : ℝ) < 0)] at hRup
  norm_num [Finset.sum_range_succ] at hT24lo hRup
  nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9,
    hT24lo, hRup]

theorem gVal4_le : gVal 4 ≤ -1 / 2000 := by
  have hlog32 := log_three_half_id
  have hL621 := log_621_id
  have a1 : Real.log (4 * ((4 : ℕ) : ℝ) + 3) = Real.log 19 := by norm_num
  have a2 : Real.log (3 * (((4 : ℕ) : ℝ) + 1)) = Real.log 15 := by norm_num
  have hR : Real.log 19 - Real.log 15 = Real.log (1 - (-4 / 15)) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hid : gVal 4 = 4 * (Real.log 3 - Real.log 2)
      - 9 / 11 * (4 * Real.log 3 - 3 * Real.log 2 + Real.log (1 - 1 / 24)) + (Real.log 19 - Real.log 15) := by
    unfold gVal Lval; rw [a1, a2, hlog32, hL621]; push_cast; ring
  have hxT : |(1 / 24 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hT24lo := log_one_sub_ge (1 / 24) 4 hxT _ _ rfl rfl
  have hxR : |(-4 / 15 : ℝ)| < 1 := by rw [abs_of_neg (by norm_num)]; norm_num
  have hRup := log_one_sub_le (-4 / 15) 8 hxR _ _ rfl rfl
  rw [hR] at hid; rw [hid]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)] at hT24lo
  rw [abs_of_neg (by norm_num : (-4 / 15 : ℝ) < 0)] at hRup
  norm_num [Finset.sum_range_succ] at hT24lo hRup
  nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9,
    hT24lo, hRup]

/-! ## The per-child bracket bound. -/

/-- Generic closure step: from `g <= q` and a rational-at-`B=2007` check `q <= (-3/5 - c)/2007`
    (valid since `-3/5 - c <= 0` and the RHS increases as `B` grows), conclude `g + c/B <= -(3/5)/B`. -/
theorem child_case {g q c B : ℝ} (hg : g ≤ q) (hB : 2007 ≤ B) (hc : -3 / 5 ≤ c)
    (hq : q ≤ (-3 / 5 - c) / 2007) : g + c / B ≤ -(3 / 5) / B := by
  have hBpos : (0 : ℝ) < B := by linarith
  have hnum : -3 / 5 - c ≤ 0 := by linarith
  have hmono : (-3 / 5 - c) / 2007 ≤ (-3 / 5 - c) / B := by
    rw [div_le_div_iff₀ (by norm_num) hBpos]; nlinarith [hnum, hB]
  have hgB : g ≤ (-3 / 5 - c) / B := le_trans hg (le_trans hq hmono)
  have hsplit : (-3 / 5 - c) / B + c / B = -(3 / 5) / B := by
    rw [← add_div]; congr 1; ring
  linarith [hgB, hsplit]

/-- **The per-child bracket bound:** for every near-star level `k` and `B >= 2007`,
    `g(k) + (3*mu(k) - 1)/B <= -(3/5)/B` where `mu(k) = 3/(4k+3)`.  Cases `k <= 4` use the boxed amplitudes
    `gVal0..4_le`; `k >= 5` uses `g(k) <= 0` and `9/(4k+3) <= 2/5`. -/
theorem child_term_le (k : ℕ) (B : ℝ) (hB : 2007 ≤ B) :
    gVal k + (3 * (3 / (4 * (k : ℝ) + 3)) - 1) / B ≤ -(3 / 5) / B := by
  have hBpos : (0 : ℝ) < B := by linarith
  rcases lt_or_ge k 5 with hk | hk
  · interval_cases k
    · exact child_case gVal0_le hB (by norm_num) (by norm_num)
    · exact child_case gVal1_le hB (by norm_num) (by norm_num)
    · exact child_case gVal2_le hB (by norm_num) (by norm_num)
    · exact child_case gVal3_le hB (by norm_num) (by norm_num)
    · exact child_case gVal4_le hB (by norm_num) (by norm_num)
  · have hg := gVal_nonpos k
    have hkr : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkp : (0 : ℝ) < 4 * (k : ℝ) + 3 := by positivity
    have hfrac : (3 * (3 / (4 * (k : ℝ) + 3)) - 1) ≤ -(3 / 5) := by
      have h9 : 3 * (3 / (4 * (k : ℝ) + 3)) = 9 / (4 * (k : ℝ) + 3) := by ring
      have key : 9 / (4 * (k : ℝ) + 3) ≤ 2 / 5 := by
        rw [div_le_iff₀ hkp]; nlinarith [hkr]
      rw [h9]; linarith [key]
    have hdiv : (3 * (3 / (4 * (k : ℝ) + 3)) - 1) / B ≤ -(3 / 5) / B :=
      div_le_div_of_nonneg_right hfrac hBpos.le
    linarith [hg, hdiv]

/-! ## The reduction and the j-tail closure. -/

/-- **The `U(s,j)` reduction:** for an all-near-star node, `log(1+x) <= x` on the coupling plus the j-independent
    head bound give `Q <= s*omega + lambda + sum ell + (3*sum mu - j)/B`. -/
theorem nodeAmp_le_U (s j : ℕ) (ell mu : Fin j → ℝ) (hmu : ∀ i, 0 ≤ mu i) :
    nodeAmp s j ell mu ≤ (s : ℝ) * omegaVal + lambdaVal + (∑ i, ell i)
      + (3 * (∑ i, mu i) - (j : ℝ)) / (4 * ((s : ℝ) + j) + 3) := by
  have hsummu : 0 ≤ ∑ i, mu i := Finset.sum_nonneg (fun i _ => hmu i)
  have hcoup_pos : 0 < (4 * (s : ℝ) + 3 * j + 3 + 3 * ∑ i, mu i) / (4 * ((s : ℝ) + j) + 3) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hcoup_pos
  have hsub : (4 * (s : ℝ) + 3 * j + 3 + 3 * ∑ i, mu i) / (4 * ((s : ℝ) + j) + 3) - 1
      = (3 * (∑ i, mu i) - (j : ℝ)) / (4 * ((s : ℝ) + j) + 3) := by
    field_simp; ring
  rw [hsub] at hlog
  have head := node_head_le s j
  unfold nodeAmp
  linarith [head, hlog]

/-- `-omega + lambda <= 1503/11315` (the constant that meets the exact integer corner). -/
theorem neg_omega_lambda_le : -omegaVal + lambdaVal ≤ 1503 / 11315 := by
  have e : -omegaVal + lambdaVal = Real.log (4 / 3) - Real.log (3 / 2) + Lval := by
    unfold omegaVal lambdaVal; ring
  have hLup : Lval ≤ 2069 / 10000 := by
    have h : Lval = (Real.log (3 / 2) - omegaVal) / 2 := by unfold omegaVal; ring
    rw [h]; linarith [log_three_half_enclosure.2, omega_enclosure.1]
  rw [e]
  have h43 := log_four_third_enclosure
  have h32 := log_three_half_enclosure
  linarith [h43.2, h32.1, hLup]

/-- **The D2 j-tail:** an all-near-star node with `s <= 64` and `j >= 501` satisfies `Q <= omega`.  The per-child
    bracket sum is `<= -3j/(5B)`, and the closure `s*omega + lambda - 3j/(5B) <= omega` holds via
    `neg_omega_lambda_le` and the exact integer corner `3885*501 = 30060*64 + 22545`. -/
theorem node_jtail_le (s j : ℕ) (hj : 501 ≤ j) (hs : s ≤ 64) (sp : Fin j → ℕ) :
    nodeAmp s j (fun i => gVal (sp i)) (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) ≤ omegaVal := by
  set B := 4 * ((s : ℝ) + j) + 3 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hjr : (501 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hsr : (s : ℝ) ≤ 64 := by exact_mod_cast hs
  have hB2007 : 2007 ≤ B := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    rw [hBdef]; linarith
  -- reduction
  have hmu : ∀ i, 0 ≤ (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) i := fun i => by positivity
  have hred := nodeAmp_le_U s j (fun i => gVal (sp i)) (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) hmu
  rw [← hBdef] at hred
  -- child-sum: ∑ ell + (3 ∑ mu - j)/B = ∑ (ell_i + (3 mu_i - 1)/B)
  have hsum_eq : (∑ i, gVal (sp i)) + (3 * (∑ i, 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - (j : ℝ)) / B
      = ∑ i, (gVal (sp i) + (3 * (3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - 1) / B) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum]
    ring
  have hchild : ∀ i, gVal (sp i) + (3 * (3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - 1) / B ≤ -(3 / 5) / B :=
    fun i => child_term_le (sp i) B hB2007
  have hsumle : (∑ i, (gVal (sp i) + (3 * (3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - 1) / B))
      ≤ ∑ _i : Fin j, (-(3 / 5) / B) := Finset.sum_le_sum (fun i _ => hchild i)
  have hconst : (∑ _i : Fin j, (-(3 / 5) / B)) = (j : ℝ) * (-(3 / 5) / B) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- closure: s*omega + lambda - 3j/(5B) <= omega
  have hcorner : (1503 : ℝ) / 11315 ≤ 3 * (j : ℝ) / (5 * B) := by
    rw [hBdef, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith [hjr, hsr]
  have hsω : (s : ℝ) * omegaVal ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) omegaVal_neg.le
  have hfin : (s : ℝ) * omegaVal + lambdaVal + (j : ℝ) * (-(3 / 5) / B) ≤ omegaVal := by
    have hj3 : (j : ℝ) * (-(3 / 5) / B) = -(3 * (j : ℝ) / (5 * B)) := by ring
    rw [hj3]
    linarith [hsω, neg_omega_lambda_le, hcorner]
  calc nodeAmp s j (fun i => gVal (sp i)) (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3))
      ≤ (s : ℝ) * omegaVal + lambdaVal + (∑ i, gVal (sp i))
          + (3 * (∑ i, 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - (j : ℝ)) / B := hred
    _ = (s : ℝ) * omegaVal + lambdaVal
          + ((∑ i, gVal (sp i)) + (3 * (∑ i, 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - (j : ℝ)) / B) := by ring
    _ ≤ (s : ℝ) * omegaVal + lambdaVal + (j : ℝ) * (-(3 / 5) / B) := by
        rw [hsum_eq]; linarith [le_trans hsumle (le_of_eq hconst)]
    _ ≤ omegaVal := hfin

/-! ## Sharper j-tail: tightening the `-omega+lambda` constant lowers the threshold `501 -> 96`.

The `501` threshold above is forced by TWO loose choices: the constant `-omega+lambda <= 1503/11315`
(actual value ~0.0879) and the per-child reference `B >= 2007`.  Using the true `-omega+lambda <= 894/10000`
(from the omega/log enclosures) and a reference `B >= 387`, the same per-child bracket closes the near-star
node for every `j >= 96` (`s <= 64`).  This shrinks the residual finite exact-check core from `j <= 500` to
`j <= 95` -- a ~5x reduction -- with no new mathematical idea, only sharper constants. -/

/-- Reference-generic closure step (the `child_case` engine parameterised by the reference denominator `r`). -/
theorem child_case_ref (r : ℝ) (hr : 0 < r) {g q c B : ℝ} (hg : g ≤ q) (hB : r ≤ B) (hc : -3 / 5 ≤ c)
    (hq : q ≤ (-3 / 5 - c) / r) : g + c / B ≤ -(3 / 5) / B := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hr hB
  have hnum : -3 / 5 - c ≤ 0 := by linarith
  have hmono : (-3 / 5 - c) / r ≤ (-3 / 5 - c) / B := by
    rw [div_le_div_iff₀ hr hBpos]; nlinarith [hnum, hB]
  have hgB : g ≤ (-3 / 5 - c) / B := le_trans hg (le_trans hq hmono)
  have hsplit : (-3 / 5 - c) / B + c / B = -(3 / 5) / B := by
    rw [← add_div]; congr 1; ring
  linarith [hgB, hsplit]

/-- **The per-child bracket bound at the sharper reference `B >= 387`.**  Same boxed amplitudes `gVal0..4_le`
    (they clear at `/387` too) and the `k >= 5` decay branch (reference-free). -/
theorem child_term_le_lo (k : ℕ) (B : ℝ) (hB : 387 ≤ B) :
    gVal k + (3 * (3 / (4 * (k : ℝ) + 3)) - 1) / B ≤ -(3 / 5) / B := by
  have hBpos : (0 : ℝ) < B := by linarith
  rcases lt_or_ge k 5 with hk | hk
  · interval_cases k
    · exact child_case_ref 387 (by norm_num) gVal0_le hB (by norm_num) (by norm_num)
    · exact child_case_ref 387 (by norm_num) gVal1_le hB (by norm_num) (by norm_num)
    · exact child_case_ref 387 (by norm_num) gVal2_le hB (by norm_num) (by norm_num)
    · exact child_case_ref 387 (by norm_num) gVal3_le hB (by norm_num) (by norm_num)
    · exact child_case_ref 387 (by norm_num) gVal4_le hB (by norm_num) (by norm_num)
  · have hg := gVal_nonpos k
    have hkr : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkp : (0 : ℝ) < 4 * (k : ℝ) + 3 := by positivity
    have hfrac : (3 * (3 / (4 * (k : ℝ) + 3)) - 1) ≤ -(3 / 5) := by
      have h9 : 3 * (3 / (4 * (k : ℝ) + 3)) = 9 / (4 * (k : ℝ) + 3) := by ring
      have key : 9 / (4 * (k : ℝ) + 3) ≤ 2 / 5 := by
        rw [div_le_iff₀ hkp]; nlinarith [hkr]
      rw [h9]; linarith [key]
    have hdiv : (3 * (3 / (4 * (k : ℝ) + 3)) - 1) / B ≤ -(3 / 5) / B :=
      div_le_div_of_nonneg_right hfrac hBpos.le
    linarith [hg, hdiv]

/-- **The sharp constant `-omega + lambda <= 894/10000`** (actual ~0.0879), from
    `-omega + lambda = -omega/2 + log(4/3) - log(3/2)/2` and the enclosures of `omega`, `log(4/3)`, `log(3/2)`.
    Strictly tighter than `neg_omega_lambda_le` (`1503/11315 ~ 0.1329`). -/
theorem neg_omega_lambda_le' : -omegaVal + lambdaVal ≤ 894 / 10000 := by
  have e : -omegaVal + lambdaVal = -omegaVal / 2 + Real.log (4 / 3) - Real.log (3 / 2) / 2 := by
    unfold omegaVal lambdaVal; ring
  rw [e]
  linarith [log_four_third_enclosure.2, log_three_half_enclosure.1, omega_enclosure.1]

/-- **The sharpened D2 j-tail:** an all-near-star node with `s <= 64` and `j >= 96` satisfies `Q <= omega`.
    Identical to `node_jtail_le` but with the tighter constant (`neg_omega_lambda_le'`) and reference
    (`child_term_le_lo`, `B >= 387`), lowering the threshold `501 -> 96`. -/
theorem node_jtail_le' (s j : ℕ) (hj : 96 ≤ j) (hs : s ≤ 64) (sp : Fin j → ℕ) :
    nodeAmp s j (fun i => gVal (sp i)) (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) ≤ omegaVal := by
  set B := 4 * ((s : ℝ) + j) + 3 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hjr : (96 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hsr : (s : ℝ) ≤ 64 := by exact_mod_cast hs
  have hB387 : 387 ≤ B := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    rw [hBdef]; linarith
  have hmu : ∀ i, 0 ≤ (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) i := fun i => by positivity
  have hred := nodeAmp_le_U s j (fun i => gVal (sp i)) (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) hmu
  rw [← hBdef] at hred
  have hsum_eq : (∑ i, gVal (sp i)) + (3 * (∑ i, 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - (j : ℝ)) / B
      = ∑ i, (gVal (sp i) + (3 * (3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - 1) / B) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum]
    ring
  have hchild : ∀ i, gVal (sp i) + (3 * (3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - 1) / B ≤ -(3 / 5) / B :=
    fun i => child_term_le_lo (sp i) B hB387
  have hsumle : (∑ i, (gVal (sp i) + (3 * (3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - 1) / B))
      ≤ ∑ _i : Fin j, (-(3 / 5) / B) := Finset.sum_le_sum (fun i _ => hchild i)
  have hconst : (∑ _i : Fin j, (-(3 / 5) / B)) = (j : ℝ) * (-(3 / 5) / B) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcorner : (894 : ℝ) / 10000 ≤ 3 * (j : ℝ) / (5 * B) := by
    rw [hBdef, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith [hjr, hsr]
  have hsω : (s : ℝ) * omegaVal ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) omegaVal_neg.le
  have hfin : (s : ℝ) * omegaVal + lambdaVal + (j : ℝ) * (-(3 / 5) / B) ≤ omegaVal := by
    have hj3 : (j : ℝ) * (-(3 / 5) / B) = -(3 * (j : ℝ) / (5 * B)) := by ring
    rw [hj3]
    linarith [hsω, neg_omega_lambda_le', hcorner]
  calc nodeAmp s j (fun i => gVal (sp i)) (fun i => 3 / (4 * ((sp i : ℕ) : ℝ) + 3))
      ≤ (s : ℝ) * omegaVal + lambdaVal + (∑ i, gVal (sp i))
          + (3 * (∑ i, 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - (j : ℝ)) / B := hred
    _ = (s : ℝ) * omegaVal + lambdaVal
          + ((∑ i, gVal (sp i)) + (3 * (∑ i, 3 / (4 * ((sp i : ℕ) : ℝ) + 3)) - (j : ℝ)) / B) := by ring
    _ ≤ (s : ℝ) * omegaVal + lambdaVal + (j : ℝ) * (-(3 / 5) / B) := by
        rw [hsum_eq]; linarith [le_trans hsumle (le_of_eq hconst)]
    _ ≤ omegaVal := hfin

end R3Cert
