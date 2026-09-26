/-
  BG spider reduction, part B1: the three finite-degree cell cores, PROVED (2026-09-24).

  `BGSpiderReduction.lean` reduced spider domination in the high-degree case (root degree `>= 24`,
  `n >= 91`) to three explicit per-vertex cores.  This file proves all three, so the high-degree case is
  unconditional (`spider_dominates_highDegree_uncond`).

  * `SurchargeCore (23/624)` (degree 4..7, arbitrary children): tangent of `log(1 + S/d)` at the
    all-cherry point `S0 = K/3`, the convex correction `1/(d+S) <= 1/(d+S0) + (S0-S)^+/(d(d+S0))`, a
    per-child bound by `ρwit` class (`surcharge_child_le`), and the atom bound `atom_bV_le` for the
    resulting arm `arm_K` (`K = d-1 in 3..6`).  Uniform in `K`, no per-cell numerics.
  * `AtomCell0Core (1/75)` and `AtomCellMuCore (23/624) (1/75)` (a non-atom vertex with `K <= 22` atom
    children): per `K`, one tangent of `log(1 + S/d)` at the extremal configuration (`K-1` cherries plus
    one arm), per-atom linear bounds (`atom_v_le_Vmax`, `atom_v_le_Vnc`) with rational upper bounds on
    `bell(arm_j)`, `j <= 4`, and on the cherry/leaf, and one rational log enclosure per `K`.  All log
    enclosures are degree-6 Taylor bounds (`Real.exp_bound`); certificates generated and exactly
    re-checked by `proof/verification/bg_spider_reduction.py` (`gen-cells`).  Tightest margin: `K = 6`
    (five cherries + one arm of four), `7.3e-4`.

  No `sorry`, no `native_decide`; standard axioms only.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSpiderReduction

namespace R3Cert
namespace BGSCL

open Real

/-! ### Taylor log enclosures. -/

theorem taylor6_sum (c : ℝ) :
    ∑ i ∈ Finset.range 6, c ^ i / (i.factorial : ℝ) = 1 + c + c^2/2 + c^3/6 + c^4/24 + c^5/120 := by
  simp [Finset.sum_range_succ, Nat.factorial]

theorem exp_taylor6 {c a : ℝ} (hca : |c| ≤ a) (ha : a ≤ 1) :
    |Real.exp c - (1 + c + c^2/2 + c^3/6 + c^4/24 + c^5/120)| ≤ a ^ 6 * (7 / 4320) := by
  have hc : |c| ≤ 1 := le_trans hca ha
  have hb := Real.exp_bound hc (n := 6) (by norm_num)
  rw [taylor6_sum] at hb
  have hf : ((Nat.succ 6 : ℕ) : ℝ) / (((Nat.factorial 6 : ℕ) : ℝ) * ((6 : ℕ) : ℝ)) = 7 / 4320 := by
    norm_num [Nat.factorial]
  rw [hf] at hb
  have hpow : |c| ^ 6 ≤ a ^ 6 := pow_le_pow_left₀ (abs_nonneg c) hca 6
  nlinarith

/-- `log x ≤ c` from a Taylor lower bound on `exp c`. -/
theorem log_le_of_taylor {x c a : ℝ} (hx : 0 < x) (hca : |c| ≤ a) (ha : a ≤ 1)
    (h : x ≤ 1 + c + c^2/2 + c^3/6 + c^4/24 + c^5/120 - a ^ 6 * (7 / 4320)) : Real.log x ≤ c := by
  have hb := (abs_le.mp (exp_taylor6 hca ha)).1
  rw [Real.log_le_iff_le_exp hx]
  linarith

/-- `c ≤ log x` from a Taylor upper bound on `exp c`. -/
theorem le_log_of_taylor {x c a : ℝ} (hx : 0 < x) (hca : |c| ≤ a) (ha : a ≤ 1)
    (h : 1 + c + c^2/2 + c^3/6 + c^4/24 + c^5/120 + a ^ 6 * (7 / 4320) ≤ x) : c ≤ Real.log x := by
  have hb := (abs_le.mp (exp_taylor6 hca ha)).2
  rw [Real.le_log_iff_exp_le hx]
  linarith

/-- `log q − F* = log(q^11 · 64/621)/11`. -/
theorem log_sub_fstar_eq {q : ℝ} (hq : 0 < q) :
    Real.log q - FSTAR = Real.log (q ^ 11 * (64 / 621)) / 11 := by
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
    show (64:ℝ) / 621 = (621 / 64)⁻¹ by norm_num, Real.log_inv, FSTAR]
  push_cast; ring

/-! ### Tight rational bounds on the atom values. -/

/-- The cherry anchor `A = 2F* − log(3/2) = log(529/486)/11 ≥ 847797/110000000` (`≈ 0.00770725`). -/
theorem anchor_ge_tight : (847797 / 110000000 : ℝ) ≤ 2 * FSTAR - Real.log (3 / 2) := by
  have hkey : (2:ℝ) * FSTAR - Real.log (3/2) = (1/11) * Real.log (529/486) := by
    rw [FSTAR, show (529/486:ℝ) = (621/64)^(2:ℕ) * (2/3)^(11:ℕ) by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (2/3:ℝ) = (3/2)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hkey]
  have := le_log_of_taylor (x := 529/486) (c := 847797/10000000) (a := 847797/10000000)
    (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  linarith

theorem log32_ge : (2027323 / 5000000 : ℝ) ≤ Real.log (3 / 2) :=
  le_log_of_taylor (x := 3 / 2) (c := 2027323 / 5000000) (a := 2027323 / 5000000) (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)

/-- `F* = (A + log(3/2))/2 ≥ 0.2065859`. -/
theorem fstar_ge_tight : (847797 / 110000000 + 2027323 / 5000000) / 2 ≤ FSTAR := by
  have h1 := anchor_ge_tight
  have h2 := log32_ge
  linarith

theorem bell_arm1_le : bell (armB 1) ≤ -1322143 / 22000000 := by
  have h := eleven_bell_armB 1
  have hl := log_le_of_taylor (c := -1322143 / 2000000) (a := 1322143 / 2000000)
    (x := ((3 / 2 : ℝ) ^ 1 * ((4 * ((1:ℕ) : ℝ) + 3) / (3 * ((1:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 1 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm2_le : bell (armB 2) ≤ -586573 / 27500000 := by
  have h := eleven_bell_armB 2
  have hl := log_le_of_taylor (c := -586573 / 2500000) (a := 586573 / 2500000)
    (x := ((3 / 2 : ℝ) ^ 2 * ((4 * ((2:ℕ) : ℝ) + 3) / (3 * ((2:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 2 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm3_le : bell (armB 3) ≤ -361041 / 55000000 := by
  have h := eleven_bell_armB 3
  have hl := log_le_of_taylor (c := -361041 / 5000000) (a := 361041 / 5000000)
    (x := ((3 / 2 : ℝ) ^ 3 * ((4 * ((3:ℕ) : ℝ) + 3) / (3 * ((3:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 3 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm4_le : bell (armB 4) ≤ -22581 / 22000000 := by
  have h := eleven_bell_armB 4
  have hl := log_le_of_taylor (c := -22581 / 2000000) (a := 22581 / 2000000)
    (x := ((3 / 2 : ℝ) ^ 4 * ((4 * ((4:ℕ) : ℝ) + 3) / (3 * ((4:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 4 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  linarith

/-! ### Per-atom linear envelopes. -/

/-- Upper envelope of `bell a + σ y_a` over non-cherry atoms other than the leaf. -/
noncomputable def Vnc1 (σ : ℝ) : ℝ :=
  max (max (-1322143 / 22000000 + σ * (3 / 7)) (-586573 / 27500000 + σ * (3 / 11)))
    (max (max (-361041 / 55000000 + σ * (1 / 5)) (-22581 / 22000000 + σ * (3 / 19))) (σ * (3 / 23)))

/-- Upper envelope over all non-cherry atoms. -/
noncomputable def Vnc (σ : ℝ) : ℝ :=
  max (Vnc1 σ) (-((847797 / 110000000 + 2027323 / 5000000) / 2) + σ)

/-- Upper envelope over all atoms. -/
noncomputable def Vmax (σ : ℝ) : ℝ := max (-(847797 / 110000000) + σ * (1 / 3)) (Vnc σ)

theorem atom_v_le_Vnc1 {σ : ℝ} (hσ : 0 ≤ σ) {a : Branch} (ha : IsAtom a) (hC : a ≠ cherry)
    (hL : a ≠ Branch.node []) : bell a + σ * bY a ≤ Vnc1 σ := by
  rcases ha with rfl | ⟨j, rfl⟩
  · exact absurd rfl hC
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j) with h | h | h | h | h | h
    · subst h; exact absurd rfl hL
    · subst h
      have hb := bell_arm1_le; rw [bY_armB]; norm_num
      unfold Vnc1
      refine le_max_of_le_left (le_max_of_le_left ?_); linarith
    · subst h
      have hb := bell_arm2_le; rw [bY_armB]; norm_num
      unfold Vnc1
      refine le_max_of_le_left (le_max_of_le_right ?_); linarith
    · subst h
      have hb := bell_arm3_le; rw [bY_armB]; norm_num
      unfold Vnc1
      refine le_max_of_le_right (le_max_of_le_left (le_max_of_le_left ?_)); linarith
    · subst h
      have hb := bell_arm4_le; rw [bY_armB]; norm_num
      unfold Vnc1
      refine le_max_of_le_right (le_max_of_le_left (le_max_of_le_right ?_)); linarith
    · have hb := bg_ceiling (armB j)
      have hy := bY_armB_le j h
      unfold Vnc1
      refine le_max_of_le_right (le_max_of_le_right ?_); nlinarith

theorem atom_v_le_Vnc {σ : ℝ} (hσ : 0 ≤ σ) {a : Branch} (ha : IsAtom a) (hC : a ≠ cherry) :
    bell a + σ * bY a ≤ Vnc σ := by
  by_cases hL : a = Branch.node []
  · subst hL
    rw [bell_leaf, bY_leaf]
    have := fstar_ge_tight
    unfold Vnc
    refine le_max_of_le_right ?_; linarith
  · exact le_max_of_le_left (atom_v_le_Vnc1 hσ ha hC hL)

theorem atom_v_le_Vmax {σ : ℝ} (hσ : 0 ≤ σ) {a : Branch} (ha : IsAtom a) :
    bell a + σ * bY a ≤ Vmax σ := by
  by_cases hC : a = cherry
  · subst hC
    rw [bell_cherry, bY_cherry]
    have := anchor_ge_tight
    unfold Vmax
    refine le_max_of_le_left ?_; linarith
  · exact le_max_of_le_right (atom_v_le_Vnc hσ ha hC)

/-! ### The generic per-`K` cell. -/

/-- Tangent of `log(1 + S/d)` at a reference `S0`:
    `bell(node cs) ≤ Σ_c (bell c + σ y_c) + (log(1 + S0/d) − F*) − σ S0`, `σ = 1/(d + S0)`. -/
theorem bell_node_le_tangent_at (cs : List Branch) {S0 : ℝ} (hS0 : 0 ≤ S0) :
    bell (Branch.node cs)
      ≤ (cs.map (fun c => bell c + 1 / ((cs.length : ℝ) + 1 + S0) * bY c)).sum
        + (Real.log (1 + S0 / ((cs.length : ℝ) + 1)) - FSTAR) - S0 / ((cs.length : ℝ) + 1 + S0) := by
  have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
  have htan := log_tangent hd (sumY_nonneg cs) hS0
  have hsum : (cs.map (fun c => bell c + 1 / ((cs.length : ℝ) + 1 + S0) * bY c)).sum
      = (cs.map bell).sum + 1 / ((cs.length : ℝ) + 1 + S0) * (cs.map bY).sum := by
    exact sum_map_bV (1 / ((cs.length : ℝ) + 1 + S0)) cs
  rw [bell_node, hsum]
  have hsplit : ((cs.map bY).sum - S0) / ((cs.length : ℝ) + 1 + S0)
      = 1 / ((cs.length : ℝ) + 1 + S0) * (cs.map bY).sum - S0 / ((cs.length : ℝ) + 1 + S0) := by
    field_simp
  linarith

/-- A list sum whose terms are all `≤ g` is `≤ |l|·g`. -/
theorem sum_le_length_mul {f : Branch → ℝ} {g : ℝ} :
    ∀ (l : List Branch), (∀ c ∈ l, f c ≤ g) → (l.map f).sum ≤ (l.length : ℝ) * g
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      have ht := sum_le_length_mul t (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
      linarith

/-- **Generic cell** (`K ≥ 2` atom children, at least one not a cherry). -/
theorem cell_generic {K : ℕ} {S0 ℓ umax unc β : ℝ} (hS0 : 0 ≤ S0)
    (hℓ : Real.log (1 + S0 / ((K : ℝ) + 1)) - FSTAR ≤ ℓ)
    (hmax : Vmax (1 / ((K : ℝ) + 1 + S0)) ≤ umax) (hnc : Vnc (1 / ((K : ℝ) + 1 + S0)) ≤ unc)
    (hfin : ((K : ℝ) - 1) * umax + unc + ℓ - S0 / ((K : ℝ) + 1 + S0) ≤ -β)
    (cs : List Branch) (hlen : cs.length = K) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -β := by
  have ht := bell_node_le_tangent_at cs hS0
  rw [hlen] at ht
  have hσ : (0:ℝ) ≤ 1 / ((K : ℝ) + 1 + S0) := by positivity
  have hsum := sum_le_of_one_gap (f := fun c => bell c + 1 / ((K : ℝ) + 1 + S0) * bY c)
    (g := umax) (δ := umax - unc) cs
    (fun c hc => le_trans (atom_v_le_Vmax hσ (hat c hc)) hmax)
    (by obtain ⟨c, hc, hne⟩ := hC
        exact ⟨c, hc, by have := le_trans (atom_v_le_Vnc hσ (hat c hc) hne) hnc; linarith⟩)
  rw [hlen] at hsum
  linarith

/-- **The `K = 1` cell**: a single atom child that is neither a leaf nor a cherry. -/
theorem cell_one {S0 ℓ unc β : ℝ} (hS0 : 0 ≤ S0)
    (hℓ : Real.log (1 + S0 / ((1 : ℝ) + 1)) - FSTAR ≤ ℓ)
    (hnc : Vnc1 (1 / ((1 : ℝ) + 1 + S0)) ≤ unc)
    (hfin : unc + ℓ - S0 / ((1 : ℝ) + 1 + S0) ≤ -β)
    (a : Branch) (ha : IsAtom a) (hC : a ≠ cherry) (hL : a ≠ Branch.node []) :
    bell (Branch.node [a]) ≤ -β := by
  have ht := bell_node_le_tangent_at [a] hS0
  simp only [List.length_cons, List.length_nil, zero_add, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ht
  have hσ : (0:ℝ) ≤ 1 / ((1 : ℝ) + 1 + S0) := by positivity
  have hv := le_trans (atom_v_le_Vnc1 hσ ha hC hL) hnc
  norm_num at ht hv hℓ hfin ⊢
  linarith

/-! ### The per-`K` certificates (generated; `bg_spider_reduction.py gen-cells`). -/

theorem cell_K1 (a : Branch) (ha : IsAtom a) (hC : a ≠ cherry) (hL : a ≠ Branch.node []) :
    bell (Branch.node [a]) ≤ -(157/2400 : ℝ) := by
  refine cell_one (S0 := (3/7 : ℝ)) (ℓ := (-1367317/110000000 : ℝ)) (unc := (43523569/374000000 : ℝ)) (by norm_num) ?_ ?_ ?_ a ha hC hL
  · have e : (1 + (3/7 : ℝ) / ((1:ℝ) + 1)) = (17/14 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (17/14 : ℝ) ^ 11 * (64 / 621)) (c := (-1367317/10000000 : ℝ)) (a := (1367317/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((1:ℝ) + 1 + (3/7 : ℝ))) = (7/17 : ℝ) := by norm_num
    rw [es]; unfold Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K2 (cs : List Branch) (hlen : cs.length = 2) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(19/800 : ℝ) := by
  refine cell_generic (K := 2) (S0 := (16/21 : ℝ)) (ℓ := (2169967/110000000 : ℝ)) (umax := (703024037/8690000000 : ℝ)) (unc := (1029536663/17380000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (16/21 : ℝ) / ((((2:ℕ):ℝ)) + 1)) = (79/63 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (79/63 : ℝ) ^ 11 * (64 / 621)) (c := (2169967/10000000 : ℝ)) (a := (2169967/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((2:ℕ):ℝ)) + 1 + (16/21 : ℝ))) = (21/79 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((2:ℕ):ℝ)) + 1 + (16/21 : ℝ))) = (21/79 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K3 (cs : List Branch) (hlen : cs.length = 3) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(369/20800 : ℝ) := by
  refine cell_generic (K := 3) (S0 := (31/33 : ℝ)) (ℓ := (59979/13750000 : ℝ)) (umax := (1071809089/17930000000 : ℝ)) (unc := (304150317/8965000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (31/33 : ℝ) / ((((3:ℕ):ℝ)) + 1)) = (163/132 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (163/132 : ℝ) ^ 11 * (64 / 621)) (c := (59979/1250000 : ℝ)) (a := (59979/1250000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((3:ℕ):ℝ)) + 1 + (31/33 : ℝ))) = (33/163 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((3:ℕ):ℝ)) + 1 + (31/33 : ℝ))) = (33/163 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K4 (cs : List Branch) (hlen : cs.length = 4) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(31/1950 : ℝ) := by
  refine cell_generic (K := 4) (S0 := (6/5 : ℝ)) (ℓ := (937773/110000000 : ℝ)) (umax := (471154879/10230000000 : ℝ)) (unc := (43807729/1705000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (6/5 : ℝ) / ((((4:ℕ):ℝ)) + 1)) = (31/25 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (31/25 : ℝ) ^ 11 * (64 / 621)) (c := (937773/10000000 : ℝ)) (a := (937773/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((4:ℕ):ℝ)) + 1 + (6/5 : ℝ))) = (5/31 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((4:ℕ):ℝ)) + 1 + (6/5 : ℝ))) = (5/31 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K5 (cs : List Branch) (hlen : cs.length = 5) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1373/93600 : ℝ) := by
  refine cell_generic (K := 5) (S0 := (23/15 : ℝ)) (ℓ := (1154561/55000000 : ℝ)) (umax := (454198939/12430000000 : ℝ)) (unc := (124202367/6215000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (23/15 : ℝ) / ((((5:ℕ):ℝ)) + 1)) = (113/90 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (113/90 : ℝ) ^ 11 * (64 / 621)) (c := (1154561/5000000 : ℝ)) (a := (1154561/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((5:ℕ):ℝ)) + 1 + (23/15 : ℝ))) = (15/113 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((5:ℕ):ℝ)) + 1 + (23/15 : ℝ))) = (15/113 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K6 (cs : List Branch) (hlen : cs.length = 6) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(251/18200 : ℝ) := by
  refine cell_generic (K := 6) (S0 := (104/57 : ℝ)) (ℓ := (550939/22000000 : ℝ)) (umax := (1663558109/55330000000 : ℝ)) (unc := (186641757/11066000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (104/57 : ℝ) / ((((6:ℕ):ℝ)) + 1)) = (503/399 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (503/399 : ℝ) ^ 11 * (64 / 621)) (c := (550939/2000000 : ℝ)) (a := (550939/2000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((6:ℕ):ℝ)) + 1 + (104/57 : ℝ))) = (57/503 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((6:ℕ):ℝ)) + 1 + (104/57 : ℝ))) = (57/503 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K7 (cs : List Branch) (hlen : cs.length = 7) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 7) (S0 := (41/19 : ℝ)) (ℓ := (1772321/55000000 : ℝ)) (umax := (1599125537/63690000000 : ℝ)) (unc := (61641867/4246000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (41/19 : ℝ) / ((((7:ℕ):ℝ)) + 1)) = (193/152 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (193/152 : ℝ) ^ 11 * (64 / 621)) (c := (1772321/5000000 : ℝ)) (a := (1772321/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((7:ℕ):ℝ)) + 1 + (41/19 : ℝ))) = (19/193 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((7:ℕ):ℝ)) + 1 + (41/19 : ℝ))) = (19/193 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K8 (cs : List Branch) (hlen : cs.length = 8) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 8) (S0 := (142/57 : ℝ)) (ℓ := (4155183/110000000 : ℝ)) (umax := (306938593/14410000000 : ℝ)) (unc := (36641889/2882000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (142/57 : ℝ) / ((((8:ℕ):ℝ)) + 1)) = (655/513 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (655/513 : ℝ) ^ 11 * (64 / 621)) (c := (4155183/10000000 : ℝ)) (a := (4155183/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((8:ℕ):ℝ)) + 1 + (142/57 : ℝ))) = (57/655 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((8:ℕ):ℝ)) + 1 + (142/57 : ℝ))) = (57/655 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K9 (cs : List Branch) (hlen : cs.length = 9) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 9) (S0 := (161/57 : ℝ)) (ℓ := (4641293/110000000 : ℝ)) (umax := (1470260393/80410000000 : ℝ)) (unc := (181493289/16082000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (161/57 : ℝ) / ((((9:ℕ):ℝ)) + 1)) = (731/570 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (731/570 : ℝ) ^ 11 * (64 / 621)) (c := (4641293/10000000 : ℝ)) (a := (4641293/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((9:ℕ):ℝ)) + 1 + (161/57 : ℝ))) = (57/731 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((9:ℕ):ℝ)) + 1 + (161/57 : ℝ))) = (57/731 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K10 (cs : List Branch) (hlen : cs.length = 10) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 10) (S0 := (60/19 : ℝ)) (ℓ := (2518721/55000000 : ℝ)) (umax := (1405827821/88770000000 : ℝ)) (unc := (59925711/5918000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (60/19 : ℝ) / ((((10:ℕ):ℝ)) + 1)) = (269/209 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (269/209 : ℝ) ^ 11 * (64 / 621)) (c := (2518721/5000000 : ℝ)) (a := (2518721/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((10:ℕ):ℝ)) + 1 + (60/19 : ℝ))) = (19/269 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((10:ℕ):ℝ)) + 1 + (60/19 : ℝ))) = (19/269 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K11 (cs : List Branch) (hlen : cs.length = 11) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 11) (S0 := (199/57 : ℝ)) (ℓ := (134159/2750000 : ℝ)) (umax := (1341395249/97130000000 : ℝ)) (unc := (178060977/19426000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (199/57 : ℝ) / ((((11:ℕ):ℝ)) + 1)) = (883/684 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (883/684 : ℝ) ^ 11 * (64 / 621)) (c := (134159/250000 : ℝ)) (a := (134159/250000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((11:ℕ):ℝ)) + 1 + (199/57 : ℝ))) = (57/883 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((11:ℕ):ℝ)) + 1 + (199/57 : ℝ))) = (57/883 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K12 (cs : List Branch) (hlen : cs.length = 12) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 12) (S0 := (218/57 : ℝ)) (ℓ := (5644127/110000000 : ℝ)) (umax := (1276962677/105490000000 : ℝ)) (unc := (176344821/21098000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (218/57 : ℝ) / ((((12:ℕ):ℝ)) + 1)) = (959/741 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (959/741 : ℝ) ^ 11 * (64 / 621)) (c := (5644127/10000000 : ℝ)) (a := (5644127/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((12:ℕ):ℝ)) + 1 + (218/57 : ℝ))) = (57/959 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((12:ℕ):ℝ)) + 1 + (218/57 : ℝ))) = (57/959 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K13 (cs : List Branch) (hlen : cs.length = 13) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 13) (S0 := (79/19 : ℝ)) (ℓ := (2940899/55000000 : ℝ)) (umax := (242506021/22770000000 : ℝ)) (unc := (3880637/506000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (79/19 : ℝ) / ((((13:ℕ):ℝ)) + 1)) = (345/266 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (345/266 : ℝ) ^ 11 * (64 / 621)) (c := (2940899/5000000 : ℝ)) (a := (2940899/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((13:ℕ):ℝ)) + 1 + (79/19 : ℝ))) = (19/345 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((13:ℕ):ℝ)) + 1 + (79/19 : ℝ))) = (19/345 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K14 (cs : List Branch) (hlen : cs.length = 14) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 14) (S0 := (256/57 : ℝ)) (ℓ := (553371/10000000 : ℝ)) (umax := (104372503/11110000000 : ℝ)) (unc := (1429029/202000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (256/57 : ℝ) / ((((14:ℕ):ℝ)) + 1)) = (1111/855 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1111/855 : ℝ) ^ 11 * (64 / 621)) (c := (6087081/10000000 : ℝ)) (a := (6087081/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((14:ℕ):ℝ)) + 1 + (256/57 : ℝ))) = (57/1111 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((14:ℕ):ℝ)) + 1 + (256/57 : ℝ))) = (57/1111 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K15 (cs : List Branch) (hlen : cs.length = 15) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 15) (S0 := (275/57 : ℝ)) (ℓ := (6266883/110000000 : ℝ)) (umax := (1083664961/130570000000 : ℝ)) (unc := (171196353/26114000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (275/57 : ℝ) / ((((15:ℕ):ℝ)) + 1)) = (1187/912 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1187/912 : ℝ) ^ 11 * (64 / 621)) (c := (6266883/10000000 : ℝ)) (a := (6266883/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((15:ℕ):ℝ)) + 1 + (275/57 : ℝ))) = (57/1187 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((15:ℕ):ℝ)) + 1 + (275/57 : ℝ))) = (57/1187 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K16 (cs : List Branch) (hlen : cs.length = 16) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 16) (S0 := (98/19 : ℝ)) (ℓ := (1284971/22000000 : ℝ)) (umax := (1019232389/138930000000 : ℝ)) (unc := (56493399/9262000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (98/19 : ℝ) / ((((16:ℕ):ℝ)) + 1)) = (421/323 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (421/323 : ℝ) ^ 11 * (64 / 621)) (c := (1284971/2000000 : ℝ)) (a := (1284971/2000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((16:ℕ):ℝ)) + 1 + (98/19 : ℝ))) = (19/421 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((16:ℕ):ℝ)) + 1 + (98/19 : ℝ))) = (19/421 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K17 (cs : List Branch) (hlen : cs.length = 17) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 17) (S0 := (313/57 : ℝ)) (ℓ := (1641271/27500000 : ℝ)) (umax := (954799817/147290000000 : ℝ)) (unc := (167764041/29458000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (313/57 : ℝ) / ((((17:ℕ):ℝ)) + 1)) = (1339/1026 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1339/1026 : ℝ) ^ 11 * (64 / 621)) (c := (1641271/2500000 : ℝ)) (a := (1641271/2500000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((17:ℕ):ℝ)) + 1 + (313/57 : ℝ))) = (57/1339 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((17:ℕ):ℝ)) + 1 + (313/57 : ℝ))) = (57/1339 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K18 (cs : List Branch) (hlen : cs.length = 18) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 18) (S0 := (332/57 : ℝ)) (ℓ := (8363/137500 : ℝ)) (umax := (178073449/31130000000 : ℝ)) (unc := (33209577/6226000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (332/57 : ℝ) / ((((18:ℕ):ℝ)) + 1)) = (1415/1083 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1415/1083 : ℝ) ^ 11 * (64 / 621)) (c := (8363/12500 : ℝ)) (a := (8363/12500 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((18:ℕ):ℝ)) + 1 + (332/57 : ℝ))) = (57/1415 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((18:ℕ):ℝ)) + 1 + (332/57 : ℝ))) = (57/1415 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K19 (cs : List Branch) (hlen : cs.length = 19) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 19) (S0 := (117/19 : ℝ)) (ℓ := (3401901/55000000 : ℝ)) (umax := (825934673/164010000000 : ℝ)) (unc := (54777243/10934000000 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (117/19 : ℝ) / ((((19:ℕ):ℝ)) + 1)) = (497/380 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (497/380 : ℝ) ^ 11 * (64 / 621)) (c := (3401901/5000000 : ℝ)) (a := (3401901/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((19:ℕ):ℝ)) + 1 + (117/19 : ℝ))) = (19/497 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((19:ℕ):ℝ)) + 1 + (117/19 : ℝ))) = (19/497 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K20 (cs : List Branch) (hlen : cs.length = 20) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 20) (S0 := (446/69 : ℝ)) (ℓ := (6795707/110000000 : ℝ)) (umax := (9/1895 : ℝ)) (unc := (9/1895 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (446/69 : ℝ) / ((((20:ℕ):ℝ)) + 1)) = (1895/1449 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1895/1449 : ℝ) ^ 11 * (64 / 621)) (c := (6795707/10000000 : ℝ)) (a := (6795707/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((20:ℕ):ℝ)) + 1 + (446/69 : ℝ))) = (69/1895 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((20:ℕ):ℝ)) + 1 + (446/69 : ℝ))) = (69/1895 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K21 (cs : List Branch) (hlen : cs.length = 21) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 21) (S0 := (469/69 : ℝ)) (ℓ := (6893289/110000000 : ℝ)) (umax := (9/1987 : ℝ)) (unc := (9/1987 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (469/69 : ℝ) / ((((21:ℕ):ℝ)) + 1)) = (1987/1518 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1987/1518 : ℝ) ^ 11 * (64 / 621)) (c := (6893289/10000000 : ℝ)) (a := (6893289/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((21:ℕ):ℝ)) + 1 + (469/69 : ℝ))) = (69/1987 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((21:ℕ):ℝ)) + 1 + (469/69 : ℝ))) = (69/1987 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num

theorem cell_K22 (cs : List Branch) (hlen : cs.length = 22) (hat : ∀ c ∈ cs, IsAtom c)
    (hC : ∃ c ∈ cs, c ≠ cherry) : bell (Branch.node cs) ≤ -(1/75 : ℝ) := by
  refine cell_generic (K := 22) (S0 := (164/23 : ℝ)) (ℓ := (698231/11000000 : ℝ)) (umax := (1/231 : ℝ)) (unc := (1/231 : ℝ))
    (by norm_num) ?_ ?_ ?_ ?_ cs hlen hat hC
  · have e : (1 + (164/23 : ℝ) / ((((22:ℕ):ℝ)) + 1)) = (693/529 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (693/529 : ℝ) ^ 11 * (64 / 621)) (c := (698231/1000000 : ℝ)) (a := (698231/1000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith
  · have es : (1 / ((((22:ℕ):ℝ)) + 1 + (164/23 : ℝ))) = (23/693 : ℝ) := by norm_num
    rw [es]; unfold Vmax Vnc Vnc1; simp only [max_le_iff]; norm_num
  · have es : (1 / ((((22:ℕ):ℝ)) + 1 + (164/23 : ℝ))) = (23/693 : ℝ) := by norm_num
    rw [es]; unfold Vnc Vnc1; simp only [max_le_iff]; norm_num
  · norm_num


/-! ### Dispatch and the two atom cores. -/

/-- The per-`K` gap delivered by the certificates. -/
noncomputable def betaK : ℕ → ℝ
  | 1 => (157/2400 : ℝ)
  | 2 => (19/800 : ℝ)
  | 3 => (369/20800 : ℝ)
  | 4 => (31/1950 : ℝ)
  | 5 => (1373/93600 : ℝ)
  | 6 => (251/18200 : ℝ)
  | 7 => (1/75 : ℝ)
  | 8 => (1/75 : ℝ)
  | 9 => (1/75 : ℝ)
  | 10 => (1/75 : ℝ)
  | 11 => (1/75 : ℝ)
  | 12 => (1/75 : ℝ)
  | 13 => (1/75 : ℝ)
  | 14 => (1/75 : ℝ)
  | 15 => (1/75 : ℝ)
  | 16 => (1/75 : ℝ)
  | 17 => (1/75 : ℝ)
  | 18 => (1/75 : ℝ)
  | 19 => (1/75 : ℝ)
  | 20 => (1/75 : ℝ)
  | 21 => (1/75 : ℝ)
  | 22 => (1/75 : ℝ)
  | _ => 0

theorem bell_node_atoms_le (cs : List Branch) (h2 : 2 ≤ cs.length) (h22 : cs.length ≤ 22)
    (hat : ∀ c ∈ cs, IsAtom c) (hC : ∃ c ∈ cs, c ≠ cherry) :
    bell (Branch.node cs) ≤ -betaK cs.length := by
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  rw [hK] at h2 h22 ⊢
  interval_cases K
  · exact cell_K2 cs hK hat hC
  · exact cell_K3 cs hK hat hC
  · exact cell_K4 cs hK hat hC
  · exact cell_K5 cs hK hat hC
  · exact cell_K6 cs hK hat hC
  · exact cell_K7 cs hK hat hC
  · exact cell_K8 cs hK hat hC
  · exact cell_K9 cs hK hat hC
  · exact cell_K10 cs hK hat hC
  · exact cell_K11 cs hK hat hC
  · exact cell_K12 cs hK hat hC
  · exact cell_K13 cs hK hat hC
  · exact cell_K14 cs hK hat hC
  · exact cell_K15 cs hK hat hC
  · exact cell_K16 cs hK hat hC
  · exact cell_K17 cs hK hat hC
  · exact cell_K18 cs hK hat hC
  · exact cell_K19 cs hK hat hC
  · exact cell_K20 cs hK hat hC
  · exact cell_K21 cs hK hat hC
  · exact cell_K22 cs hK hat hC

theorem betaK_ge0 (K : ℕ) (h2 : 2 ≤ K) (h22 : K ≤ 22) :
    1 / 75 + (if K = 2 then 1 / 96 else if K = 3 then 1 / 1536 else 0) ≤ betaK K := by
  interval_cases K <;> norm_num [betaK]

theorem betaK_geMu (K : ℕ) (h3 : 3 ≤ K) (h22 : K ≤ 22) :
    1 / 75 - 23 / 624 * (3 / 23) + 23 / 624 * (1 / ((K : ℝ) + 1)) ≤ betaK K := by
  interval_cases K <;> norm_num [betaK]

/-- `y(node cs) ≤ 1/(|cs| + 1)`. -/
theorem bY_node_le_inv (cs : List Branch) : bY (Branch.node cs) ≤ 1 / ((cs.length : ℝ) + 1) := by
  rw [bY_node]
  have := sumY_nonneg cs
  apply one_div_le_one_div_of_le (by positivity); linarith

/-- A non-atom vertex with `K ≥ 2` atom children has a non-cherry child. -/
theorem exists_ne_cherry_of_nonatom (cs : List Branch) (hna : ¬ IsAtom (Branch.node cs)) :
    ∃ c ∈ cs, c ≠ cherry := by
  by_contra h
  push Not at h
  apply hna
  right
  refine ⟨cs.length, ?_⟩
  unfold armB
  congr 1
  exact List.eq_replicate_iff.mpr ⟨rfl, h⟩

/-- `ρwit` of a vertex with `K ≥ 2` children is at most `1/96`, `1/1536`, `0` for `K = 2, 3, ≥ 4`. -/
theorem ρwit_node_le (cs : List Branch) (h2 : 2 ≤ cs.length) :
    ρwit (Branch.node cs) ≤ (if cs.length = 2 then 1 / 96 else if cs.length = 3 then 1 / 1536 else 0) := by
  have hy := bY_node_le_inv cs
  have hy0 := bY_nonneg (Branch.node cs)
  rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [ρwit, bcc, List.length_cons, List.length_nil] at hy ⊢
    norm_num at hy ⊢; linarith
  · simp only [ρwit, bcc, List.length_cons, List.length_nil] at hy ⊢
    norm_num at hy ⊢; linarith
  · rw [ρwit_node_of_four_le _ (by simp)]
    simp

/-- **`AtomCell0Core (1/75)`, proved.** -/
theorem atomCell0Core_proved : AtomCell0Core (1 / 75) := by
  intro cs h22 hat hna
  rcases cs with _ | ⟨a, _ | ⟨a2, t⟩⟩
  · exact absurd (Or.inr ⟨0, rfl⟩) hna
  · -- one child: neither a leaf (node [leaf] = cherry) nor a cherry (node [cherry] = arm_1)
    have ha := hat a (by simp)
    have hC : a ≠ cherry := by
      rintro rfl; exact hna (Or.inr ⟨1, rfl⟩)
    have hL : a ≠ Branch.node [] := by
      rintro rfl; exact hna (Or.inl rfl)
    have hb := cell_K1 a ha hC hL
    have hy : bY (Branch.node [a]) ≤ 1 / 2 := by
      have := bY_node_le_inv [a]; norm_num at this; linarith
    have hA := cherry_anchor_le
    simp only [ρwit, bcc, List.length_cons, List.length_nil]
    linarith
  · have h2 : 2 ≤ (a :: a2 :: t).length := by simp
    have hb := bell_node_atoms_le _ h2 h22 hat (exists_ne_cherry_of_nonatom _ hna)
    have hge := betaK_ge0 _ h2 h22
    have hρ := ρwit_node_le _ h2
    split_ifs at hge hρ <;> linarith

/-- **`AtomCellMuCore (23/624) (1/75)`, proved.** -/
theorem atomCellMuCore_proved : AtomCellMuCore (23 / 624) (1 / 75) := by
  intro cs h3 h22 hat hna
  have hb := bell_node_atoms_le cs (by omega) h22 hat (exists_ne_cherry_of_nonatom cs hna)
  have hge := betaK_geMu _ h3 h22
  have hy := bY_node_le_inv cs
  rw [bV]
  nlinarith

/-! ### `SurchargeCore (23/624)`, proved. -/

/-- Per-child surcharge bound, by `ρwit` class (`σ ∈ [1/9, 1/5]`, `0 ≤ m ≤ 1/500`). -/
theorem surcharge_child_le {σ m : ℝ} (hσ1 : 1 / 9 ≤ σ) (hσ2 : σ ≤ 1 / 5) (hm0 : 0 ≤ m) (hm1 : m ≤ 1 / 500)
    (c : Branch) :
    σ * bY c - ρwit c + m * max 0 (1 / 3 - bY c) ≤ σ / 3 - (2 * FSTAR - Real.log (3 / 2)) := by
  have hA := cherry_anchor_le_tight
  have hF := fstar_ge_tight
  have hy := bY_node_le_inv
  cases c with
  | node cs =>
    rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
    · rw [bY_leaf]
      simp only [ρwit, bcc, List.length_nil]
      rw [max_eq_left (by norm_num)]
      linarith
    · have hlo := bY_deg2_ge_third c1
      rw [max_eq_left (by linarith)]
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      nlinarith
    · have h1 := hy [c1, c2]; have h0 := bY_nonneg (Branch.node [c1, c2])
      norm_num at h1
      rw [max_eq_right (by linarith)]
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ σ - 1 / 32 - m by linarith) (show (0:ℝ) ≤ 1 / 3 - bY (Branch.node [c1, c2]) by linarith)]
    · have h1 := hy [c1, c2, c3]; have h0 := bY_nonneg (Branch.node [c1, c2, c3])
      norm_num at h1
      rw [max_eq_right (by linarith)]
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ σ - 1 / 384 - m by linarith) (show (0:ℝ) ≤ 1 / 4 - bY (Branch.node [c1, c2, c3]) by linarith)]
    · have h1 := hy (c1 :: c2 :: c3 :: c4 :: t); have h0 := bY_nonneg (Branch.node (c1 :: c2 :: c3 :: c4 :: t))
      have hlen : (5:ℝ) ≤ (((c1 :: c2 :: c3 :: c4 :: t).length : ℕ) : ℝ) + 1 := by
        simp only [List.length_cons]; push_cast; linarith [(Nat.cast_nonneg t.length : (0:ℝ) ≤ _)]
      have h15 : bY (Branch.node (c1 :: c2 :: c3 :: c4 :: t)) ≤ 1 / 5 := by
        refine le_trans h1 ?_; exact one_div_le_one_div_of_le (by norm_num) hlen
      rw [max_eq_right (by linarith), ρwit_node_of_four_le _ (by simp)]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ σ - m by linarith) (show (0:ℝ) ≤ 1 / 5 - bY (Branch.node (c1 :: c2 :: c3 :: c4 :: t)) by linarith)]

theorem sum_surcharge_split (σ m : ℝ) (l : List Branch) :
    (l.map (fun c => σ * bY c - ρwit c + m * max 0 (1 / 3 - bY c))).sum
      = σ * (l.map bY).sum - (l.map ρwit).sum + m * (l.map (fun c => max 0 (1 / 3 - bY c))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_third_sub_le (l : List Branch) :
    (l.length : ℝ) / 3 - (l.map bY).sum ≤ (l.map (fun c => max 0 (1 / 3 - bY c))).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      have := le_max_right 0 (1 / 3 - bY a)
      linarith

theorem sum_max_nonneg (l : List Branch) : 0 ≤ (l.map (fun c => max 0 (1 / 3 - bY c))).sum := by
  apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
  obtain ⟨c, _, rfl⟩ := hx; exact le_max_left _ _

/-- `1/(d+S) ≤ 1/(d+S0) + max 0 (S0 − S)/(d(d+S0))`. -/
theorem inv_le_plus {d S S0 : ℝ} (hd : 0 < d) (hS : 0 ≤ S) (hS0 : 0 ≤ S0) :
    1 / (d + S) ≤ 1 / (d + S0) + max 0 (S0 - S) / (d * (d + S0)) := by
  rcases le_total S0 S with h | h
  · rw [max_eq_left (by linarith)]
    have := one_div_le_one_div_of_le (by positivity) (by linarith : d + S0 ≤ d + S)
    simp only [zero_div, add_zero]; exact this
  · rw [max_eq_right (by linarith)]
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hS (sub_nonneg.mpr h)) (by positivity : (0:ℝ) ≤ d + S0),
      mul_nonneg hS hS0, mul_pos hd hd]

/-- **`SurchargeCore (23/624)`, proved** (uniform in `K = 3..6`). -/
theorem surchargeCore_proved : SurchargeCore (23 / 624) := by
  intro cs h3 h6
  set K := cs.length with hKdef
  have hK3 : (3:ℝ) ≤ (K : ℝ) := by exact_mod_cast h3
  have hK6 : (K : ℝ) ≤ 6 := by exact_mod_cast h6
  set d : ℝ := (K : ℝ) + 1 with hd
  set S0 : ℝ := (K : ℝ) / 3 with hS0
  set S := (cs.map bY).sum with hS
  set P := (cs.map (fun c => max 0 (1 / 3 - bY c))).sum with hP
  have hdpos : (0:ℝ) < d := by rw [hd]; linarith
  have hS0nn : (0:ℝ) ≤ S0 := by rw [hS0]; linarith
  have hSnn : 0 ≤ S := sumY_nonneg cs
  set σ : ℝ := 1 / (d + S0) with hσ
  set m : ℝ := 23 / 624 * (1 / (d * (d + S0))) with hm
  have hσeq : σ = 3 / (4 * (K : ℝ) + 3) := by rw [hσ, hd, hS0]; field_simp; ring
  have hσ1 : 1 / 9 ≤ σ := by
    rw [hσeq, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hσ2 : σ ≤ 1 / 5 := by
    rw [hσeq, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hm1 : m ≤ 1 / 500 := by
    rw [hm, hd, hS0]
    have h1 : (20:ℝ) ≤ ((K : ℝ) + 1) * ((K : ℝ) + 1 + (K : ℝ) / 3) := by nlinarith
    have h2 : 1 / (((K : ℝ) + 1) * ((K : ℝ) + 1 + (K : ℝ) / 3)) ≤ 1 / 20 :=
      one_div_le_one_div_of_le (by norm_num) h1
    nlinarith
  -- (a) tangent of the log at S0
  have htan := log_tangent hdpos hSnn hS0nn
  -- (b) the convex correction for y_b
  have hyb : bY (Branch.node cs) ≤ σ + P / (d * (d + S0)) := by
    rw [bY_node, ← hKdef, ← hd, ← hS]
    have h1 := inv_le_plus hdpos hSnn hS0nn
    have h2 : max 0 (S0 - S) ≤ P := by
      apply max_le (sum_max_nonneg cs)
      have := sum_third_sub_le cs
      rw [← hKdef, ← hS, ← hP] at this
      rw [hS0]; linarith
    have h3 : max 0 (S0 - S) / (d * (d + S0)) ≤ P / (d * (d + S0)) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    rw [hσ]; linarith
  -- (c) per-child bound summed
  have hchild := sum_le_length_mul (f := fun c => σ * bY c - ρwit c + m * max 0 (1 / 3 - bY c))
    (g := σ / 3 - (2 * FSTAR - Real.log (3 / 2))) cs (fun c _ => surcharge_child_le hσ1 hσ2 hm0 hm1 c)
  rw [sum_surcharge_split, ← hKdef, ← hS, ← hP] at hchild
  -- (d) the arm_K atom bound
  have harm := atom_bV_le (μ := 23 / 624) (by norm_num) le_rfl (a := armB K) (Or.inr ⟨K, rfl⟩)
  rw [bV, bell_armB, bY_armB] at harm
  have hlog : Real.log ((4 * (K : ℝ) + 3) / (3 * (K : ℝ) + 3)) = Real.log (1 + S0 / d) := by
    congr 1; rw [hS0, hd]; field_simp; ring
  have hy0 : 3 / (4 * (K : ℝ) + 3) = σ := hσeq.symm
  rw [hlog, hy0] at harm
  have hσS0 : σ * S0 = (K : ℝ) * σ / 3 := by rw [hS0]; ring
  have hmP : 23 / 624 * (P / (d * (d + S0))) = m * P := by rw [hm]; field_simp
  have htan' : Real.log (1 + S / d) ≤ Real.log (1 + S0 / d) + σ * S - σ * S0 := by
    have : (S - S0) / (d + S0) = σ * S - σ * S0 := by rw [hσ]; field_simp
    linarith
  nlinarith [htan', hyb, hchild, harm, hσS0, hmP]

/-! ### The high-degree case, unconditional. -/

/-- **Spider domination in the high-degree case (UNCONDITIONAL).**  Every root list with `k ≥ 24`
    children, at least one of which is not an atom (leaf, cherry, arm), and total size `n − 1 ≥ 90`, is
    STRICTLY beaten by the spider with `q = (5(n−1)) mod 11` arms of four cherries and
    `a = ((n−1) − 9q)/11` arms of five cherries.  Consequently every tree on `n ≥ 91` vertices with a
    vertex of degree `≥ 24` is either a two-level spider centred at that vertex or strictly dominated by
    one. -/
theorem spider_dominates_highDegree_uncond
    (cs : List Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (hN : 90 ≤ bsizeList cs) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) :=
  spider_dominates_highDegree_of_cores atomCell0Core_proved surchargeCore_proved atomCellMuCore_proved
    cs hk hna hN

end BGSCL
end R3Cert
