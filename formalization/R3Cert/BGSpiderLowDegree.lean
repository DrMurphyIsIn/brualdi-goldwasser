/-
  BG spider reduction, part B1: the LOW-degree case (maximum degree `<= 23`), PROVED for `n >= 492`
  (2026-09-24).

  Rooted at a vertex of maximum degree `k <= 23`, every other vertex has `<= k - 1` children.  A
  per-vertex RATE cell (`RateCellCap D α`, degree cap `D`) telescopes to a LINEAR deficit
  `bell b + ρwit b ≤ −α |b|` for every non-atom branch (`bell_add_ρwit_le_rateCap`), so the root bound loses
  `α (n − 1)` and falls below the arm_5/arm_4 spider floor `log(26/23) − 1/96` once `n − 1 ≥ 491`.

  Caps / rates: `D = 23, α = 1/3700` (root degree 6..23); `D = 5, 4, 3, 2` with `α = 1/2100, 1/660,
  1/420, 1/135` (root degree 5, 4, 3, 2).  Every rate cell (32 of them) and root cell (22) is a
  tangent-at-`S0` certificate with rational per-child envelopes and degree-6 Taylor log enclosures,
  generated and exactly re-checked by `proof/verification/bg_spider_reduction.py gen-rate`.

  Main theorem: `spider_dominates_lowDegree_uncond`.  No `sorry`; standard axioms.
  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSpiderCells

namespace R3Cert
namespace BGSCL

open Real

/-! ### The capped rate cell and its telescoping. -/

/-- The per-vertex rate cell under degree cap `D` (a vertex has `≤ D − 1` children, and so do all
    vertices of its children). -/
def RateCellCap (D : ℕ) (α : ℝ) : Prop :=
  ∀ cs : List Branch, cs.length + 1 ≤ D → (∀ c ∈ cs, maxCh c + 1 ≤ D) → ¬ IsAtom (Branch.node cs) →
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + (cs.map (rateG α)).sum ≤ 0

theorem bell_add_ρwit_le_rateCap {D : ℕ} {α : ℝ} (hR : RateCellCap D α) :
    ∀ b, maxCh b + 1 ≤ D → ¬ IsAtom b → bell b + ρwit b ≤ -α * (bsize b : ℝ) := by
  refine scl_of_child_step bsize bchildren
    (fun b => maxCh b + 1 ≤ D → ¬ IsAtom b → bell b + ρwit b ≤ -α * (bsize b : ℝ))
    bchildren_bsize_lt (fun a hIH => ?_)
  cases a with
  | node cs =>
    intro hcap hna
    rw [maxCh_node] at hcap
    have hlen : cs.length + 1 ≤ D := by have := le_max_left cs.length (maxChList cs); omega
    have hcc : ∀ c ∈ cs, maxCh c + 1 ≤ D := fun c hc => by
      have h1 := maxCh_le_of_mem hc
      have h2 := le_max_right cs.length (maxChList cs)
      omega
    have hch : ∀ c ∈ cs, ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ) := fun c hc =>
      hIH c (by simpa only [bchildren] using hc) (hcc c hc)
    have hsum := sum_bell_le_rateG cs hch
    have hcell := hR cs hlen hcc hna
    have hsz : (bsize (Branch.node cs) : ℝ) = 1 + (bsizeList cs : ℝ) := by
      simp only [bsize]; push_cast; ring
    rw [bell_node, hsz]
    linarith

theorem phiRoot_le_rateCap {D : ℕ} {α : ℝ} (hR : RateCellCap D α) (cs : List Branch)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D) :
    phiRoot cs ≤ Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG α)).sum
      - α * (bsizeList cs : ℝ) := by
  rw [phiRoot_eq]
  have := sum_bell_le_rateG cs (fun c hc hna => bell_add_ρwit_le_rateCap hR c (hcap c hc) hna)
  linarith

/-! ### Structural facts: arms, message ranges. -/

theorem maxCh_armB_ge (j : ℕ) : j ≤ maxCh (armB j) := by
  simp only [armB, maxCh_node, List.length_replicate]; exact le_max_left _ _

/-- The message of any branch with at least one child is `≤ 1/2`. -/
theorem bY_le_half_of_ne_leaf {c : Branch} (h : c ≠ Branch.node []) : bY c ≤ 1 / 2 := by
  cases c with
  | node cs =>
    have hy := bY_node_le_inv cs
    have hl : 1 ≤ cs.length := by
      rcases cs with _ | ⟨a, t⟩
      · exact absurd rfl h
      · simp
    have : (2:ℝ) ≤ (cs.length : ℝ) + 1 := by have : (1:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hl
                                             linarith
    exact le_trans hy (one_div_le_one_div_of_le (by norm_num) this)

/-- `log x ≤ c` for `|c| ≤ 2`, from `exp c = exp(c/2)^2`. -/
theorem log_le_of_taylor2 {x c a : ℝ} (hx : 0 < x) (hca : |c / 2| ≤ a) (ha : a ≤ 1)
    (hp : 0 ≤ 1 + c/2 + (c/2)^2/2 + (c/2)^3/6 + (c/2)^4/24 + (c/2)^5/120 - a ^ 6 * (7 / 4320))
    (h : x ≤ (1 + c/2 + (c/2)^2/2 + (c/2)^3/6 + (c/2)^4/24 + (c/2)^5/120 - a ^ 6 * (7 / 4320)) ^ 2) :
    Real.log x ≤ c := by
  have hb := (abs_le.mp (exp_taylor6 hca ha)).1
  have he : Real.exp c = Real.exp (c / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [Real.log_le_iff_le_exp hx, he]
  have h2 : (1 + c/2 + (c/2)^2/2 + (c/2)^3/6 + (c/2)^4/24 + (c/2)^5/120 - a ^ 6 * (7 / 4320))
      ≤ Real.exp (c / 2) := by linarith
  calc x ≤ _ := h
    _ ≤ Real.exp (c / 2) ^ 2 := by gcongr

/-- The per-child envelope of a NON-atom child: `−ρwit c + σ y_c ≤ Nb σ`. -/
noncomputable def Nb (σ : ℝ) : ℝ :=
  max (max (-(847797 / 110000000) - 1 / 60 + σ * (2 / 5)) (-(847797 / 110000000) - 1 / 24 + σ * (1 / 2)))
    (max (max 0 ((σ - 1 / 32) / 3)) (max ((σ - 1 / 384) / 4) (σ / 5)))

theorem nonatom_le_Nb {σ : ℝ} (hσ : 0 ≤ σ) {c : Branch} (hna : ¬ IsAtom c) :
    -ρwit c + σ * bY c ≤ Nb σ := by
  have hA := anchor_ge_tight
  cases c with
  | node cs =>
    rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · -- degree 2, non-atom: c1 is not a leaf, so y ∈ [2/5, 1/2]
      have hc1 : c1 ≠ Branch.node [] := by rintro rfl; exact hna (Or.inl rfl)
      have hy1 := bY_le_half_of_ne_leaf hc1
      have hy0 := bY_nonneg c1
      have hyv : bY (Branch.node [c1]) = 1 / (2 + bY c1) := by
        rw [bY_node]; simp; ring_nf
      have hlo : 2 / 5 ≤ bY (Branch.node [c1]) := by
        rw [hyv, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      have hhi : bY (Branch.node [c1]) ≤ 1 / 2 := by
        rw [hyv, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      unfold Nb
      rcases le_total σ (1 / 4) with hs | hs
      · refine le_max_of_le_left (le_max_of_le_left ?_); nlinarith
      · refine le_max_of_le_left (le_max_of_le_right ?_); nlinarith
    · have h1 := bY_node_le_inv [c1, c2]; have h0 := bY_nonneg (Branch.node [c1, c2])
      norm_num at h1
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      unfold Nb
      refine le_max_of_le_right (le_max_of_le_left ?_)
      rcases le_total σ (1 / 32) with hs | hs
      · refine le_max_of_le_left ?_; nlinarith
      · refine le_max_of_le_right ?_; nlinarith
    · have h1 := bY_node_le_inv [c1, c2, c3]; have h0 := bY_nonneg (Branch.node [c1, c2, c3])
      norm_num at h1
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      unfold Nb
      rcases le_total σ (1 / 384) with hs | hs
      · refine le_max_of_le_right (le_max_of_le_left (le_max_of_le_left ?_)); nlinarith
      · refine le_max_of_le_right (le_max_of_le_right (le_max_of_le_left ?_)); nlinarith
    · have h1 := bY_node_le_inv (c1 :: c2 :: c3 :: c4 :: t)
      have h0 := bY_nonneg (Branch.node (c1 :: c2 :: c3 :: c4 :: t))
      have hlen : (5:ℝ) ≤ (((c1 :: c2 :: c3 :: c4 :: t).length : ℕ) : ℝ) + 1 := by
        simp only [List.length_cons]; push_cast; linarith [(Nat.cast_nonneg t.length : (0:ℝ) ≤ _)]
      have h15 : bY (Branch.node (c1 :: c2 :: c3 :: c4 :: t)) ≤ 1 / 5 :=
        le_trans h1 (one_div_le_one_div_of_le (by norm_num) hlen)
      rw [ρwit_node_of_four_le _ (by simp)]
      unfold Nb
      refine le_max_of_le_right (le_max_of_le_right (le_max_of_le_right ?_)); nlinarith

/-- A root whose Lagrangian value is below the spider floor is strictly beaten by an arm_5/arm_4 spider. -/
theorem spider_of_phiRoot_lt (cs : List Branch) (hN : 90 ≤ bsizeList cs)
    (hlt : phiRoot cs < Real.log (26 / 23) - 1 / 96) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) := by
  set N := bsizeList cs with hNdef
  refine ⟨(N - 9 * ((5 * N) % 11)) / 11, (5 * N) % 11, by omega, ?_, ?_⟩
  · rw [bsizeList_spiderB]; omega
  · have hsz : bsizeList (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) = N := by
      rw [bsizeList_spiderB]; omega
    have haq : 1 ≤ (N - 9 * ((5 * N) % 11)) / 11 + (5 * N) % 11 := by omega
    have hq10 : (((5 * N) % 11 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (by omega : (5 * N) % 11 ≤ 10)
    have hlo := phiRoot_spider_ge _ _ haq
    have h4 := bell_arm4_ge
    have h4' : (-1 / 96 : ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) * bell (armB 4) := by
      have hqnn : (0:ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hlt' : phiRoot cs < phiRoot (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) := by
      linarith
    unfold phiRoot at hlt'
    rw [hsz, ← hNdef] at hlt'
    exact (Real.log_lt_log_iff (piRoot_pos _) (piRoot_pos _)).mp (by linarith)

/-! ### Per-child envelopes. -/

/-- `−ρwit c + σ y_c + 1/(4(2 + y_c))` over non-atom classes (endpoint values; chords of the convex
    `1/(2+y)`). -/
noncomputable def Nb1 (σ : ℝ) : ℝ :=
  max (max (max (-(847797 / 110000000) - 1 / 60 + σ * (2 / 5) + 5 / 48)
                (-(847797 / 110000000) - 1 / 24 + σ * (1 / 2) + 1 / 10))
           (max (1 / 8) (-(1 / 96) + σ * (1 / 3) + 3 / 28)))
      (max (max (1 / 8) (-(1 / 1536) + σ * (1 / 4) + 1 / 9))
           (max (1 / 8) (σ * (1 / 5) + 5 / 44)))

theorem nonatom_le_Nb1 {σ : ℝ} (hσ : 0 ≤ σ) {c : Branch} (hna : ¬ IsAtom c) :
    -ρwit c + σ * bY c + 1 / (4 * (2 + bY c)) ≤ Nb1 σ := by
  have hA := anchor_ge_tight
  have h0c := bY_nonneg c
  cases c with
  | node cs =>
    rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · have hc1 : c1 ≠ Branch.node [] := by rintro rfl; exact hna (Or.inl rfl)
      have hy1 := bY_le_half_of_ne_leaf hc1
      have hy0 := bY_nonneg c1
      have hyv : bY (Branch.node [c1]) = 1 / (2 + bY c1) := by
        rw [bY_node]; simp; ring_nf
      have hlo : 2 / 5 ≤ bY (Branch.node [c1]) := by
        rw [hyv, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      have hhi : bY (Branch.node [c1]) ≤ 1 / 2 := by
        rw [hyv, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      set y := bY (Branch.node [c1])
      have hch : 1 / (4 * (2 + y)) ≤ 5 / 48 - (y - 2 / 5) / 24 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      unfold Nb1
      refine le_max_of_le_left (le_max_of_le_left ?_)
      rcases le_total σ (1 / 4 + 1 / 24) with hs | hs
      · refine le_max_of_le_left ?_; nlinarith
      · refine le_max_of_le_right ?_; nlinarith
    · have h1 := bY_node_le_inv [c1, c2]
      norm_num at h1
      set y := bY (Branch.node [c1, c2])
      have hch : 1 / (4 * (2 + y)) ≤ 1 / 8 - 3 * y / 56 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg h0c (show (0:ℝ) ≤ 1 / 3 - y by linarith)]
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      unfold Nb1
      refine le_max_of_le_left (le_max_of_le_right ?_)
      rcases le_total σ (1 / 32 + 3 / 56) with hs | hs
      · refine le_max_of_le_left ?_; nlinarith
      · refine le_max_of_le_right ?_; nlinarith
    · have h1 := bY_node_le_inv [c1, c2, c3]
      norm_num at h1
      set y := bY (Branch.node [c1, c2, c3])
      have hch : 1 / (4 * (2 + y)) ≤ 1 / 8 - y / 18 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg h0c (show (0:ℝ) ≤ 1 / 4 - y by linarith)]
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      unfold Nb1
      refine le_max_of_le_right (le_max_of_le_left ?_)
      rcases le_total σ (1 / 384 + 1 / 18) with hs | hs
      · refine le_max_of_le_left ?_; nlinarith
      · refine le_max_of_le_right ?_; nlinarith
    · have h1 := bY_node_le_inv (c1 :: c2 :: c3 :: c4 :: t)
      have hlen : (5:ℝ) ≤ (((c1 :: c2 :: c3 :: c4 :: t).length : ℕ) : ℝ) + 1 := by
        simp only [List.length_cons]; push_cast; linarith [(Nat.cast_nonneg t.length : (0:ℝ) ≤ _)]
      have h15 : bY (Branch.node (c1 :: c2 :: c3 :: c4 :: t)) ≤ 1 / 5 :=
        le_trans h1 (one_div_le_one_div_of_le (by norm_num) hlen)
      set y := bY (Branch.node (c1 :: c2 :: c3 :: c4 :: t))
      have hch : 1 / (4 * (2 + y)) ≤ 1 / 8 - 5 * y / 88 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg h0c (show (0:ℝ) ≤ 1 / 5 - y by linarith)]
      rw [ρwit_node_of_four_le _ (by simp)]
      unfold Nb1
      refine le_max_of_le_right (le_max_of_le_right ?_)
      rcases le_total σ (5 / 88) with hs | hs
      · refine le_max_of_le_left ?_; nlinarith
      · refine le_max_of_le_right ?_; nlinarith

/-! ### Arm bell bounds `j ≤ 22` (generated). -/

theorem bell_arm6_leT : bell (armB 6) ≤ (-4167/2750000 : ℝ) := by
  have h := eleven_bell_armB 6
  have hl := log_le_of_taylor2 (c := (-4167/250000 : ℝ)) (a := (4167/500000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 6 * ((4 * ((6:ℕ) : ℝ) + 3) / (3 * ((6:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 6 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm7_leT : bell (armB 7) ≤ (-253197/55000000 : ℝ) := by
  have h := eleven_bell_armB 7
  have hl := log_le_of_taylor2 (c := (-253197/5000000 : ℝ)) (a := (253197/10000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 7 * ((4 * ((7:ℕ) : ℝ) + 3) / (3 * ((7:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 7 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm8_leT : bell (armB 8) ≤ (-120079/13750000 : ℝ) := by
  have h := eleven_bell_armB 8
  have hl := log_le_of_taylor2 (c := (-120079/1250000 : ℝ)) (a := (120079/2500000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 8 * ((4 * ((8:ℕ) : ℝ) + 3) / (3 * ((8:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 8 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm9_leT : bell (armB 9) ≤ (-2123/156250 : ℝ) := by
  have h := eleven_bell_armB 9
  have hl := log_le_of_taylor2 (c := (-23353/156250 : ℝ)) (a := (23353/312500 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 9 * ((4 * ((9:ℕ) : ℝ) + 3) / (3 * ((9:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 9 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm10_leT : bell (armB 10) ≤ (-1043139/55000000 : ℝ) := by
  have h := eleven_bell_armB 10
  have hl := log_le_of_taylor2 (c := (-1043139/5000000 : ℝ)) (a := (1043139/10000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 10 * ((4 * ((10:ℕ) : ℝ) + 3) / (3 * ((10:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 10 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm11_leT : bell (armB 11) ≤ (-170069/6875000 : ℝ) := by
  have h := eleven_bell_armB 11
  have hl := log_le_of_taylor2 (c := (-170069/625000 : ℝ)) (a := (170069/1250000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 11 * ((4 * ((11:ℕ) : ℝ) + 3) / (3 * ((11:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 11 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm12_leT : bell (armB 12) ≤ (-423627/13750000 : ℝ) := by
  have h := eleven_bell_armB 12
  have hl := log_le_of_taylor2 (c := (-423627/1250000 : ℝ)) (a := (423627/2500000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 12 * ((4 * ((12:ℕ) : ℝ) + 3) / (3 * ((12:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 12 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm13_leT : bell (armB 13) ≤ (-4082857/110000000 : ℝ) := by
  have h := eleven_bell_armB 13
  have hl := log_le_of_taylor2 (c := (-4082857/10000000 : ℝ)) (a := (4082857/20000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 13 * ((4 * ((13:ℕ) : ℝ) + 3) / (3 * ((13:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 13 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm14_leT : bell (armB 14) ≤ (-4797391/110000000 : ℝ) := by
  have h := eleven_bell_armB 14
  have hl := log_le_of_taylor2 (c := (-4797391/10000000 : ℝ)) (a := (4797391/20000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 14 * ((4 * ((14:ℕ) : ℝ) + 3) / (3 * ((14:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 14 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm15_leT : bell (armB 15) ≤ (-43193/859375 : ℝ) := by
  have h := eleven_bell_armB 15
  have hl := log_le_of_taylor2 (c := (-43193/78125 : ℝ)) (a := (43193/156250 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 15 * ((4 * ((15:ℕ) : ℝ) + 3) / (3 * ((15:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 15 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm16_leT : bell (armB 16) ≤ (-3136897/55000000 : ℝ) := by
  have h := eleven_bell_armB 16
  have hl := log_le_of_taylor2 (c := (-3136897/5000000 : ℝ)) (a := (3136897/10000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 16 * ((4 * ((16:ℕ) : ℝ) + 3) / (3 * ((16:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 16 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm17_leT : bell (armB 17) ≤ (-7030311/110000000 : ℝ) := by
  have h := eleven_bell_armB 17
  have hl := log_le_of_taylor2 (c := (-7030311/10000000 : ℝ)) (a := (7030311/20000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 17 * ((4 * ((17:ℕ) : ℝ) + 3) / (3 * ((17:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 17 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm18_leT : bell (armB 18) ≤ (-3898177/55000000 : ℝ) := by
  have h := eleven_bell_armB 18
  have hl := log_le_of_taylor2 (c := (-3898177/5000000 : ℝ)) (a := (3898177/10000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 18 * ((4 * ((18:ℕ) : ℝ) + 3) / (3 * ((18:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 18 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm19_leT : bell (armB 19) ≤ (-66958/859375 : ℝ) := by
  have h := eleven_bell_armB 19
  have hl := log_le_of_taylor2 (c := (-66958/78125 : ℝ)) (a := (33479/78125 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 19 * ((4 * ((19:ℕ) : ℝ) + 3) / (3 * ((19:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 19 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm20_leT : bell (armB 20) ≤ (-9351809/110000000 : ℝ) := by
  have h := eleven_bell_armB 20
  have hl := log_le_of_taylor2 (c := (-9351809/10000000 : ℝ)) (a := (9351809/20000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 20 * ((4 * ((20:ℕ) : ℝ) + 3) / (3 * ((20:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 20 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm21_leT : bell (armB 21) ≤ (-10138151/110000000 : ℝ) := by
  have h := eleven_bell_armB 21
  have hl := log_le_of_taylor2 (c := (-10138151/10000000 : ℝ)) (a := (10138151/20000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 21 * ((4 * ((21:ℕ) : ℝ) + 3) / (3 * ((21:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 21 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem bell_arm22_leT : bell (armB 22) ≤ (-5464941/55000000 : ℝ) := by
  have h := eleven_bell_armB 22
  have hl := log_le_of_taylor2 (c := (-5464941/5000000 : ℝ)) (a := (5464941/10000000 : ℝ))
    (x := ((3 / 2 : ℝ) ^ 22 * ((4 * ((22:ℕ) : ℝ) + 3) / (3 * ((22:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 22 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Rational upper bounds on `bell(arm_j)`, `1 ≤ j ≤ 22`. -/
noncomputable def bjT : ℕ → ℝ
  | 1 => (-1322143/22000000 : ℝ)
  | 2 => (-586573/27500000 : ℝ)
  | 3 => (-361041/55000000 : ℝ)
  | 4 => (-22581/22000000 : ℝ)
  | 5 => (0 : ℝ)
  | 6 => (-4167/2750000 : ℝ)
  | 7 => (-253197/55000000 : ℝ)
  | 8 => (-120079/13750000 : ℝ)
  | 9 => (-2123/156250 : ℝ)
  | 10 => (-1043139/55000000 : ℝ)
  | 11 => (-170069/6875000 : ℝ)
  | 12 => (-423627/13750000 : ℝ)
  | 13 => (-4082857/110000000 : ℝ)
  | 14 => (-4797391/110000000 : ℝ)
  | 15 => (-43193/859375 : ℝ)
  | 16 => (-3136897/55000000 : ℝ)
  | 17 => (-7030311/110000000 : ℝ)
  | 18 => (-3898177/55000000 : ℝ)
  | 19 => (-66958/859375 : ℝ)
  | 20 => (-9351809/110000000 : ℝ)
  | 21 => (-10138151/110000000 : ℝ)
  | 22 => (-5464941/55000000 : ℝ)
  | _ => 0

theorem arm_bell_le_T (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 22) : bell (armB j) ≤ bjT j := by
  interval_cases j <;> simp only [bjT]
  · exact bell_arm1_le
  · exact bell_arm2_le
  · exact bell_arm3_le
  · exact bell_arm4_le
  · rw [bell_arm5]
  · exact bell_arm6_leT
  · exact bell_arm7_leT
  · exact bell_arm8_leT
  · exact bell_arm9_leT
  · exact bell_arm10_leT
  · exact bell_arm11_leT
  · exact bell_arm12_leT
  · exact bell_arm13_leT
  · exact bell_arm14_leT
  · exact bell_arm15_leT
  · exact bell_arm16_leT
  · exact bell_arm17_leT
  · exact bell_arm18_leT
  · exact bell_arm19_leT
  · exact bell_arm20_leT
  · exact bell_arm21_leT
  · exact bell_arm22_leT

/-! ### Generic rate / root cells. -/

theorem child_le_env {σ α u : ℝ} {D : ℕ} (hσ : 0 ≤ σ) (hD : D ≤ 23)
    (hL : -((847797 / 110000000 + 2027323 / 5000000) / 2) + α + σ ≤ u)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      bjT j + α * (2 * (j : ℝ) + 1) + σ * (3 / (4 * (j : ℝ) + 3)) ≤ u)
    (hN : Nb σ ≤ u) {c : Branch} (hc : maxCh c + 1 ≤ D) (hC : c ≠ cherry) :
    rateG α c + σ * bY c ≤ u := by
  unfold rateG
  split_ifs with ha
  · rcases ha with rfl | ⟨j, rfl⟩
    · exact absurd rfl hC
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · have hl : armB 0 = Branch.node [] := rfl
        rw [hl, bell_leaf, bY_leaf]
        have hs : bsize (Branch.node []) = 1 := by simp [bsize, bsizeList]
        rw [hs]; have := fstar_ge_tight; push_cast; linarith
      · have hjm := maxCh_armB_ge j
        have hb := arm_bell_le_T j hj (by omega)
        have hA := hArm j hj (by omega)
        rw [bY_armB, bsize_armB]; push_cast; linarith
  · have := nonatom_le_Nb hσ ha; linarith

theorem cherry_le_env {σ α : ℝ} :
    rateG α cherry + σ * bY cherry ≤ -(847797 / 110000000) + 2 * α + σ * (1 / 3) := by
  have hat : IsAtom cherry := Or.inl rfl
  unfold rateG; rw [if_pos hat, bell_cherry, bY_cherry, bsize_cherry]
  have := anchor_ge_tight; push_cast; linarith

theorem child_le_env1 {σ α u : ℝ} {D : ℕ} (hσ : 0 ≤ σ) (hD : D ≤ 23)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      σ * (3 / (4 * (j : ℝ) + 3)) + 1 / (4 * (2 + 3 / (4 * (j : ℝ) + 3))) + bjT j
        + α * (2 * (j : ℝ) + 1) ≤ u)
    (hN : Nb1 σ ≤ u) {c : Branch} (hc : maxCh c + 1 ≤ D) (hC : c ≠ cherry) (hL : c ≠ Branch.node []) :
    σ * bY c + 1 / (4 * (2 + bY c)) + rateG α c ≤ u := by
  unfold rateG
  split_ifs with ha
  · rcases ha with rfl | ⟨j, rfl⟩
    · exact absurd rfl hC
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd rfl hL
      · have hjm := maxCh_armB_ge j
        have hb := arm_bell_le_T j hj (by omega)
        have hA := hArm j hj (by omega)
        rw [bY_armB, bsize_armB]; push_cast; linarith
  · have := nonatom_le_Nb1 hσ ha; linarith

theorem sum_rateG_add (α σ : ℝ) (l : List Branch) :
    (l.map (fun c => rateG α c + σ * bY c)).sum = (l.map (rateG α)).sum + σ * (l.map bY).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Generic rate cell** (`K ≥ 2` children). -/
theorem rate_cell_generic {D K : ℕ} (hD : D ≤ 23) {α S0 ℓ umax unc ρm : ℝ} (hS0 : 0 ≤ S0)
    (hℓ : Real.log (1 + S0 / ((K : ℝ) + 1)) - FSTAR ≤ ℓ)
    (hL : -((847797 / 110000000 + 2027323 / 5000000) / 2) + α + 1 / ((K : ℝ) + 1 + S0) ≤ unc)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      bjT j + α * (2 * (j : ℝ) + 1) + 1 / ((K : ℝ) + 1 + S0) * (3 / (4 * (j : ℝ) + 3)) ≤ unc)
    (hN : Nb (1 / ((K : ℝ) + 1 + S0)) ≤ unc)
    (hCu : -(847797 / 110000000) + 2 * α + 1 / ((K : ℝ) + 1 + S0) * (1 / 3) ≤ umax) (hu : unc ≤ umax)
    (hρ : ∀ cs : List Branch, cs.length = K → ρwit (Branch.node cs) ≤ ρm)
    (hfin : ((K : ℝ) - 1) * umax + unc + ℓ - S0 / ((K : ℝ) + 1 + S0) + α + ρm ≤ 0)
    (cs : List Branch) (hlen : cs.length = K) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + (cs.map (rateG α)).sum ≤ 0 := by
  set σ := 1 / ((K : ℝ) + 1 + S0) with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hd : (0:ℝ) < (K : ℝ) + 1 := by positivity
  have htan := log_tangent hd (sumY_nonneg cs) hS0
  have hsum := sum_le_of_one_gap (f := fun c => rateG α c + σ * bY c) (g := umax) (δ := umax - unc) cs
    (fun c hc => by
      by_cases hC : c = cherry
      · subst hC; have := cherry_le_env (σ := σ) (α := α); linarith
      · have := child_le_env hσ0 hD hL hArm hN (hcap c hc) hC; linarith)
    (by obtain ⟨c, hc, hne⟩ := exists_ne_cherry_of_nonatom cs hna
        exact ⟨c, hc, by have := child_le_env hσ0 hD hL hArm hN (hcap c hc) hne; linarith⟩)
  rw [sum_rateG_add, hlen] at hsum
  have hρ' := hρ cs hlen
  rw [hlen]
  have hsplit : ((cs.map bY).sum - S0) / ((K : ℝ) + 1 + S0) = σ * (cs.map bY).sum - S0 / ((K : ℝ) + 1 + S0) := by
    rw [hσ]; field_simp
  linarith

/-- **Generic rate cell, `K = 1`.** -/
theorem rate_cell_one {D : ℕ} (hD : D ≤ 23) {α S0 ℓ u : ℝ} (hS0 : 0 ≤ S0)
    (hℓ : Real.log (1 + S0 / ((1 : ℝ) + 1)) - FSTAR ≤ ℓ)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      1 / ((1 : ℝ) + 1 + S0) * (3 / (4 * (j : ℝ) + 3)) + 1 / (4 * (2 + 3 / (4 * (j : ℝ) + 3))) + bjT j
        + α * (2 * (j : ℝ) + 1) ≤ u)
    (hN : Nb1 (1 / ((1 : ℝ) + 1 + S0)) ≤ u)
    (hfin : u + ℓ - S0 / ((1 : ℝ) + 1 + S0) + 133 / 17061 - 1 / 12 + α ≤ 0)
    (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + (cs.map (rateG α)).sum ≤ 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen
  have hC : c ≠ cherry := by rintro rfl; exact hna (Or.inr ⟨1, rfl⟩)
  have hL : c ≠ Branch.node [] := by rintro rfl; exact hna (Or.inl rfl)
  set σ := 1 / ((1 : ℝ) + 1 + S0) with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hw := child_le_env1 hσ0 hD hArm hN (hcap c (by simp)) hC hL
  have hy0 := bY_nonneg c
  have htan := log_tangent (d := (1:ℝ) + 1) (by norm_num) hy0 hS0
  have hAh := cherry_anchor_le_tight
  have hyv : bY (Branch.node [c]) = 1 / (2 + bY c) := by rw [bY_node]; simp; ring_nf
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_cons,
    List.length_nil, zero_add]
  simp only [ρwit, bcc, List.length_cons, List.length_nil]
  rw [hyv]
  have hsplit : (bY c - S0) / ((1:ℝ) + 1 + S0) = σ * bY c - S0 / ((1:ℝ) + 1 + S0) := by
    rw [hσ]; field_simp
  have h4 : 1 / (2 + bY c) / 4 = 1 / (4 * (2 + bY c)) := by field_simp
  norm_num at htan hsplit hℓ ⊢
  have hinv : (2 + bY c)⁻¹ = 4 * (1 / (4 * (2 + bY c))) := by field_simp
  have hS : S0 / (2 + S0) = S0 / (1 + 1 + S0) := by norm_num
  linarith [hinv, hS]

/-- **Generic root cell.** -/
theorem root_generic {D k : ℕ} (hk : 1 ≤ k) (hD : D ≤ 23) {α t ℓt umax unc : ℝ} (ht : 0 < t)
    (hℓ : Real.log t ≤ ℓt)
    (hL : -((847797 / 110000000 + 2027323 / 5000000) / 2) + α + 1 / ((k : ℝ) * t) ≤ unc)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      bjT j + α * (2 * (j : ℝ) + 1) + 1 / ((k : ℝ) * t) * (3 / (4 * (j : ℝ) + 3)) ≤ unc)
    (hN : Nb (1 / ((k : ℝ) * t)) ≤ unc)
    (hCu : -(847797 / 110000000) + 2 * α + 1 / ((k : ℝ) * t) * (1 / 3) ≤ umax) (hu : unc ≤ umax)
    (cs : List Branch) (hlen : cs.length = k) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG α)).sum
      ≤ (k : ℝ) * umax + ℓt + 1 / t - 1 := by
  set σ := 1 / ((k : ℝ) * t) with hσ
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hfac : (0:ℝ) < 1 + (cs.map bY).sum / (cs.length : ℝ) := by
    have := div_nonneg (sumY_nonneg cs) (Nat.cast_nonneg cs.length); linarith
  have htan := log_le_tangent_at hfac ht
  have hsum := sum_le_length_mul (f := fun c => rateG α c + σ * bY c) (g := umax) cs
    (fun c hc => by
      by_cases hC : c = cherry
      · subst hC; have := cherry_le_env (σ := σ) (α := α); linarith
      · have := child_le_env hσ0 hD hL hArm hN (hcap c hc) hC; linarith)
  rw [sum_rateG_add, hlen] at hsum
  rw [hlen] at htan ⊢
  have hsplit : (1 + (cs.map bY).sum / (k : ℝ)) / t = 1 / t + σ * (cs.map bY).sum := by
    rw [hσ]; field_simp
  linarith

theorem log_26_23_ge : (613011 / 5000000 : ℝ) ≤ Real.log (26 / 23) :=
  le_log_of_taylor (x := 26 / 23) (c := 613011 / 5000000) (a := 613011 / 5000000) (by norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)

/-! ### Rate-cell instances (generated by `bg_spider_reduction.py gen-rate`). -/

theorem rcell_2_1 (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 2)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/135 : ℝ)
      + (cs.map (rateG (1/135 : ℝ))).sum ≤ 0 :=
  rate_cell_one (D := 2) (by norm_num) (S0 := (1/2 : ℝ)) (ℓ := (14229/859375 : ℝ)) (u := (82706609/330000000 : ℝ)) (by norm_num)
    (by
    have e : (1 + (1/2 : ℝ) / ((1:ℝ) + 1)) = (5/4 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (5/4 : ℝ) ^ 11 * (64 / 621)) (c := (14229/78125 : ℝ)) (a := (14229/78125 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by intro j h1 h2; have h3 : j ≤ 1 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb1; simp only [max_le_iff]; norm_num)
    (by norm_num) cs hlen hcap hna

theorem rcell_3_1 (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 3)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/420 : ℝ)
      + (cs.map (rateG (1/420 : ℝ))).sum ≤ 0 :=
  rate_cell_one (D := 3) (by norm_num) (S0 := (1/2 : ℝ)) (ℓ := (14229/859375 : ℝ)) (u := (82706609/330000000 : ℝ)) (by norm_num)
    (by
    have e : (1 + (1/2 : ℝ) / ((1:ℝ) + 1)) = (5/4 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (5/4 : ℝ) ^ 11 * (64 / 621)) (c := (14229/78125 : ℝ)) (a := (14229/78125 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by intro j h1 h2; have h3 : j ≤ 2 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb1; simp only [max_le_iff]; norm_num)
    (by norm_num) cs hlen hcap hna

theorem rcell_3_2 (cs : List Branch) (hlen : cs.length = 2) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 3)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/420 : ℝ)
      + (cs.map (rateG (1/420 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 3) (K := 2) (by norm_num) (S0 := (167/200 : ℝ)) (ℓ := (535867/13750000 : ℝ)) (umax := (148781533721/1771770000000 : ℝ))
    (unc := (20502969103/253110000000 : ℝ)) (ρm := (1/96 : ℝ)) (by norm_num)
    (by
    have e : (1 + (167/200 : ℝ) / ((((2:ℕ):ℝ)) + 1)) = (767/600 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (767/600 : ℝ) ^ 11 * (64 / 621)) (c := (535867/1250000 : ℝ)) (a := (535867/1250000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 2 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_4_1 (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 4)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/660 : ℝ)
      + (cs.map (rateG (1/660 : ℝ))).sum ≤ 0 :=
  rate_cell_one (D := 4) (by norm_num) (S0 := (1/2 : ℝ)) (ℓ := (14229/859375 : ℝ)) (u := (82706609/330000000 : ℝ)) (by norm_num)
    (by
    have e : (1 + (1/2 : ℝ) / ((1:ℝ) + 1)) = (5/4 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (5/4 : ℝ) ^ 11 * (64 / 621)) (c := (14229/78125 : ℝ)) (a := (14229/78125 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by intro j h1 h2; have h3 : j ≤ 3 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb1; simp only [max_le_iff]; norm_num)
    (by norm_num) cs hlen hcap hna

theorem rcell_4_2 (cs : List Branch) (hlen : cs.length = 2) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 4)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/660 : ℝ)
      + (cs.map (rateG (1/660 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 4) (K := 2) (by norm_num) (S0 := (167/200 : ℝ)) (ℓ := (535867/13750000 : ℝ)) (umax := (6938739701/84370000000 : ℝ))
    (unc := (20502969103/253110000000 : ℝ)) (ρm := (1/96 : ℝ)) (by norm_num)
    (by
    have e : (1 + (167/200 : ℝ) / ((((2:ℕ):ℝ)) + 1)) = (767/600 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (767/600 : ℝ) ^ 11 * (64 / 621)) (c := (535867/1250000 : ℝ)) (a := (535867/1250000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 3 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_4_3 (cs : List Branch) (hlen : cs.length = 3) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 4)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/660 : ℝ)
      + (cs.map (rateG (1/660 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 4) (K := 3) (by norm_num) (S0 := (399/400 : ℝ)) (ℓ := (883149/55000000 : ℝ)) (umax := (13638253797/219890000000 : ℝ))
    (unc := (10801/191904 : ℝ)) (ρm := (1/1536 : ℝ)) (by norm_num)
    (by
    have e : (1 + (399/400 : ℝ) / ((((3:ℕ):ℝ)) + 1)) = (1999/1600 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1999/1600 : ℝ) ^ 11 * (64 / 621)) (c := (883149/5000000 : ℝ)) (a := (883149/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 3 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_5_1 (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 5)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/2100 : ℝ)
      + (cs.map (rateG (1/2100 : ℝ))).sum ≤ 0 :=
  rate_cell_one (D := 5) (by norm_num) (S0 := (1/2 : ℝ)) (ℓ := (14229/859375 : ℝ)) (u := (82706609/330000000 : ℝ)) (by norm_num)
    (by
    have e : (1 + (1/2 : ℝ) / ((1:ℝ) + 1)) = (5/4 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (5/4 : ℝ) ^ 11 * (64 / 621)) (c := (14229/78125 : ℝ)) (a := (14229/78125 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by intro j h1 h2; have h3 : j ≤ 4 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb1; simp only [max_le_iff]; norm_num)
    (by norm_num) cs hlen hcap hna

theorem rcell_5_2 (cs : List Branch) (hlen : cs.length = 2) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 5)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/2100 : ℝ)
      + (cs.map (rateG (1/2100 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 5) (K := 2) (by norm_num) (S0 := (91/100 : ℝ)) (ℓ := (3209379/55000000 : ℝ)) (umax := (10129284119/129030000000 : ℝ))
    (unc := (10129284119/129030000000 : ℝ)) (ρm := (1/96 : ℝ)) (by norm_num)
    (by
    have e : (1 + (91/100 : ℝ) / ((((2:ℕ):ℝ)) + 1)) = (391/300 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (391/300 : ℝ) ^ 11 * (64 / 621)) (c := (3209379/5000000 : ℝ)) (a := (3209379/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 4 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_5_3 (cs : List Branch) (hlen : cs.length = 3) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 5)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/2100 : ℝ)
      + (cs.map (rateG (1/2100 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 5) (K := 3) (by norm_num) (S0 := (399/400 : ℝ)) (ℓ := (883149/55000000 : ℝ)) (umax := (92269376579/1539230000000 : ℝ))
    (unc := (10801/191904 : ℝ)) (ρm := (1/1536 : ℝ)) (by norm_num)
    (by
    have e : (1 + (399/400 : ℝ) / ((((3:ℕ):ℝ)) + 1)) = (1999/1600 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1999/1600 : ℝ) ^ 11 * (64 / 621)) (c := (883149/5000000 : ℝ)) (a := (883149/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 4 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_5_4 (cs : List Branch) (hlen : cs.length = 4) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 5)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/2100 : ℝ)
      + (cs.map (rateG (1/2100 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 5) (K := 4) (by norm_num) (S0 := (133/100 : ℝ)) (ℓ := (1610201/55000000 : ℝ)) (umax := (67122834479/1462230000000 : ℝ))
    (unc := (2567/60768 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (133/100 : ℝ) / ((((4:ℕ):ℝ)) + 1)) = (633/500 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (633/500 : ℝ) ^ 11 * (64 / 621)) (c := (1610201/5000000 : ℝ)) (a := (1610201/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 4 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_1 (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_one (D := 23) (by norm_num) (S0 := (1/2 : ℝ)) (ℓ := (14229/859375 : ℝ)) (u := (82706609/330000000 : ℝ)) (by norm_num)
    (by
    have e : (1 + (1/2 : ℝ) / ((1:ℝ) + 1)) = (5/4 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (5/4 : ℝ) ^ 11 * (64 / 621)) (c := (14229/78125 : ℝ)) (a := (14229/78125 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb1; simp only [max_le_iff]; norm_num)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_2 (cs : List Branch) (hlen : cs.length = 2) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 2) (by norm_num) (S0 := (19/20 : ℝ)) (ℓ := (471263/6875000 : ℝ)) (umax := (74487068107/964590000000 : ℝ))
    (unc := (2012822111/26070000000 : ℝ)) (ρm := (1/96 : ℝ)) (by norm_num)
    (by
    have e : (1 + (19/20 : ℝ) / ((((2:ℕ):ℝ)) + 1)) = (79/60 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (79/60 : ℝ) ^ 11 * (64 / 621)) (c := (471263/625000 : ℝ)) (a := (471263/625000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_3 (cs : List Branch) (hlen : cs.length = 3) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 3) (by norm_num) (S0 := (399/400 : ℝ)) (ℓ := (883149/55000000 : ℝ)) (umax := (1453076571467/24407790000000 : ℝ))
    (unc := (10801/191904 : ℝ)) (ρm := (1/1536 : ℝ)) (by norm_num)
    (by
    have e : (1 + (399/400 : ℝ) / ((((3:ℕ):ℝ)) + 1)) = (1999/1600 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1999/1600 : ℝ) ^ 11 * (64 / 621)) (c := (883149/5000000 : ℝ)) (a := (883149/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_4 (cs : List Branch) (hlen : cs.length = 4) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 4) (by norm_num) (S0 := (133/100 : ℝ)) (ℓ := (1610201/55000000 : ℝ)) (umax := (351609039389/7728930000000 : ℝ))
    (unc := (2567/60768 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (133/100 : ℝ) / ((((4:ℕ):ℝ)) + 1)) = (633/500 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (633/500 : ℝ) ^ 11 * (64 / 621)) (c := (1610201/5000000 : ℝ)) (a := (1610201/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_5 (cs : List Branch) (hlen : cs.length = 5) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 5) (by norm_num) (S0 := (133/80 : ℝ)) (ℓ := (2089661/55000000 : ℝ)) (umax := (271959148729/7484730000000 : ℝ))
    (unc := (649/19616 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (133/80 : ℝ) / ((((5:ℕ):ℝ)) + 1)) = (613/480 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (613/480 : ℝ) ^ 11 * (64 / 621)) (c := (2089661/5000000 : ℝ)) (a := (2089661/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_6 (cs : List Branch) (hlen : cs.length = 6) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 6) (by norm_num) (S0 := (48/25 : ℝ)) (ℓ := (787609/22000000 : ℝ)) (umax := (82236280859/2722830000000 : ℝ))
    (unc := (9377/342528 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (48/25 : ℝ) / ((((6:ℕ):ℝ)) + 1)) = (223/175 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (223/175 : ℝ) ^ 11 * (64 / 621)) (c := (787609/2000000 : ℝ)) (a := (787609/2000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_7 (cs : List Branch) (hlen : cs.length = 7) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 7) (by norm_num) (S0 := (903/400 : ℝ)) (ℓ := (52479/1250000 : ℝ)) (umax := (10487314619/414030000000 : ℝ))
    (unc := (149497/6302208 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (903/400 : ℝ) / ((((7:ℕ):ℝ)) + 1)) = (4103/3200 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (4103/3200 : ℝ) ^ 11 * (64 / 621)) (c := (577269/1250000 : ℝ)) (a := (577269/1250000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_8 (cs : List Branch) (hlen : cs.length = 8) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 8) (by norm_num) (S0 := (129/50 : ℝ)) (ℓ := (454727/10000000 : ℝ)) (umax := (152834334607/7069590000000 : ℝ))
    (unc := (2069/98816 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (129/50 : ℝ) / ((((8:ℕ):ℝ)) + 1)) = (193/150 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (193/150 : ℝ) ^ 11 * (64 / 621)) (c := (5001997/10000000 : ℝ)) (a := (5001997/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_9 (cs : List Branch) (hlen : cs.length = 9) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 9) (by norm_num) (S0 := (279/100 : ℝ)) (ℓ := (4344353/110000000 : ℝ)) (umax := (37121/1964544 : ℝ))
    (unc := (37121/1964544 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (279/100 : ℝ) / ((((9:ℕ):ℝ)) + 1)) = (1279/1000 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (1279/1000 : ℝ) ^ 11 * (64 / 621)) (c := (4344353/10000000 : ℝ)) (a := (4344353/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_10 (cs : List Branch) (hlen : cs.length = 10) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 10) (by norm_num) (S0 := (5/2 : ℝ)) (ℓ := (-197093/110000000 : ℝ)) (umax := (247/13824 : ℝ))
    (unc := (247/13824 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (5/2 : ℝ) / ((((10:ℕ):ℝ)) + 1)) = (27/22 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (27/22 : ℝ) ^ 11 * (64 / 621)) (c := (-197093/10000000 : ℝ)) (a := (197093/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_11 (cs : List Branch) (hlen : cs.length = 11) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 11) (by norm_num) (S0 := (11/4 : ℝ)) (ℓ := (-27471/110000000 : ℝ)) (umax := (1477/90624 : ℝ))
    (unc := (1477/90624 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (11/4 : ℝ) / ((((11:ℕ):ℝ)) + 1)) = (59/48 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (59/48 : ℝ) ^ 11 * (64 / 621)) (c := (-27471/10000000 : ℝ)) (a := (27471/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_12 (cs : List Branch) (hlen : cs.length = 12) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 12) (by norm_num) (S0 := (3 : ℝ)) (ℓ := (2633/2500000 : ℝ)) (umax := (23/1536 : ℝ))
    (unc := (23/1536 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (3 : ℝ) / ((((12:ℕ):ℝ)) + 1)) = (16/13 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (16/13 : ℝ) ^ 11 * (64 / 621)) (c := (28963/2500000 : ℝ)) (a := (28963/2500000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_13 (cs : List Branch) (hlen : cs.length = 13) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 13) (by norm_num) (S0 := (13/4 : ℝ)) (ℓ := (238551/110000000 : ℝ)) (umax := (163/11776 : ℝ))
    (unc := (163/11776 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (13/4 : ℝ) / ((((13:ℕ):ℝ)) + 1)) = (69/56 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (69/56 : ℝ) ^ 11 * (64 / 621)) (c := (238551/10000000 : ℝ)) (a := (238551/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_14 (cs : List Branch) (hlen : cs.length = 14) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 14) (by norm_num) (S0 := (7/2 : ℝ)) (ℓ := (17239/5500000 : ℝ)) (umax := (731/56832 : ℝ))
    (unc := (731/56832 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (7/2 : ℝ) / ((((14:ℕ):ℝ)) + 1)) = (37/30 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (37/30 : ℝ) ^ 11 * (64 / 621)) (c := (17239/500000 : ℝ)) (a := (17239/500000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_15 (cs : List Branch) (hlen : cs.length = 15) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 15) (by norm_num) (S0 := (15/4 : ℝ)) (ℓ := (19893/5000000 : ℝ)) (umax := (1457/121344 : ℝ))
    (unc := (1457/121344 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (15/4 : ℝ) / ((((15:ℕ):ℝ)) + 1)) = (79/64 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (79/64 : ℝ) ^ 11 * (64 / 621)) (c := (218823/5000000 : ℝ)) (a := (218823/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_16 (cs : List Branch) (hlen : cs.length = 16) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 16) (by norm_num) (S0 := (4 : ℝ)) (ℓ := (259761/55000000 : ℝ)) (umax := (121/10752 : ℝ))
    (unc := (121/10752 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (4 : ℝ) / ((((16:ℕ):ℝ)) + 1)) = (21/17 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (21/17 : ℝ) ^ 11 * (64 / 621)) (c := (259761/5000000 : ℝ)) (a := (259761/5000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_17 (cs : List Branch) (hlen : cs.length = 17) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 17) (by norm_num) (S0 := (17/4 : ℝ)) (ℓ := (592249/110000000 : ℝ)) (umax := (1447/136704 : ℝ))
    (unc := (1447/136704 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (17/4 : ℝ) / ((((17:ℕ):ℝ)) + 1)) = (89/72 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (89/72 : ℝ) ^ 11 * (64 / 621)) (c := (592249/10000000 : ℝ)) (a := (592249/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_18 (cs : List Branch) (hlen : cs.length = 18) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 18) (by norm_num) (S0 := (9/2 : ℝ)) (ℓ := (1027/171875 : ℝ)) (umax := (721/72192 : ℝ))
    (unc := (721/72192 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (9/2 : ℝ) / ((((18:ℕ):ℝ)) + 1)) = (47/38 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (47/38 : ℝ) ^ 11 * (64 / 621)) (c := (1027/15625 : ℝ)) (a := (1027/15625 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_19 (cs : List Branch) (hlen : cs.length = 19) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 19) (by norm_num) (S0 := (19/4 : ℝ)) (ℓ := (28631/4400000 : ℝ)) (umax := (479/50688 : ℝ))
    (unc := (479/50688 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (19/4 : ℝ) / ((((19:ℕ):ℝ)) + 1)) = (99/80 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (99/80 : ℝ) ^ 11 * (64 / 621)) (c := (28631/400000 : ℝ)) (a := (28631/400000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_20 (cs : List Branch) (hlen : cs.length = 20) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 20) (by norm_num) (S0 := (5 : ℝ)) (ℓ := (768673/110000000 : ℝ)) (umax := (179/19968 : ℝ))
    (unc := (179/19968 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (5 : ℝ) / ((((20:ℕ):ℝ)) + 1)) = (26/21 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (26/21 : ℝ) ^ 11 * (64 / 621)) (c := (768673/10000000 : ℝ)) (a := (768673/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_21 (cs : List Branch) (hlen : cs.length = 21) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 21) (by norm_num) (S0 := (21/4 : ℝ)) (ℓ := (74249/10000000 : ℝ)) (umax := (1427/167424 : ℝ))
    (unc := (1427/167424 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (21/4 : ℝ) / ((((21:ℕ):ℝ)) + 1)) = (109/88 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (109/88 : ℝ) ^ 11 * (64 / 621)) (c := (816739/10000000 : ℝ)) (a := (816739/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rcell_23_22 (cs : List Branch) (hlen : cs.length = 22) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + (1/3700 : ℝ)
      + (cs.map (rateG (1/3700 : ℝ))).sum ≤ 0 :=
  rate_cell_generic (D := 23) (K := 22) (by norm_num) (S0 := (11/2 : ℝ)) (ℓ := (78237/10000000 : ℝ)) (umax := (79/9728 : ℝ))
    (unc := (79/9728 : ℝ)) (ρm := (0 : ℝ)) (by norm_num)
    (by
    have e : (1 + (11/2 : ℝ) / ((((22:ℕ):ℝ)) + 1)) = (57/46 : ℝ) := by norm_num
    rw [e, log_sub_fstar_eq (by norm_num)]
    have h := log_le_of_taylor (x := (57/46 : ℝ) ^ 11 * (64 / 621)) (c := (860607/10000000 : ℝ)) (a := (860607/10000000 : ℝ))
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    linarith)
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    (fun cs' h => by have := ρwit_node_le cs' (by omega); rw [h] at this; simpa using this)
    (by norm_num) cs hlen hcap hna

theorem rateCellCap_2 : RateCellCap 2 (1/135 : ℝ) := by
  intro cs hlen hcap hna
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  have hK0 : 1 ≤ K := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · simp at hK; omega
  have hKD : K ≤ 1 := by omega
  interval_cases K
  · exact rcell_2_1 cs hK hcap hna

theorem rateCellCap_3 : RateCellCap 3 (1/420 : ℝ) := by
  intro cs hlen hcap hna
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  have hK0 : 1 ≤ K := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · simp at hK; omega
  have hKD : K ≤ 2 := by omega
  interval_cases K
  · exact rcell_3_1 cs hK hcap hna
  · exact rcell_3_2 cs hK hcap hna

theorem rateCellCap_4 : RateCellCap 4 (1/660 : ℝ) := by
  intro cs hlen hcap hna
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  have hK0 : 1 ≤ K := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · simp at hK; omega
  have hKD : K ≤ 3 := by omega
  interval_cases K
  · exact rcell_4_1 cs hK hcap hna
  · exact rcell_4_2 cs hK hcap hna
  · exact rcell_4_3 cs hK hcap hna

theorem rateCellCap_5 : RateCellCap 5 (1/2100 : ℝ) := by
  intro cs hlen hcap hna
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  have hK0 : 1 ≤ K := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · simp at hK; omega
  have hKD : K ≤ 4 := by omega
  interval_cases K
  · exact rcell_5_1 cs hK hcap hna
  · exact rcell_5_2 cs hK hcap hna
  · exact rcell_5_3 cs hK hcap hna
  · exact rcell_5_4 cs hK hcap hna

theorem rateCellCap_23 : RateCellCap 23 (1/3700 : ℝ) := by
  intro cs hlen hcap hna
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  have hK0 : 1 ≤ K := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · simp at hK; omega
  have hKD : K ≤ 22 := by omega
  interval_cases K
  · exact rcell_23_1 cs hK hcap hna
  · exact rcell_23_2 cs hK hcap hna
  · exact rcell_23_3 cs hK hcap hna
  · exact rcell_23_4 cs hK hcap hna
  · exact rcell_23_5 cs hK hcap hna
  · exact rcell_23_6 cs hK hcap hna
  · exact rcell_23_7 cs hK hcap hna
  · exact rcell_23_8 cs hK hcap hna
  · exact rcell_23_9 cs hK hcap hna
  · exact rcell_23_10 cs hK hcap hna
  · exact rcell_23_11 cs hK hcap hna
  · exact rcell_23_12 cs hK hcap hna
  · exact rcell_23_13 cs hK hcap hna
  · exact rcell_23_14 cs hK hcap hna
  · exact rcell_23_15 cs hK hcap hna
  · exact rcell_23_16 cs hK hcap hna
  · exact rcell_23_17 cs hK hcap hna
  · exact rcell_23_18 cs hK hcap hna
  · exact rcell_23_19 cs hK hcap hna
  · exact rcell_23_20 cs hK hcap hna
  · exact rcell_23_21 cs hK hcap hna
  · exact rcell_23_22 cs hK hcap hna

/-! ### Root-cell instances. -/

theorem rootcell_2 (cs : List Branch) (hlen : cs.length = 2) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 2) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/135 : ℝ))).sum ≤ (306400987639/959310000000 : ℝ) := by
  have h := root_generic (D := 2) (k := 2) (by norm_num) (by norm_num) (α := (1/135 : ℝ)) (t := (323/200 : ℝ))
    (ℓt := (2396821/5000000 : ℝ)) (umax := (211852116937/1918620000000 : ℝ)) (unc := (211852116937/1918620000000 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2396821/5000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 1 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (2:ℕ) * (211852116937/1918620000000 : ℝ) + (2396821/5000000 : ℝ) + 1 / (323/200 : ℝ) - 1 = (306400987639/959310000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_3 (cs : List Branch) (hlen : cs.length = 3) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 3) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/420 : ℝ))).sum ≤ (687941899/2467080000 : ℝ) := by
  have h := root_generic (D := 3) (k := 3) (by norm_num) (by norm_num) (α := (1/420 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (148550206663/1850310000000 : ℝ)) (unc := (6652414603/88110000000 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 2 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (3:ℕ) * (148550206663/1850310000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (687941899/2467080000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_4 (cs : List Branch) (hlen : cs.length = 4) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 4) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/660 : ℝ))).sum ≤ (23699553853/88110000000 : ℝ) := by
  have h := root_generic (D := 4) (k := 4) (by norm_num) (by norm_num) (α := (1/660 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (5087914603/88110000000 : ℝ)) (unc := (1333/25632 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 3 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (4:ℕ) * (5087914603/88110000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (23699553853/88110000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_5 (cs : List Branch) (hlen : cs.length = 5) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 5) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/2100 : ℝ))).sum ≤ (19575534899/77096250000 : ℝ) := by
  have h := root_generic (D := 5) (k := 5) (by norm_num) (by norm_num) (α := (1/2100 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (26633802221/616770000000 : ℝ)) (unc := (1013/25632 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 4 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (5:ℕ) * (26633802221/616770000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (19575534899/77096250000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_6 (cs : List Branch) (hlen : cs.length = 6) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (797688373183/3260070000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 6) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (336908120933/9780210000000 : ℝ)) (unc := (2399/76896 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (6:ℕ) * (336908120933/9780210000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (797688373183/3260070000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_7 (cs : List Branch) (hlen : cs.length = 7) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (387162206747/1630035000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 7) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (650452282177/22820490000000 : ℝ)) (unc := (24977/956928 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (7:ℕ) * (650452282177/22820490000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (387162206747/1630035000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_8 (cs : List Branch) (hlen : cs.length = 8) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (150192090761/652014000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 8) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (78386040311/3260070000000 : ℝ)) (unc := (1037/45568 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (8:ℕ) * (78386040311/3260070000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (150192090761/652014000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_9 (cs : List Branch) (hlen : cs.length = 9) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (181899123529/815017500000 : ℝ) := by
  have h := root_generic (D := 23) (k := 9) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (267/200 : ℝ))
    (ℓt := (2889331/10000000 : ℝ)) (umax := (603724362799/29340630000000 : ℝ)) (unc := (24799/1230336 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2889331/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (9:ℕ) * (603724362799/29340630000000 : ℝ) + (2889331/10000000 : ℝ) + 1 / (267/200 : ℝ) - 1 = (181899123529/815017500000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_10 (cs : List Branch) (hlen : cs.length = 10) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (13014779/60000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 10) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (32/25 : ℝ))
    (ℓt := (2468609/10000000 : ℝ)) (umax := (29/1536 : ℝ)) (unc := (29/1536 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2468609/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (10:ℕ) * (29/1536 : ℝ) + (2468609/10000000 : ℝ) + 1 / (32/25 : ℝ) - 1 = (13014779/60000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_11 (cs : List Branch) (hlen : cs.length = 11) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (25917893/120000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 11) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (1481/84480 : ℝ)) (unc := (1481/84480 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (11:ℕ) * (1481/84480 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (25917893/120000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_12 (cs : List Branch) (hlen : cs.length = 12) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (1076657/5000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 12) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (41/2560 : ℝ)) (unc := (41/2560 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (12:ℕ) * (41/2560 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (1076657/5000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_13 (cs : List Branch) (hlen : cs.length = 13) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (25761643/120000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 13) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (1471/99840 : ℝ)) (unc := (1471/99840 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (13:ℕ) * (1471/99840 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (25761643/120000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_14 (cs : List Branch) (hlen : cs.length = 14) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (12841759/60000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 14) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (733/53760 : ℝ)) (unc := (733/53760 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (14:ℕ) * (733/53760 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (12841759/60000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_15 (cs : List Branch) (hlen : cs.length = 15) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (8535131/40000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 15) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (487/38400 : ℝ)) (unc := (487/38400 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (15:ℕ) * (487/38400 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (8535131/40000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_16 (cs : List Branch) (hlen : cs.length = 16) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (6381817/30000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 16) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (91/7680 : ℝ)) (unc := (91/7680 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (16:ℕ) * (91/7680 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (6381817/30000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_17 (cs : List Branch) (hlen : cs.length = 17) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (25449143/120000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 17) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (1451/130560 : ℝ)) (unc := (1451/130560 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (17:ℕ) * (1451/130560 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (25449143/120000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_18 (cs : List Branch) (hlen : cs.length = 18) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (4228503/20000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 18) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (241/23040 : ℝ)) (unc := (241/23040 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (18:ℕ) * (241/23040 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (4228503/20000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_19 (cs : List Branch) (hlen : cs.length = 19) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (25292893/120000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 19) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (1441/145920 : ℝ)) (unc := (1441/145920 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (19:ℕ) * (1441/145920 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (25292893/120000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_20 (cs : List Branch) (hlen : cs.length = 20) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (1575923/7500000 : ℝ) := by
  have h := root_generic (D := 23) (k := 20) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (359/38400 : ℝ)) (unc := (359/38400 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (20:ℕ) * (359/38400 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (1575923/7500000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_21 (cs : List Branch) (hlen : cs.length = 21) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (8378881/40000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 21) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (159/17920 : ℝ)) (unc := (159/17920 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (21:ℕ) * (159/17920 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (8378881/40000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_22 (cs : List Branch) (hlen : cs.length = 22) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (12529259/60000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 22) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (713/84480 : ℝ)) (unc := (713/84480 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (22:ℕ) * (713/84480 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (12529259/60000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

theorem rootcell_23 (cs : List Branch) (hlen : cs.length = 23) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ 23) :
    Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG (1/3700 : ℝ))).sum ≤ (24980393/120000000 : ℝ) := by
  have h := root_generic (D := 23) (k := 23) (by norm_num) (by norm_num) (α := (1/3700 : ℝ)) (t := (5/4 : ℝ))
    (ℓt := (2231439/10000000 : ℝ)) (umax := (1421/176640 : ℝ)) (unc := (1421/176640 : ℝ)) (by norm_num)
    (log_le_of_taylor (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (a := (2231439/10000000 : ℝ)) (by norm_num))
    (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ 22 := by omega
        interval_cases j <;> norm_num [bjT])
    (by unfold Nb; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num) cs hlen hcap
  have e : (23:ℕ) * (1421/176640 : ℝ) + (2231439/10000000 : ℝ) + 1 / (5/4 : ℝ) - 1 = (24980393/120000000 : ℝ) := by norm_num
  push_cast at h e ⊢
  linarith

/-! ### The low-degree case, unconditional. -/

/-- **Spider domination for maximum degree `≤ 23` and `n ≥ 492` (UNCONDITIONAL).**  For a root list with
    `2 ≤ k ≤ 23` children in which every other vertex has `≤ k − 1` children (i.e. the root is a vertex of
    maximum degree and the maximum degree is `k`), and `n − 1 ≥ 491`, some arm_5/arm_4 spider of the same
    size has strictly larger `piRoot`. -/
theorem spider_dominates_lowDegree_uncond (cs : List Branch) (hk2 : 2 ≤ cs.length) (hk : cs.length ≤ 23)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length) (hN : 491 ≤ bsizeList cs) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) := by
  have hL := log_26_23_ge
  have hNR : (491:ℝ) ≤ (bsizeList cs : ℝ) := by exact_mod_cast hN
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  rw [hK] at hk2 hk hcap
  interval_cases K
  · have hb := phiRoot_le_rateCap rateCellCap_2 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_2 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_3 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_3 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_4 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_4 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_5 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_5 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_6 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_7 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_8 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_9 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_10 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_11 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_12 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_13 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_14 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_15 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_16 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_17 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_18 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_19 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_20 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_21 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_22 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)
  · have hb := phiRoot_le_rateCap rateCellCap_23 cs (fun c hc => by have := hcap c hc; omega)
    have hr := rootcell_23 cs hK (fun c hc => by have := hcap c hc; omega)
    exact spider_of_phiRoot_lt cs (by omega) (by linarith)

/-! ### Combined statement. -/

/-- **Spider reduction for `n ≥ 492`, rooted at a vertex of maximum degree (UNCONDITIONAL).**  Let `cs` be
    the child list of a root of maximum degree `k = |cs| ≥ 2` (every other vertex has `≤ k − 1`
    children), with `n − 1 = bsizeList cs ≥ 491`.  If some child is not an atom, or if `k ≤ 23`, then an
    arm_5/arm_4 spider of the same size has strictly larger `piRoot`.  (For `k ≥ 24` with only atom
    children the tree is itself a spider centred at the root.) -/
theorem spider_dominates_of_maxDegreeRoot (cs : List Branch) (hk2 : 2 ≤ cs.length)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length) (hN : 491 ≤ bsizeList cs)
    (hna : cs.length ≤ 23 ∨ ∃ c ∈ cs, ¬ IsAtom c) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) := by
  rcases le_or_gt cs.length 23 with hk | hk
  · exact spider_dominates_lowDegree_uncond cs hk2 hk hcap hN
  · rcases hna with h | h
    · omega
    · exact spider_dominates_highDegree_uncond cs (by omega) h (by omega)

end BGSCL
end R3Cert
