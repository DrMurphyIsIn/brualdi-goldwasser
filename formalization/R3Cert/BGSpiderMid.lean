/-
  BG spider reduction: the MID range `150 <= n <= 491`, generic layer (2026-09-25).

  Refines the low-degree rate cells of `BGSpiderLowDegree.lean` in two ways:
  * cap-refined message ranges: in a tree of maximum degree `<= D` every branch has `y >= 1/(2D-1)`
    (`bY_ge_ymin`), which tightens the per-class message ranges of non-atom children;
  * class credits: the invariant for a non-atom branch becomes
      `bell b + ρwit b <= -α |b| - κ(bcc b)`,   κ = (κ1, κ2, κ3, κ4) for `bcc = 1, 2, 3, >= 4`
    (`bell_add_ρwit_le_rateKap`), so non-atom children hand their surplus to the parent and the root.
  The root is then bounded by an explicit atom knapsack (`phiRoot_le_split`), certified per `(k, n)` in
  the generated files `BGSpiderMidCells*.lean` / `BGSpiderMidRoot*.lean`.

  No `sorry`; standard axioms.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSpiderLowDegree
import R3Cert.BGSpiderDP

namespace R3Cert
namespace BGSCL

open Real

/-! ### Class credits and the credited rate cell. -/

/-- The class credit of a branch, by its child count. -/
noncomputable def kapF (k1 k2 k3 k4 : ℝ) (b : Branch) : ℝ :=
  match bcc b with
  | 0 => 0
  | 1 => k1
  | 2 => k2
  | 3 => k3
  | _ => k4

/-- Per-child weight of the credited rate cell. -/
noncomputable def rateGK (α k1 k2 k3 k4 : ℝ) (c : Branch) : ℝ :=
  open Classical in
  if IsAtom c then bell c + α * (bsize c : ℝ) else -ρwit c - kapF k1 k2 k3 k4 c

/-- The credited rate cell under degree cap `D`. -/
def RateCellKap (D : ℕ) (α k1 k2 k3 k4 : ℝ) : Prop :=
  ∀ cs : List Branch, cs.length + 1 ≤ D → (∀ c ∈ cs, maxCh c + 1 ≤ D) → ¬ IsAtom (Branch.node cs) →
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + kapF k1 k2 k3 k4 (Branch.node cs) + (cs.map (rateGK α k1 k2 k3 k4)).sum ≤ 0

theorem bell_le_rateGK {α k1 k2 k3 k4 : ℝ} {c : Branch}
    (h : ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ) - kapF k1 k2 k3 k4 c) :
    bell c ≤ rateGK α k1 k2 k3 k4 c - α * (bsize c : ℝ) := by
  unfold rateGK
  split_ifs with ha
  · linarith
  · have := h ha; linarith

theorem sum_bell_le_rateGK {α k1 k2 k3 k4 : ℝ} : ∀ (cs : List Branch),
    (∀ c ∈ cs, ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ) - kapF k1 k2 k3 k4 c) →
    (cs.map bell).sum ≤ (cs.map (rateGK α k1 k2 k3 k4)).sum - α * (bsizeList cs : ℝ)
  | [], _ => by simp [bsizeList]
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons, bsizeList, Nat.cast_add]
      have ha := bell_le_rateGK (h a (List.mem_cons.mpr (Or.inl rfl)))
      have ht := sum_bell_le_rateGK t (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
      linarith

/-- **Credited linear deficit.** -/
theorem bell_add_ρwit_le_rateKap {D : ℕ} {α k1 k2 k3 k4 : ℝ} (hR : RateCellKap D α k1 k2 k3 k4) :
    ∀ b, maxCh b + 1 ≤ D → ¬ IsAtom b →
      bell b + ρwit b ≤ -α * (bsize b : ℝ) - kapF k1 k2 k3 k4 b := by
  refine scl_of_child_step bsize bchildren
    (fun b => maxCh b + 1 ≤ D → ¬ IsAtom b →
      bell b + ρwit b ≤ -α * (bsize b : ℝ) - kapF k1 k2 k3 k4 b)
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
    have hch : ∀ c ∈ cs, ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ) - kapF k1 k2 k3 k4 c :=
      fun c hc => hIH c (by simpa only [bchildren] using hc) (hcc c hc)
    have hsum := sum_bell_le_rateGK cs hch
    have hcell := hR cs hlen hcc hna
    have hsz : (bsize (Branch.node cs) : ℝ) = 1 + (bsizeList cs : ℝ) := by
      simp only [bsize]; push_cast; ring
    rw [bell_node, hsz]
    linarith

/-! ### Message ranges under a degree cap. -/

theorem sumY_le_length (cs : List Branch) : (cs.map bY).sum ≤ (cs.length : ℝ) := by
  induction cs with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      have := bY_le_one a; linarith

/-- **Minimal message under a degree cap:** `maxCh b + 1 ≤ D → 1/(2D−1) ≤ y_b`. -/
theorem bY_ge_ymin {D : ℕ} {b : Branch} (h : maxCh b + 1 ≤ D) :
    1 / (2 * (D : ℝ) - 1) ≤ bY b := by
  cases b with
  | node cs =>
    rw [maxCh_node] at h
    have hl : cs.length + 1 ≤ D := by have := le_max_left cs.length (maxChList cs); omega
    have hlR : (cs.length : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast hl
    have hS := sumY_le_length cs
    have hS0 := sumY_nonneg cs
    rw [bY_node]
    apply one_div_le_one_div_of_le (by positivity)
    linarith

/-- Sum of messages of capped children is at least `|cs| / (2D−1)`. -/
theorem sumY_ge_ymin {D : ℕ} : ∀ (cs : List Branch), (∀ c ∈ cs, maxCh c + 1 ≤ D) →
    (cs.length : ℝ) * (1 / (2 * (D : ℝ) - 1)) ≤ (cs.map bY).sum
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      have ha := bY_ge_ymin (h a (List.mem_cons.mpr (Or.inl rfl)))
      have ht := sumY_ge_ymin t (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
      linarith

theorem bsize_ge_one (b : Branch) : 1 ≤ bsize b := by
  cases b with
  | node cs => simp only [bsize]; omega

/-- A non-atom branch has at least three vertices. -/
theorem three_le_bsize_of_nonatom {b : Branch} (h : ¬ IsAtom b) : 3 ≤ bsize b := by
  cases b with
  | node cs =>
    rcases cs with _ | ⟨c, _ | ⟨c2, t⟩⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) h
    · cases c with
      | node cs' =>
        rcases cs' with _ | ⟨d, t'⟩
        · exact absurd (Or.inl rfl) h
        · have := bsize_ge_one d
          simp only [bsize, bsizeList] at this ⊢
          omega
    · have h1 := bsize_ge_one c; have h2 := bsize_ge_one c2
      simp only [bsize, bsizeList] at h1 h2 ⊢
      omega

/-! ### Per-class envelope of a non-atom child (cap-refined ranges, credits). -/

/-- Envelope `−ρwit c − κ(c) + σ y_c` over non-atom children, cap `D`; endpoints of the refined ranges. -/
noncomputable def NbK (D : ℝ) (k1 k2 k3 k4 σ : ℝ) : ℝ :=
  max (max (-(847797 / 110000000) - (2 / 5 - 1 / 3) / 4 - k1 + σ * (2 / 5))
           (-(847797 / 110000000) - (1 / (2 + 1 / (2 * D - 1)) - 1 / 3) / 4 - k1
              + σ * (1 / (2 + 1 / (2 * D - 1)))))
      (max (max (-(1 / 5) / 32 - k2 + σ * (1 / 5))
                (-(1 / (3 + 2 * (1 / (2 * D - 1)))) / 32 - k2 + σ * (1 / (3 + 2 * (1 / (2 * D - 1))))))
           (max (max (-(1 / 7) / 384 - k3 + σ * (1 / 7))
                     (-(1 / (4 + 3 * (1 / (2 * D - 1)))) / 384 - k3
                        + σ * (1 / (4 + 3 * (1 / (2 * D - 1))))))
                (max (-k4 + σ * (1 / (2 * D - 1)))
                     (-k4 + σ * (1 / (5 + 4 * (1 / (2 * D - 1))))))))

/-- A linear function on `[lo, hi]` is below the max of its endpoint values. -/
theorem lin_le_max_ends {a b lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) :
    a + b * y ≤ max (a + b * lo) (a + b * hi) := by
  rcases le_total 0 b with hb | hb
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

theorem nonatom_le_NbK {D : ℕ} (hD : 2 ≤ D) {k1 k2 k3 k4 σ : ℝ} {c : Branch} (hna : ¬ IsAtom c)
    (hc : maxCh c + 1 ≤ D) :
    -ρwit c - kapF k1 k2 k3 k4 c + σ * bY c ≤ NbK (D : ℝ) k1 k2 k3 k4 σ := by
  have hA := anchor_ge_tight
  have hDR : (2:ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  set ym := 1 / (2 * (D : ℝ) - 1) with hym
  have hym0 : 0 < ym := by rw [hym]; apply one_div_pos.mpr; linarith
  cases c with
  | node cs =>
    have hcc : ∀ x ∈ cs, maxCh x + 1 ≤ D := fun x hx => by
      rw [maxCh_node] at hc
      have := maxCh_le_of_mem hx; have := le_max_right cs.length (maxChList cs); omega
    have hlenD : cs.length + 1 ≤ D := by
      rw [maxCh_node] at hc; have := le_max_left cs.length (maxChList cs); omega
    have hSlo := sumY_ge_ymin cs hcc
    have hShi := sumY_le_length cs
    have hyv := bY_node cs
    rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · -- bcc 1: child non-leaf, y_c1 ∈ [ym, 1/2]
      have hc1 : c1 ≠ Branch.node [] := by rintro rfl; exact hna (Or.inl rfl)
      have hy1 := bY_le_half_of_ne_leaf hc1
      have hy0 := bY_ge_ymin (hcc c1 (by simp))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil, zero_add] at hyv
      rw [show ((1:ℕ):ℝ) + 1 + bY c1 = 2 + bY c1 by push_cast; ring] at hyv
      have hlo : 2 / 5 ≤ bY (Branch.node [c1]) := by
        rw [hyv, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      have hhi : bY (Branch.node [c1]) ≤ 1 / (2 + ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by linarith); linarith
      simp only [ρwit, kapF, bcc, List.length_cons, List.length_nil]
      unfold NbK
      refine le_max_of_le_left ?_
      have := lin_le_max_ends (a := -(2 * FSTAR - Real.log (3 / 2)) + 1 / 12 - k1) (b := σ - 1 / 4) hlo hhi
      rw [← hym]
      refine le_trans (le_of_eq_of_le (by ring) this) (max_le_max (by nlinarith) (by nlinarith))
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil] at hyv hSlo hShi
      push_cast at hSlo hShi hyv
      have hlo : 1 / 5 ≤ bY (Branch.node [c1, c2]) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by linarith); linarith
      have hhi : bY (Branch.node [c1, c2]) ≤ 1 / (3 + 2 * ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by positivity); linarith
      simp only [ρwit, kapF, bcc, List.length_cons, List.length_nil]
      unfold NbK
      refine le_max_of_le_right (le_max_of_le_left ?_)
      have := lin_le_max_ends (a := -k2) (b := σ - 1 / 32) hlo hhi
      rw [← hym]
      refine le_trans (le_of_eq_of_le (by ring) this) (max_le_max (by nlinarith) (by nlinarith))
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil] at hyv hSlo hShi
      push_cast at hSlo hShi hyv
      have hlo : 1 / 7 ≤ bY (Branch.node [c1, c2, c3]) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by linarith); linarith
      have hhi : bY (Branch.node [c1, c2, c3]) ≤ 1 / (4 + 3 * ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by positivity); linarith
      simp only [ρwit, kapF, bcc, List.length_cons, List.length_nil]
      unfold NbK
      refine le_max_of_le_right (le_max_of_le_right (le_max_of_le_left ?_))
      have := lin_le_max_ends (a := -k3) (b := σ - 1 / 384) hlo hhi
      rw [← hym]
      refine le_trans (le_of_eq_of_le (by ring) this) (max_le_max (by nlinarith) (by nlinarith))
    · set L := c1 :: c2 :: c3 :: c4 :: t with hL
      have hlenR : (4:ℝ) ≤ (L.length : ℝ) := by
        rw [hL]; simp only [List.length_cons]; push_cast; linarith [(Nat.cast_nonneg t.length : (0:ℝ) ≤ _)]
      have hlenDR : (L.length : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast hlenD
      have hlo : ym ≤ bY (Branch.node L) := bY_ge_ymin hc
      have hhi : bY (Branch.node L) ≤ 1 / (5 + 4 * ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by positivity); nlinarith
      have hρ : ρwit (Branch.node L) = 0 := ρwit_node_of_four_le L (by rw [hL]; simp)
      have hk : kapF k1 k2 k3 k4 (Branch.node L) = k4 := by
        rw [hL]; simp [kapF, bcc]
      rw [hρ, hk]
      unfold NbK
      refine le_max_of_le_right (le_max_of_le_right (le_max_of_le_right ?_))
      have := lin_le_max_ends (a := -k4) (b := σ) hlo hhi
      rw [← hym]
      linarith [this]

/-! ### Degree-2 cells: chord of `1/(2+y)`. -/

/-- `a + b y + 1/(4(2+y)) ≤ max` of its endpoint values on `[lo, hi]` (chord of the convex `1/(2+y)`). -/
theorem chord_le_max_ends {a b lo hi y : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    a + b * y + 1 / (4 * (2 + y)) ≤ max (a + b * lo + 1 / (4 * (2 + lo))) (a + b * hi + 1 / (4 * (2 + hi))) := by
  have hl2 : (2:ℝ) + lo ≠ 0 := by positivity
  have hh2 : (2:ℝ) + hi ≠ 0 := by have : 0 ≤ hi := le_trans h0 (le_trans h1 h2); positivity
  have hy2 : (2:ℝ) + y ≠ 0 := by have : 0 ≤ y := le_trans h0 h1; positivity
  have hc : 1 / (4 * (2 + y)) ≤ 1 / (4 * (2 + lo)) - (y - lo) / (4 * ((2 + lo) * (2 + hi))) := by
    have key : 1 / (4 * (2 + lo)) - (y - lo) / (4 * ((2 + lo) * (2 + hi))) - 1 / (4 * (2 + y))
        = (y - lo) * (hi - y) / (4 * ((2 + lo) * (2 + hi) * (2 + y))) := by
      field_simp; ring
    have hnn : 0 ≤ (y - lo) * (hi - y) / (4 * ((2 + lo) * (2 + hi) * (2 + y))) := by
      apply div_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2))
      have : 0 ≤ hi := le_trans h0 (le_trans h1 h2); have : 0 ≤ y := le_trans h0 h1; positivity
    linarith
  have hlin := lin_le_max_ends (a := a + 1 / (4 * (2 + lo)) + lo / (4 * ((2 + lo) * (2 + hi))))
    (b := b - 1 / (4 * ((2 + lo) * (2 + hi)))) h1 h2
  have e1 : a + 1 / (4 * (2 + lo)) + lo / (4 * ((2 + lo) * (2 + hi)))
      + (b - 1 / (4 * ((2 + lo) * (2 + hi)))) * lo = a + b * lo + 1 / (4 * (2 + lo)) := by ring
  have e2 : a + 1 / (4 * (2 + lo)) + lo / (4 * ((2 + lo) * (2 + hi)))
      + (b - 1 / (4 * ((2 + lo) * (2 + hi)))) * hi = a + b * hi + 1 / (4 * (2 + hi)) := by
    field_simp; ring
  rw [e1, e2] at hlin
  have e3 : a + 1 / (4 * (2 + lo)) + lo / (4 * ((2 + lo) * (2 + hi)))
      + (b - 1 / (4 * ((2 + lo) * (2 + hi)))) * y
      = a + b * y + (1 / (4 * (2 + lo)) - (y - lo) / (4 * ((2 + lo) * (2 + hi)))) := by ring
  rw [e3] at hlin
  linarith

/-- Envelope of `−ρwit c − κ(c) + σ y_c + 1/(4(2+y_c))` over non-atom children, cap `D`. -/
noncomputable def Nb1K (D : ℝ) (k1 k2 k3 k4 σ : ℝ) : ℝ :=
  max (max (-(847797 / 110000000) - (2 / 5 - 1 / 3) / 4 - k1 + σ * (2 / 5) + 1 / (4 * (2 + 2 / 5)))
           (-(847797 / 110000000) - (1 / (2 + (1 / (2 * D - 1))) - 1 / 3) / 4 - k1 + σ * (1 / (2 + (1 / (2 * D - 1))))
              + 1 / (4 * (2 + 1 / (2 + (1 / (2 * D - 1)))))))
      (max (max (-(1 / 5) / 32 - k2 + σ * (1 / 5) + 1 / (4 * (2 + 1 / 5)))
                (-(1 / (3 + 2 * (1 / (2 * D - 1)))) / 32 - k2 + σ * (1 / (3 + 2 * (1 / (2 * D - 1)))) + 1 / (4 * (2 + 1 / (3 + 2 * (1 / (2 * D - 1)))))))
           (max (max (-(1 / 7) / 384 - k3 + σ * (1 / 7) + 1 / (4 * (2 + 1 / 7)))
                     (-(1 / (4 + 3 * (1 / (2 * D - 1)))) / 384 - k3 + σ * (1 / (4 + 3 * (1 / (2 * D - 1))))
                        + 1 / (4 * (2 + 1 / (4 + 3 * (1 / (2 * D - 1)))))))
                (max (-k4 + σ * (1 / (2 * D - 1)) + 1 / (4 * (2 + (1 / (2 * D - 1)))))
                     (-k4 + σ * (1 / (5 + 4 * (1 / (2 * D - 1)))) + 1 / (4 * (2 + 1 / (5 + 4 * (1 / (2 * D - 1)))))))))

theorem nonatom_le_Nb1K {D : ℕ} (hD : 2 ≤ D) {k1 k2 k3 k4 σ : ℝ} {c : Branch} (hna : ¬ IsAtom c)
    (hc : maxCh c + 1 ≤ D) :
    -ρwit c - kapF k1 k2 k3 k4 c + σ * bY c + 1 / (4 * (2 + bY c)) ≤ Nb1K (D : ℝ) k1 k2 k3 k4 σ := by
  have hA := anchor_ge_tight
  have hDR : (2:ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  set ym := 1 / (2 * (D : ℝ) - 1) with hym
  have hym0 : 0 < ym := by rw [hym]; apply one_div_pos.mpr; linarith
  cases c with
  | node cs =>
    have hcc : ∀ x ∈ cs, maxCh x + 1 ≤ D := fun x hx => by
      rw [maxCh_node] at hc
      have := maxCh_le_of_mem hx; have := le_max_right cs.length (maxChList cs); omega
    have hlenD : cs.length + 1 ≤ D := by
      rw [maxCh_node] at hc; have := le_max_left cs.length (maxChList cs); omega
    have hSlo := sumY_ge_ymin cs hcc
    have hShi := sumY_le_length cs
    have hyv := bY_node cs
    rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · have hc1 : c1 ≠ Branch.node [] := by rintro rfl; exact hna (Or.inl rfl)
      have hy1 := bY_le_half_of_ne_leaf hc1
      have hy0 := bY_ge_ymin (hcc c1 (by simp))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil, zero_add] at hyv
      rw [show ((1:ℕ):ℝ) + 1 + bY c1 = 2 + bY c1 by push_cast; ring] at hyv
      have hlo : 2 / 5 ≤ bY (Branch.node [c1]) := by
        rw [hyv, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      have hhi : bY (Branch.node [c1]) ≤ 1 / (2 + ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by linarith); linarith
      simp only [ρwit, kapF, bcc, List.length_cons, List.length_nil]
      unfold Nb1K
      refine le_max_of_le_left ?_
      have := chord_le_max_ends (a := -(2 * FSTAR - Real.log (3 / 2)) + 1 / 12 - k1) (b := σ - 1 / 4)
        (by norm_num) hlo hhi
      simp only [hym] at hhi hlo this ⊢
      refine le_trans (le_of_eq_of_le (by ring) this) (max_le_max (by first | nlinarith [hA] | (ring_nf; nlinarith [hA])) (by first | nlinarith [hA] | (ring_nf; nlinarith [hA])))
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil] at hyv hSlo hShi
      push_cast at hSlo hShi hyv
      have hlo : 1 / 5 ≤ bY (Branch.node [c1, c2]) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by linarith); linarith
      have hhi : bY (Branch.node [c1, c2]) ≤ 1 / (3 + 2 * ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by positivity); linarith
      simp only [ρwit, kapF, bcc, List.length_cons, List.length_nil]
      unfold Nb1K
      refine le_max_of_le_right (le_max_of_le_left ?_)
      have := chord_le_max_ends (a := -k2) (b := σ - 1 / 32) (by norm_num) hlo hhi
      simp only [hym] at hhi hlo this ⊢
      refine le_trans (le_of_eq_of_le (by ring) this) (max_le_max (by first | nlinarith [hA] | (ring_nf; nlinarith [hA])) (by first | nlinarith [hA] | (ring_nf; nlinarith [hA])))
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil] at hyv hSlo hShi
      push_cast at hSlo hShi hyv
      have hlo : 1 / 7 ≤ bY (Branch.node [c1, c2, c3]) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by linarith); linarith
      have hhi : bY (Branch.node [c1, c2, c3]) ≤ 1 / (4 + 3 * ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by positivity); linarith
      simp only [ρwit, kapF, bcc, List.length_cons, List.length_nil]
      unfold Nb1K
      refine le_max_of_le_right (le_max_of_le_right (le_max_of_le_left ?_))
      have := chord_le_max_ends (a := -k3) (b := σ - 1 / 384) (by norm_num) hlo hhi
      simp only [hym] at hhi hlo this ⊢
      refine le_trans (le_of_eq_of_le (by ring) this) (max_le_max (by first | nlinarith [hA] | (ring_nf; nlinarith [hA])) (by first | nlinarith [hA] | (ring_nf; nlinarith [hA])))
    · set L := c1 :: c2 :: c3 :: c4 :: t with hL
      have hlenR : (4:ℝ) ≤ (L.length : ℝ) := by
        rw [hL]; simp only [List.length_cons]; push_cast; linarith [(Nat.cast_nonneg t.length : (0:ℝ) ≤ _)]
      have hlo : ym ≤ bY (Branch.node L) := bY_ge_ymin hc
      have hhi : bY (Branch.node L) ≤ 1 / (5 + 4 * ym) := by
        rw [hyv]; apply one_div_le_one_div_of_le (by positivity); nlinarith
      have hρ : ρwit (Branch.node L) = 0 := ρwit_node_of_four_le L (by rw [hL]; simp)
      have hk : kapF k1 k2 k3 k4 (Branch.node L) = k4 := by
        rw [hL]; simp [kapF, bcc]
      rw [hρ, hk]
      unfold Nb1K
      refine le_max_of_le_right (le_max_of_le_right (le_max_of_le_right ?_))
      have := chord_le_max_ends (a := -k4) (b := σ) hym0.le hlo hhi
      simp only [hym] at hhi hlo this ⊢
      linarith [this]

/-! ### Per-child envelopes (atoms exact via `bjT`, non-atoms via `NbK`/`Nb1K`). -/

theorem child_le_envK {σ α u k1 k2 k3 k4 : ℝ} {D : ℕ} (hσ : 0 ≤ σ) (hD : 2 ≤ D) (hD23 : D ≤ 23)
    (hL : -((847797 / 110000000 + 2027323 / 5000000) / 2) + α + σ ≤ u)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      bjT j + α * (2 * (j : ℝ) + 1) + σ * (3 / (4 * (j : ℝ) + 3)) ≤ u)
    (hN : NbK (D : ℝ) k1 k2 k3 k4 σ ≤ u) {c : Branch} (hc : maxCh c + 1 ≤ D) (hC : c ≠ cherry) :
    rateGK α k1 k2 k3 k4 c + σ * bY c ≤ u := by
  unfold rateGK
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
  · have := nonatom_le_NbK hD (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) (σ := σ) ha hc; linarith

theorem cherry_le_envK {σ α k1 k2 k3 k4 : ℝ} :
    rateGK α k1 k2 k3 k4 cherry + σ * bY cherry ≤ -(847797 / 110000000) + 2 * α + σ * (1 / 3) := by
  have hat : IsAtom cherry := Or.inl rfl
  unfold rateGK; rw [if_pos hat, bell_cherry, bY_cherry, bsize_cherry]
  have := anchor_ge_tight; push_cast; linarith

theorem child_le_env1K {σ α u k1 k2 k3 k4 : ℝ} {D : ℕ} (hσ : 0 ≤ σ) (hD : 2 ≤ D) (hD23 : D ≤ 23)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      σ * (3 / (4 * (j : ℝ) + 3)) + 1 / (4 * (2 + 3 / (4 * (j : ℝ) + 3))) + bjT j
        + α * (2 * (j : ℝ) + 1) ≤ u)
    (hN : Nb1K (D : ℝ) k1 k2 k3 k4 σ ≤ u) {c : Branch} (hc : maxCh c + 1 ≤ D) (hC : c ≠ cherry)
    (hL : c ≠ Branch.node []) :
    σ * bY c + 1 / (4 * (2 + bY c)) + rateGK α k1 k2 k3 k4 c ≤ u := by
  unfold rateGK
  split_ifs with ha
  · rcases ha with rfl | ⟨j, rfl⟩
    · exact absurd rfl hC
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd rfl hL
      · have hjm := maxCh_armB_ge j
        have hb := arm_bell_le_T j hj (by omega)
        have hA := hArm j hj (by omega)
        rw [bY_armB, bsize_armB]; push_cast; linarith
  · have := nonatom_le_Nb1K hD (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) (σ := σ) ha hc; linarith

theorem sum_rateGK_add (α k1 k2 k3 k4 σ : ℝ) (l : List Branch) :
    (l.map (fun c => rateGK α k1 k2 k3 k4 c + σ * bY c)).sum
      = (l.map (rateGK α k1 k2 k3 k4)).sum + σ * (l.map bY).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `bY(node cs) ≤ 1/(d + (d−1)·ym)` for capped children. -/
theorem bY_node_le_cap {D : ℕ} (hD1 : 1 ≤ D) (cs : List Branch) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D) :
    bY (Branch.node cs) ≤ 1 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) * (1 / (2 * (D : ℝ) - 1))) := by
  rw [bY_node]
  have := sumY_ge_ymin cs hcap
  have h0 : (0:ℝ) ≤ (cs.length : ℝ) * (1 / (2 * (D : ℝ) - 1)) := by
    have : (1:ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    apply mul_nonneg (Nat.cast_nonneg _); apply div_nonneg (by norm_num); linarith
  apply one_div_le_one_div_of_le (by positivity); linarith

/-- **Generic credited rate cell** (`K ≥ 2` children). -/
theorem rate_cell_genericK {D K : ℕ} (hD : 2 ≤ D) (hD23 : D ≤ 23) {α k1 k2 k3 k4 S0 ℓ umax unc ρm km : ℝ}
    (hS0 : 0 ≤ S0)
    (hℓ : Real.log (1 + S0 / ((K : ℝ) + 1)) - FSTAR ≤ ℓ)
    (hL : -((847797 / 110000000 + 2027323 / 5000000) / 2) + α + 1 / ((K : ℝ) + 1 + S0) ≤ unc)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      bjT j + α * (2 * (j : ℝ) + 1) + 1 / ((K : ℝ) + 1 + S0) * (3 / (4 * (j : ℝ) + 3)) ≤ unc)
    (hN : NbK (D : ℝ) k1 k2 k3 k4 (1 / ((K : ℝ) + 1 + S0)) ≤ unc)
    (hCu : -(847797 / 110000000) + 2 * α + 1 / ((K : ℝ) + 1 + S0) * (1 / 3) ≤ umax) (hu : unc ≤ umax)
    (hρ : ∀ cs : List Branch, cs.length = K → (∀ c ∈ cs, maxCh c + 1 ≤ D) → ρwit (Branch.node cs) ≤ ρm)
    (hkm : ∀ cs : List Branch, cs.length = K → kapF k1 k2 k3 k4 (Branch.node cs) = km)
    (hfin : ((K : ℝ) - 1) * umax + unc + ℓ - S0 / ((K : ℝ) + 1 + S0) + α + ρm + km ≤ 0)
    (cs : List Branch) (hlen : cs.length = K) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + kapF k1 k2 k3 k4 (Branch.node cs) + (cs.map (rateGK α k1 k2 k3 k4)).sum ≤ 0 := by
  set σ := 1 / ((K : ℝ) + 1 + S0) with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hd : (0:ℝ) < (K : ℝ) + 1 := by positivity
  have htan := log_tangent hd (sumY_nonneg cs) hS0
  have hsum := sum_le_of_one_gap (f := fun c => rateGK α k1 k2 k3 k4 c + σ * bY c) (g := umax)
    (δ := umax - unc) cs
    (fun c hc => by
      by_cases hC : c = cherry
      · subst hC; have := cherry_le_envK (σ := σ) (α := α) (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4)
        linarith
      · have := child_le_envK hσ0 hD hD23 hL hArm hN (hcap c hc) hC; linarith)
    (by obtain ⟨c, hc, hne⟩ := exists_ne_cherry_of_nonatom cs hna
        exact ⟨c, hc, by have := child_le_envK hσ0 hD hD23 hL hArm hN (hcap c hc) hne; linarith⟩)
  rw [sum_rateGK_add, hlen] at hsum
  have hρ' := hρ cs hlen hcap
  have hk' := hkm cs hlen
  rw [hlen, hk']
  have hsplit : ((cs.map bY).sum - S0) / ((K : ℝ) + 1 + S0)
      = σ * (cs.map bY).sum - S0 / ((K : ℝ) + 1 + S0) := by
    rw [hσ]; field_simp
  linarith

/-- **Generic credited rate cell, `K = 1`.** -/
theorem rate_cell_oneK {D : ℕ} (hD : 2 ≤ D) (hD23 : D ≤ 23) {α k1 k2 k3 k4 S0 ℓ u : ℝ} (hS0 : 0 ≤ S0)
    (hℓ : Real.log (1 + S0 / ((1 : ℝ) + 1)) - FSTAR ≤ ℓ)
    (hArm : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      1 / ((1 : ℝ) + 1 + S0) * (3 / (4 * (j : ℝ) + 3)) + 1 / (4 * (2 + 3 / (4 * (j : ℝ) + 3))) + bjT j
        + α * (2 * (j : ℝ) + 1) ≤ u)
    (hN : Nb1K (D : ℝ) k1 k2 k3 k4 (1 / ((1 : ℝ) + 1 + S0)) ≤ u)
    (hfin : u + ℓ - S0 / ((1 : ℝ) + 1 + S0) + 133 / 17061 - 1 / 12 + α + k1 ≤ 0)
    (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D)
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + kapF k1 k2 k3 k4 (Branch.node cs) + (cs.map (rateGK α k1 k2 k3 k4)).sum ≤ 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen
  have hC : c ≠ cherry := by rintro rfl; exact hna (Or.inr ⟨1, rfl⟩)
  have hL : c ≠ Branch.node [] := by rintro rfl; exact hna (Or.inl rfl)
  set σ := 1 / ((1 : ℝ) + 1 + S0) with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hw := child_le_env1K hσ0 hD hD23 hArm hN (hcap c (by simp)) hC hL
  have hy0 := bY_nonneg c
  have htan := log_tangent (d := (1:ℝ) + 1) (by norm_num) hy0 hS0
  have hAh := cherry_anchor_le_tight
  have hyv : bY (Branch.node [c]) = 1 / (2 + bY c) := by rw [bY_node]; simp; ring_nf
  have hk : kapF k1 k2 k3 k4 (Branch.node [c]) = k1 := by simp [kapF, bcc]
  rw [hk]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_cons,
    List.length_nil, zero_add]
  simp only [ρwit, bcc, List.length_cons, List.length_nil]
  rw [hyv]
  have hsplit : (bY c - S0) / ((1:ℝ) + 1 + S0) = σ * bY c - S0 / ((1:ℝ) + 1 + S0) := by
    rw [hσ]; field_simp
  norm_num at htan hsplit hℓ ⊢
  have hinv : (2 + bY c)⁻¹ = 4 * (1 / (4 * (2 + bY c))) := by field_simp
  have hS : S0 / (2 + S0) = S0 / (1 + 1 + S0) := by norm_num
  linarith [hinv, hS]

/-! ### Root bound through the verified knapsack. -/

/-- Lift of the per-child type bounds to a list: a list of types with the same length, sizes summing to at
    most the branch sizes, and weights dominating `f`. -/
theorem exists_types {D : ℕ} {tys : List (ℕ × ℤ)} {SC : ℝ} {f : Branch → ℝ}
    (htype : ∀ c, maxCh c + 1 ≤ D → ∃ p ∈ tys, p.1 ≤ bsize c ∧ f c ≤ (p.2 : ℝ) / SC) :
    ∀ L : List Branch, (∀ c ∈ L, maxCh c + 1 ≤ D) →
      ∃ ps : List (ℕ × ℤ), ps.length = L.length ∧ (∀ p ∈ ps, p ∈ tys) ∧
        (ps.map Prod.fst).sum ≤ bsizeList L ∧ (L.map f).sum ≤ ((ps.map Prod.snd).sum : ℝ) / SC
  | [], _ => ⟨[], rfl, by simp, by simp [bsizeList], by simp⟩
  | c :: L, h => by
      obtain ⟨p, hp, hp1, hp2⟩ := htype c (h c (by simp))
      obtain ⟨ps, h1, h2, h3, h4⟩ := exists_types htype L (fun x hx => h x (List.mem_cons_of_mem _ hx))
      refine ⟨p :: ps, by simp [h1], ?_, ?_, ?_⟩
      · intro q hq; rcases List.mem_cons.mp hq with rfl | hq'; exact hp; exact h2 q hq'
      · simp only [List.map_cons, List.sum_cons, bsizeList]; omega
      · simp only [List.map_cons, List.sum_cons, Int.cast_add]
        rw [add_div]; linarith

/-- **Root bound via the knapsack.**  If every capped child `c` has a type `p ∈ tys` with
    `p.1 ≤ |c|` and `bell c + σ y_c + α|c| ≤ p.2 / SC`, and some child is a non-atom whose own bound is
    `(3, VNI)`, then `log pi − (n−1)F* ≤ log t + 1/t − 1 + (VNI + row_{k−1}[N−3]) / SC − α N`. -/
theorem phiRoot_le_dp {D : ℕ} {tys : List (ℕ × ℤ)} {SC α t : ℝ} {VNI : ℤ} (hSC : 0 < SC) (ht : 0 < t)
    (cs : List Branch) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D)
    (htype : ∀ c, maxCh c + 1 ≤ D →
      ∃ p ∈ tys, p.1 ≤ bsize c ∧
        bell c + 1 / ((cs.length : ℝ) * t) * bY c + α * (bsize c : ℝ) ≤ (p.2 : ℝ) / SC)
    (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (hnaB : ∀ c, maxCh c + 1 ≤ D → ¬ IsAtom c →
      bell c + 1 / ((cs.length : ℝ) * t) * bY c + α * (bsize c : ℝ) ≤ (VNI : ℝ) / SC)
    (L : ℕ) (hNL : bsizeList cs < L + 3) :
    phiRoot cs ≤ Real.log t + 1 / t - 1
      + ((VNI : ℝ) + ((dpRow tys L (cs.length - 1)).getD (bsizeList cs - 3) NEGI : ℝ)) / SC
      - α * (bsizeList cs : ℝ) := by
  classical
  obtain ⟨c0, hc0, hnc0⟩ := hna
  have hcs : cs ≠ [] := List.ne_nil_of_mem hc0
  have htan := phiRoot_le_tangent cs hcs ht
  set σ := 1 / ((cs.length : ℝ) * t) with hσ
  set f : Branch → ℝ := fun c => bell c + σ * bY c + α * (bsize c : ℝ) with hf
  -- Σ bV = Σ f − α N
  have hsumf : (cs.map (bV σ)).sum = (cs.map f).sum - α * (bsizeList cs : ℝ) := by
    have : ∀ l : List Branch, (l.map (bV σ)).sum = (l.map f).sum - α * (bsizeList l : ℝ) := by
      intro l; induction l with
      | nil => simp [bsizeList]
      | cons a r ih =>
          simp only [List.map_cons, List.sum_cons, ih, bsizeList, Nat.cast_add, hf, bV]; ring
    exact this cs
  -- split off c0
  have hperm := List.perm_cons_erase hc0
  have hsum_perm : (cs.map f).sum = f c0 + ((cs.erase c0).map f).sum := by
    rw [(hperm.map f).sum_eq]; simp
  have hsize_perm : bsizeList cs = bsize c0 + bsizeList (cs.erase c0) := by
    rw [bsizeList_eq_sum, bsizeList_eq_sum, (hperm.map bsize).sum_eq]; simp
  have hlen_perm : (cs.erase c0).length = cs.length - 1 := List.length_erase_of_mem hc0
  have hc03 := three_le_bsize_of_nonatom hnc0
  have hf0 := hnaB c0 (hcap c0 hc0) hnc0
  obtain ⟨ps, hps1, hps2, hps3, hps4⟩ := exists_types (D := D) (tys := tys) (SC := SC) (f := f)
    (fun c hc => htype c hc) (cs.erase c0) (fun c hc => hcap c (List.mem_of_mem_erase hc))
  have hdp := dp_sound tys L ps hps2 (bsizeList cs - 3) (by omega) (by omega)
  rw [hps1, hlen_perm] at hdp
  have hdpR : ((ps.map Prod.snd).sum : ℝ) ≤ ((dpRow tys L (cs.length - 1)).getD (bsizeList cs - 3) NEGI : ℝ) := by
    exact_mod_cast hdp
  have hdiv : ((ps.map Prod.snd).sum : ℝ) / SC
      ≤ ((dpRow tys L (cs.length - 1)).getD (bsizeList cs - 3) NEGI : ℝ) / SC :=
    div_le_div_of_nonneg_right hdpR hSC.le
  rw [hsumf, hsum_perm] at htan
  rw [add_div]
  linarith

/-! ### Per-child types from the rate cell and the envelopes. -/

theorem htype_of {D : ℕ} (hD : 2 ≤ D) (hD23 : D ≤ 23) {α k1 k2 k3 k4 σ SC : ℝ}
    (hR : RateCellKap D α k1 k2 k3 k4) (hSC : 0 < SC) (hσ : 0 ≤ σ)
    {tys : List (ℕ × ℤ)} {VNI WL WC : ℤ} {WA : ℕ → ℤ}
    (hVN : NbK (D : ℝ) k1 k2 k3 k4 σ ≤ (VNI : ℝ) / SC)
    (hWL : -((847797 / 110000000 + 2027323 / 5000000) / 2) + σ + α ≤ (WL : ℝ) / SC)
    (hWC : -(847797 / 110000000) + σ * (1 / 3) + 2 * α ≤ (WC : ℝ) / SC)
    (hWA : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D →
      bjT j + σ * (3 / (4 * (j : ℝ) + 3)) + α * (2 * (j : ℝ) + 1) ≤ (WA j : ℝ) / SC)
    (hm3 : ((3 : ℕ), VNI) ∈ tys) (hm1 : ((1 : ℕ), WL) ∈ tys) (hm2 : ((2 : ℕ), WC) ∈ tys)
    (hmA : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ D → (2 * j + 1, WA j) ∈ tys) :
    (∀ c, maxCh c + 1 ≤ D → ∃ p ∈ tys, p.1 ≤ bsize c ∧
        bell c + σ * bY c + α * (bsize c : ℝ) ≤ (p.2 : ℝ) / SC) ∧
    (∀ c, maxCh c + 1 ≤ D → ¬ IsAtom c → bell c + σ * bY c + α * (bsize c : ℝ) ≤ (VNI : ℝ) / SC) := by
  have hnab : ∀ c, maxCh c + 1 ≤ D → ¬ IsAtom c →
      bell c + σ * bY c + α * (bsize c : ℝ) ≤ (VNI : ℝ) / SC := by
    intro c hc hna
    have h1 := bell_add_ρwit_le_rateKap hR c hc hna
    have h2 := nonatom_le_NbK hD (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) (σ := σ) hna hc
    linarith
  refine ⟨fun c hc => ?_, hnab⟩
  by_cases ha : IsAtom c
  · rcases ha with rfl | ⟨j, rfl⟩
    · refine ⟨(2, WC), hm2, by simp [bsize_cherry], ?_⟩
      rw [bell_cherry, bY_cherry, bsize_cherry]
      have := anchor_ge_tight; push_cast; linarith
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨(1, WL), hm1, by simp [bsize_armB], ?_⟩
        have hl : armB 0 = Branch.node [] := rfl
        rw [hl, bell_leaf, bY_leaf]
        have hs : bsize (Branch.node []) = 1 := by simp [bsize, bsizeList]
        rw [hs]; have := fstar_ge_tight; push_cast; linarith
      · have hjm := maxCh_armB_ge j
        refine ⟨(2 * j + 1, WA j), hmA j hj (by omega), by simp [bsize_armB], ?_⟩
        have hb := arm_bell_le_T j hj (by omega)
        have hA := hWA j hj (by omega)
        rw [bY_armB, bsize_armB]; push_cast; linarith
  · exact ⟨(3, VNI), hm3, three_le_bsize_of_nonatom ha, hnab c hc ha⟩

/-! ### Spiders with cherries, arm_5 and arm_4. -/

/-- `c` cherries, `a` arms of five cherries, `q` arms of four cherries. -/
def spiderC (c a q : ℕ) : List Branch := List.replicate c cherry ++ spiderB a q

theorem bsizeList_spiderC (c a q : ℕ) : bsizeList (spiderC c a q) = 2 * c + 11 * a + 9 * q := by
  rw [spiderC, bsizeList_append, bsizeList_replicate, bsizeList_spiderB, bsize_cherry]; ring

theorem phiRoot_spiderC (c a q : ℕ) :
    phiRoot (spiderC c a q) = (c : ℝ) * bell cherry + (q : ℝ) * bell (armB 4)
      + Real.log (1 + ((c : ℝ) * (1 / 3) + (a : ℝ) * (3 / 23) + (q : ℝ) * (3 / 19))
          / ((c : ℝ) + (a : ℝ) + (q : ℝ))) := by
  rw [phiRoot_eq]
  have hbell : ((spiderC c a q).map bell).sum = (c : ℝ) * bell cherry + (q : ℝ) * bell (armB 4) := by
    rw [spiderC, spiderB, List.map_append, List.sum_append, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, List.map_replicate, List.sum_replicate,
      List.map_replicate, List.sum_replicate, bell_arm5, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hY : ((spiderC c a q).map bY).sum
      = (c : ℝ) * (1 / 3) + (a : ℝ) * (3 / 23) + (q : ℝ) * (3 / 19) := by
    rw [spiderC, spiderB, List.map_append, List.sum_append, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, List.map_replicate, List.sum_replicate,
      List.map_replicate, List.sum_replicate, bY_cherry, bY_arm5, bY_arm4, nsmul_eq_mul, nsmul_eq_mul,
      nsmul_eq_mul]
    ring
  have hlen : ((spiderC c a q).length : ℝ) = (c : ℝ) + (a : ℝ) + (q : ℝ) := by
    rw [spiderC, spiderB, List.length_append, List.length_append, List.length_replicate,
      List.length_replicate, List.length_replicate]; push_cast; ring
  rw [hbell, hY, hlen]

theorem bell_arm4_ge_tight : (-22581 / 22000000 - 1 / 10000000 : ℝ) ≤ bell (armB 4) := by
  have h := eleven_bell_armB 4
  have hl := le_log_of_taylor (c := -11291 / 1000000) (a := 11291 / 1000000)
    (x := ((3 / 2 : ℝ) ^ 4 * ((4 * ((4:ℕ) : ℝ) + 3) / (3 * ((4:ℕ) : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * 4 + 1))
    (by positivity) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  linarith

theorem rho_len2_le {D : ℕ} (hD : 1 ≤ D) (cs : List Branch) (h : cs.length = 2)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D) :
    ρwit (Branch.node cs) ≤ (1 / (3 + 2 * (1 / (2 * (D : ℝ) - 1)))) / 32 := by
  have hy := bY_node_le_cap hD cs hcap
  rw [h] at hy; push_cast at hy
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [ρwit, bcc, List.length_cons, List.length_nil]
    have : (2:ℝ) + 1 + 2 * (1 / (2 * (D : ℝ) - 1)) = 3 + 2 * (1 / (2 * (D : ℝ) - 1)) := by ring
    rw [this] at hy
    linarith
  · simp at h

theorem rho_len3_le {D : ℕ} (hD : 1 ≤ D) (cs : List Branch) (h : cs.length = 3)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ D) :
    ρwit (Branch.node cs) ≤ (1 / (4 + 3 * (1 / (2 * (D : ℝ) - 1)))) / 384 := by
  have hy := bY_node_le_cap hD cs hcap
  rw [h] at hy; push_cast at hy
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp only [ρwit, bcc, List.length_cons, List.length_nil]
    have : (3:ℝ) + 1 + 3 * (1 / (2 * (D : ℝ) - 1)) = 4 + 3 * (1 / (2 * (D : ℝ) - 1)) := by ring
    rw [this] at hy
    linarith
  · simp at h

theorem kapF_node_len (k1 k2 k3 k4 : ℝ) (cs : List Branch) :
    kapF k1 k2 k3 k4 (Branch.node cs)
      = if cs.length = 0 then 0 else if cs.length = 1 then k1 else if cs.length = 2 then k2
        else if cs.length = 3 then k3 else k4 := by
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> simp [kapF, bcc]

end BGSCL
end R3Cert
