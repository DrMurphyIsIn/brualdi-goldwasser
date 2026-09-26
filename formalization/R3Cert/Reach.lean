/-
  The reachable-cavity predicate + the E0/E1 band classification -- PROMOTED to theorems.

  `E0_cavity_classification` / `E1_forbidden_band` in `Structure.lean` are stated over an ABSTRACT
  `Reach : ℝ → Prop`.  This file gives `Reach` a concrete inductive definition -- the DEC branch cavities
  `mu = 3 / t`, where a branch has `c` cherries and a list of child branches, degree `d = 1 + n_ch + c`, and
  `t = 3 d + c + 3 S = 3 + 3·n_ch + 4 c + 3 S` with `S` the sum of child cavities -- and proves E0
  (`mu ∈ {1} ∪ (0, 1/2)`) and E1 (`mu ∉ (1/3, 2/5]`) by structural induction, exactly the depth-free
  `lemma_proofs.prove_E0` / `prove_E1` arguments:

    * bare leaf `(c = 0, no children)` gives `t = 3`, `mu = 1`; every other branch gives `t > 6`, `mu < 1/2`;
    * the forbidden band is `t ∈ [15/2, 9)`; it is empty by shape: a leaf has `t = 3 + 4c ∈ {3,7,11,...}`
      (skips `[7.5,9)`); the chain `(1,0)` has `t = 6 + 3 nu` needing `nu ∈ [1/2,1)`, which E0 forbids on the
      child (a genuine induction); `(1, c≥1)` gives `t ≥ 10`; `n_ch ≥ 2` gives `t ≥ 9`.
-/
import Mathlib
import R3Cert.Structure

namespace R3Cert

open Real

/-- A DEC branch: `c` cherries at the root plus a list of child branches. -/
inductive Branch where
  | node (c : ℕ) (children : List Branch)

mutual
/-- Branch cavity `mu = 3 / (3 + 3·n_ch + 4 c + 3 S)`, `S` = sum of child cavities. -/
noncomputable def cav : Branch → ℝ
  | .node c ch => 3 / (3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch)
/-- Sum of child cavities. -/
noncomputable def cavSum : List Branch → ℝ
  | [] => 0
  | b :: rest => cav b + cavSum rest
end

mutual
theorem cav_pos (b : Branch) : 0 < cav b := by
  cases b with
  | node c ch =>
    have hS : 0 ≤ cavSum ch := cavSum_nonneg ch
    have h1 : (0 : ℝ) ≤ (ch.length : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (c : ℝ) := by positivity
    rw [cav]; exact div_pos (by norm_num) (by linarith [hS])
theorem cavSum_nonneg (l : List Branch) : 0 ≤ cavSum l := by
  cases l with
  | nil => simp [cavSum]
  | cons b rest => rw [cavSum]; have := cav_pos b; have := cavSum_nonneg rest; linarith
end

theorem cavSum_pos (l : List Branch) (hl : l ≠ []) : 0 < cavSum l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b rest => rw [cavSum]; have := cav_pos b; have := cavSum_nonneg rest; linarith

/-- Abbreviation for the branch denominator `t = 3 + 3·n_ch + 4 c + 3 S`. -/
theorem cav_eq (c : ℕ) (ch : List Branch) :
    cav (Branch.node c ch) = 3 / (3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch) := by
  rw [cav]

/-- **E0 (cavity classification), PROVED.**  Every branch cavity lies in `{1} ∪ (0, 1/2)`; it is `1` exactly for
    the bare leaf `(c = 0, no children)`, where `t = 3`.  Otherwise `t > 6` so `mu = 3/t < 1/2`. -/
theorem E0_holds (b : Branch) : cav b = 1 ∨ (0 < cav b ∧ cav b < 1 / 2) := by
  cases b with
  | node c ch =>
    have hS : 0 ≤ cavSum ch := cavSum_nonneg ch
    have hlen : (0 : ℝ) ≤ (ch.length : ℝ) := by positivity
    have hc : (0 : ℝ) ≤ (c : ℝ) := by positivity
    have hden : (0 : ℝ) < 3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch := by linarith [hS]
    by_cases hbare : c = 0 ∧ ch = []
    · left
      obtain ⟨hc0, hch0⟩ := hbare
      rw [cav_eq, hc0, hch0]; simp only [cavSum, List.length_nil, Nat.cast_zero]; norm_num
    · right
      have ht6 : (6 : ℝ) < 3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch := by
        by_cases hch : ch = []
        · have hc1 : c ≠ 0 := fun h => hbare ⟨h, hch⟩
          have hc1' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc1
          rw [hch]; simp only [cavSum, List.length_nil, Nat.cast_zero]; linarith
        · have hpos : 0 < cavSum ch := cavSum_pos ch hch
          have hlen1 : (1 : ℝ) ≤ (ch.length : ℝ) := by
            have : 1 ≤ ch.length := List.length_pos_of_ne_nil hch
            exact_mod_cast this
          linarith [hpos, hlen1, hc]
      rw [cav_eq]
      refine ⟨div_pos (by norm_num) hden, ?_⟩
      rw [div_lt_iff₀ hden]; linarith [ht6]

/-- **E1 (forbidden band), PROVED.**  No branch cavity lies in `(1/3, 2/5]` (equivalently no `t ∈ [15/2, 9)`).
    By shape: leaf `t = 3 + 4c` skips the band; chain `(1,0)` `t = 6 + 3·(child cavity)` needs the child cavity
    in `[1/2, 1)`, forbidden by E0 on the child; `(1, c≥1)` gives `t ≥ 10`; `n_ch ≥ 2` gives `t ≥ 9`. -/
theorem E1_holds (b : Branch) : ¬ (1 / 3 < cav b ∧ cav b ≤ 2 / 5) := by
  cases b with
  | node c ch =>
    rintro ⟨h1, h2⟩
    have hS : 0 ≤ cavSum ch := cavSum_nonneg ch
    have hlen : (0 : ℝ) ≤ (ch.length : ℝ) := by positivity
    have hc : (0 : ℝ) ≤ (c : ℝ) := by positivity
    have hden : (0 : ℝ) < 3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch := by linarith [hS]
    rw [cav_eq] at h1 h2
    rw [lt_div_iff₀ hden] at h1        -- 1/3 * t < 3   (so t < 9)
    rw [div_le_iff₀ hden] at h2        -- 3 ≤ 2/5 * t   (so t ≥ 15/2)
    by_cases hch : ch = []
    · -- leaf: t = 3 + 4c;  1/3*(3+4c) < 3 forces c ≤ 1;  3 ≤ 2/5*(3+4c) forces c ≥ 2.
      rw [hch] at h1 h2
      simp only [cavSum, List.length_nil, Nat.cast_zero] at h1 h2
      have hc_lt2 : (c : ℝ) < 2 := by nlinarith [h1]
      have hc_gt1 : (1 : ℝ) < (c : ℝ) := by nlinarith [h2]
      have : c < 2 := by exact_mod_cast hc_lt2
      have : 1 < c := by exact_mod_cast hc_gt1
      omega
    · obtain ⟨b1, rest, rfl⟩ := List.exists_cons_of_ne_nil hch
      by_cases hrest : rest = []
      · subst hrest
        by_cases hc0 : c = 0
        · -- chain (1,0):  t = 6 + 3·cav b1.  E0 on b1: cav b1 = 1 (→ t=9) or < 1/2 (→ t < 15/2).
          subst hc0
          simp only [cavSum, List.length_cons, List.length_nil, Nat.cast_zero, Nat.cast_one] at h1 h2
          rcases E0_holds b1 with hb1 | ⟨_, hb1lt⟩
          · rw [hb1] at h1; nlinarith [h1]
          · nlinarith [h2, hb1lt]
        · -- (1, c≥1):  t = 6 + 4c + 3·cav b1 ≥ 10 > 9, contradicting t < 9.
          have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc0
          have hb1pos : 0 < cav b1 := cav_pos b1
          simp only [cavSum, List.length_cons, List.length_nil, Nat.cast_zero, Nat.cast_one] at h1
          nlinarith [h1, hc1, hb1pos]
      · -- n_ch ≥ 2:  t = 3 + 3·n_ch + 4c + 3S ≥ 9 > t (< 9), contradiction.
        have hlen2 : (2 : ℝ) ≤ ((b1 :: rest).length : ℝ) := by
          have : 2 ≤ (b1 :: rest).length := by
            have : 1 ≤ rest.length := List.length_pos_of_ne_nil hrest
            simp only [List.length_cons]; omega
          exact_mod_cast this
        have hSpos : 0 ≤ cavSum (b1 :: rest) := cavSum_nonneg _
        nlinarith [h1, hlen2, hSpos, hc]

/-- The concrete reachable-cavity predicate: `mu` is the cavity of some DEC branch. -/
def Reachable (mu : ℝ) : Prop := ∃ b : Branch, cav b = mu

/-- **E0 as an instance of the abstract classification, on the concrete `Reachable`.** -/
theorem E0_cavity_classification_holds : E0_cavity_classification Reachable := by
  rintro mu ⟨b, rfl⟩; exact E0_holds b

/-- **E1 as an instance of the abstract forbidden-band statement, on the concrete `Reachable`.** -/
theorem E1_forbidden_band_holds : E1_forbidden_band Reachable := by
  rintro mu ⟨b, rfl⟩; exact E1_holds b

/-! ## The tree-induction assembly -- CONDITIONAL on a valid potential (the open crux isolated).

`general_induction.py`: the branch log-amplitude telescopes as `log Φ(node) = Σ_children log Φ + e_root`,
`e_root = log a(d,c) + log(1 + z·S)`, `d = n_ch+1+c`, `z = 3/(3d+c)`, `S = Σ child cavities`.  The conjecture
`Φ(T) ≤ 1` is the inductive statement `log Φ(B) ≤ 0` for every branch.  The naive induction (assume only
`log Φ_i ≤ 0`) OVERSHOOTS: `e_root` can be `> 0` and must be paid by the children's negative amplitudes, so the
step needs the QUANTITATIVE, cavity-dependent bound -- equivalently a POTENTIAL `P ≥ 0` with the per-vertex
inequality `e_root ≤ Σ_children P(m_c) − P(m_v)`.  This file makes the strong induction a machine-checked
theorem GIVEN such a `P`, and isolates its EXISTENCE as the open Brualdi–Goldwasser crux: the tightest
`P* = −Ψ` (Ψ the value function) has `P* ≥ 0` iff the conjecture (circular), no smooth `P` works (the marginal
tie), and the proven child families do not capture Ψ (the optimal child is non-monotone). -/

/-- `z(d,c) = 3/(3d+c)`, `d = n_ch + 1 + c`. -/
noncomputable def zc (c nch : ℕ) : ℝ := 3 / (3 * ((nch : ℝ) + 1 + (c : ℝ)) + (c : ℝ))

/-- `a(d,c) = (3/2)^c · (1 + c/(3d)) / rhoB^(1+2c)`, `d = n_ch + 1 + c`. -/
noncomputable def ac (c nch : ℕ) : ℝ :=
  (3 / 2) ^ c * (1 + (c : ℝ) / (3 * ((nch : ℝ) + 1 + (c : ℝ)))) / rhoB ^ (1 + 2 * c)

/-- The root increment `e_root = log a(d,c) + log(1 + z·S)`, `S = Σ child cavities`. -/
noncomputable def eroot (c : ℕ) (ch : List Branch) : ℝ :=
  Real.log (ac c ch.length) + Real.log (1 + zc c ch.length * cavSum ch)

mutual
/-- The branch log-amplitude `log Φ(B) = Σ_children log Φ + e_root`. -/
noncomputable def logPhi : Branch → ℝ
  | .node c ch => logPhiSum ch + eroot c ch
/-- Sum of child log-amplitudes. -/
noncomputable def logPhiSum : List Branch → ℝ
  | [] => 0
  | b :: rest => logPhi b + logPhiSum rest
end

/-- A **valid potential**: `P ≥ 0` and the per-vertex inequality `e_root(node) ≤ Σ_children P(cav child) −
    P(cav node)`.  `∃ P, ValidPotential P` is the OPEN Brualdi–Goldwasser crux. -/
def ValidPotential (P : ℝ → ℝ) : Prop :=
  (∀ m, 0 ≤ P m) ∧
    (∀ (c : ℕ) (ch : List Branch),
      eroot c ch ≤ (ch.map (fun b => P (cav b))).sum - P (cav (Branch.node c ch)))

mutual
/-- Strong-induction step (branch): `log Φ(B) ≤ −P(cav B)`, given a valid potential. -/
theorem logPhi_le_of_potential (P : ℝ → ℝ) (hP : ValidPotential P) (B : Branch) :
    logPhi B ≤ - P (cav B) := by
  cases B with
  | node c ch =>
    have hsum := logPhiSum_le_of_potential P hP ch
    have hstep := hP.2 c ch
    rw [logPhi]; linarith [hsum, hstep]
/-- Strong-induction step (child list): `Σ log Φ ≤ −Σ P(cav ·)`. -/
theorem logPhiSum_le_of_potential (P : ℝ → ℝ) (hP : ValidPotential P) (ch : List Branch) :
    logPhiSum ch ≤ - (ch.map (fun b => P (cav b))).sum := by
  cases ch with
  | nil => rw [logPhiSum]; simp
  | cons b rest =>
    have hb := logPhi_le_of_potential P hP b
    have hrest := logPhiSum_le_of_potential P hP rest
    rw [logPhiSum]; simp only [List.map_cons, List.sum_cons]; linarith [hb, hrest]
end

/-- **THE TREE-INDUCTION ASSEMBLY (conditional on the open crux).**  If a valid potential `P` exists, then
    every branch satisfies `log Φ(B) ≤ 0`, i.e. `Φ(B) ≤ 1` -- the whole Brualdi–Goldwasser conjecture -- by the
    strong induction `logPhi_le_of_potential` (`log Φ(B) ≤ −P(cav B) ≤ 0`).  So `Φ ≤ 1` reduces EXACTLY to
    `∃ P, ValidPotential P`, the open crux.  The induction is machine-checked; the potential's existence is not
    (and cannot be, by the circular/no-smooth/non-monotone obstructions in `general_induction.py`). -/
theorem phi_le_one_of_potential (P : ℝ → ℝ) (hP : ValidPotential P) (B : Branch) : logPhi B ≤ 0 := by
  have h1 := logPhi_le_of_potential P hP B
  have h2 := hP.1 (cav B)
  linarith

end R3Cert
