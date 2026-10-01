/- Comparator challenge: the witness framework (imports Mathlib and the one-block transcription of planted
   branches, the cavity recursion and M_n only). The deficit g(b) = |b| F - log T_b; the type (E, m) of a branch
   (multiset of exempt children, number of non-exempt children); a witness (lam > 0; an interval I with
   (0,1/2] ⊆ I ⊆ [0,1]; membership in A determined by the type, no exempt type with m >= 1; g >= 0 on A; h convex
   and bounded below on I, the leaf clause, and the Bellman inequality for every non-exempt type with |E| + m >= 1
   and every ybar in I (no ybar if m = 0)); and the witness theorem (a), (b), (c). -/
import ChOneBlockTl
import ChOneBlockGraph

open Finset Filter Topology

namespace LeanCherry

noncomputable section

open Classical

def rhoSet (l : ℝ) : Set ℝ := {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))}
def rhoB (l : ℝ) : ℝ := sSup (rhoSet l)

namespace Br

/-- g(b) = |b| F - log T_b -/
def gB (l F : ℝ) (b : Br) : ℝ := (size b : ℝ) * F - Real.log (Tl l b)

/-- children of the root lying in A, as a multiset -/
def exE (A : Set Br) (cs : List Br) : Multiset Br := ↑(cs.filter (fun c => decide (c ∈ A)))
/-- children of the root not in A -/
def nonE (A : Set Br) (cs : List Br) : List Br := cs.filter (fun c => decide (c ∉ A))

/-- the type (E, m) -/
def typeOf (A : Set Br) : Br → Multiset Br × ℕ
  | .node cs => (exE A cs, (nonE A cs).length)

/-- "a type whose branches are not exempt" -/
def TypeNonExempt (A : Set Br) (E : Multiset Br) (m : ℕ) : Prop := ∀ b, typeOf A b = (E, m) → b ∉ A

/-- the Bellman inequality, d = |E| + m + 1, R = sum_E y_a + m ybar, read right-to-left -/
def Bellman (l F : ℝ) (h : ℝ → ℝ) (E : Multiset Br) (m : ℕ) (ybar : ℝ) : Prop :=
  h (1 / ((E.card : ℝ) + m + 1 + l * ((E.map (msgl l)).sum + m * ybar))) ≤
    F + (E.map (gB l F)).sum + m * h ybar
      - Real.log (1 + l * ((E.map (msgl l)).sum + m * ybar) / ((E.card : ℝ) + m + 1))

end Br

open Br

/-- a witness -/
structure Witness (l F : ℝ) (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ) : Prop where
  lam_pos : 0 < l
  I_ord : I.OrdConnected
  I_lo : Set.Ioc (0 : ℝ) (1 / 2) ⊆ I
  I_hi : I ⊆ Set.Icc 0 1
  HA_type : ∀ b b' : Br, typeOf A b = typeOf A b' → (b ∈ A ↔ b' ∈ A)
  HA_m : ∀ b ∈ A, (typeOf A b).2 = 0
  H0 : ∀ a ∈ A, 0 ≤ gB l F a
  convex : ConvexOn ℝ I h
  bdd : BddBelow (h '' I)
  leaf : Br.node [] ∉ A → (1 : ℝ) ∈ I ∧ h 1 ≤ F
  bell : ∀ (E : Multiset Br) (m : ℕ), (∀ a ∈ E, a ∈ A) → 1 ≤ E.card + m → TypeNonExempt A E m →
    ∀ ybar : ℝ, (0 < m → ybar ∈ I) → Bellman l F h E m ybar

namespace Witness

variable {l F : ℝ} {A : Set Br} {I : Set ℝ} {h : ℝ → ℝ}

/-- the witness theorem (a) -/
theorem mt_main_a (W : Witness l F A I h) :
    (∀ y ∈ I, 0 ≤ h y) ∧ (∀ b, b ∉ A → h (msgl l b) ≤ gB l F b ∧ 0 ≤ h (msgl l b)) ∧ (∀ b ∈ A, 0 ≤ gB l F b) ∧
      ∀ b : Br, Tl l b ≤ Real.exp (F * size b) := by
  sorry

/-- the witness theorem (b) -/
theorem mt_main_b (W : Witness l F A I h) :
    (∀ n : ℕ, 1 ≤ n → Mn l n ≤ (1 + l) * Real.exp (F * ((n : ℝ) - 1))) ∧ rhoB l ≤ Real.exp F := by
  sorry

/-- the witness theorem (c) -/
theorem mt_main_c (W : Witness l F A I h) {bs : Br} (hbs : gB l F bs = 0) :
    rhoB l = Real.exp F ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (F * size bs * (((n - 1) / size bs : ℕ) : ℝ)) ≤ Mn l n ∧ Mn l n ≤ (1 + l) * Real.exp (F * ((n : ℝ) - 1)) := by
  sorry

end Witness

end

end LeanCherry
