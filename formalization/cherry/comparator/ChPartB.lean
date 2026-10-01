/- Comparator challenge, part (B) definitions (imports Mathlib and the witness transcription only). The cherry
   (a vertex with one leaf child), the arm A_j (a root carrying j cherries, 2j+1 vertices), f_j = log T(A_j)/(2j+1),
   f* = sup_{j>=1} f_j (the best arm rate), and the two external inputs of part (B) as stated in `PartB.lean`
   (a witness and a best arm on [0.1, 1+sqrt5); the branch bound itself and a best arm on (0, 0.1]). -/
import ChWitness

namespace LeanCherry

namespace Br

/-- the cherry -/
def cherry : Br := .node [.node []]

end Br

noncomputable section

open Br

/-- the arm A_j -/
def armB (j : ℕ) : Br := .node (List.replicate j cherry)

/-- f_j -/
def fArm (l : ℝ) (j : ℕ) : ℝ := Real.log (Tl l (armB j)) / (2 * j + 1)

/-- f* = sup_j f_j -/
def fstar (l : ℝ) : ℝ := sSup {x | ∃ j : ℕ, 1 ≤ j ∧ x = fArm l j}

def PartB_WitnessInput : Prop :=
  ∀ l : ℝ, (1 / 10 : ℝ) ≤ l → l < 1 + √5 →
    (∃ (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ), Witness l (fstar l) A I h) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

def PartB_SmallInput : Prop :=
  ∀ l : ℝ, 0 < l → l ≤ 1 / 10 →
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧ ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l

end

end LeanCherry
