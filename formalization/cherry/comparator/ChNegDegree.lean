/- Comparator NEGATIVE CONTROL, must be REJECTED: identical to ChHeadline.lean except that piL uses the
   degree + 1 (a planted-degree bug). Imports only Mathlib. -/
import Mathlib

namespace LeanCherry

universe u

noncomputable section

/-- a set of edges is a matching: two distinct edges have no common vertex -/
def IsGMg {α : Type*} (M : Finset (Sym2 α)) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

open Classical in
/-- weight of the edge uv: lambda / (deg u * deg w) -/
def wS {α : Type*} (δ : α → ℝ) (l : ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u w => l / (δ u * δ w), fun u w => by simp only [mul_comm]⟩

open Classical in
/-- sum over all subsets of E that are matchings of the product of edge weights -/
def MS {α : Type*} (l : ℝ) (δ : α → ℝ) (E : Finset (Sym2 α)) : ℝ :=
  ∑ M ∈ E.powerset, if IsGMg M then ∏ e ∈ M, wS δ l e else 0

/-- pi_lambda of a finite simple graph, with its true (Mathlib) degrees -/
def piL {V : Type u} [Fintype V] [DecidableEq V] (l : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  MS l (fun v => (G.degree v : ℝ) + 1) G.edgeFinset

theorem pi_lam_le_tree {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : ℝ} (hl : 1 + √5 ≤ l) (hG : G.IsTree) :
    piL l G ≤ (1 + l) * (1 + l / 2) ^ (((Fintype.card V : ℝ) - 1) / 2) := by
  sorry

end

end LeanCherry
