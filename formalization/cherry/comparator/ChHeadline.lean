/- Comparator challenge (imports only Mathlib, not LeanCherry): the upper bound for every tree.
   pi_lambda(T) = sum over the matchings M of T, the empty one included, of prod_{uv in M} lambda/(deg u deg v),
   with deg the degree in T (Mathlib's SimpleGraph.degree). Statement: for every finite tree on n vertices and
   lambda >= 1 + sqrt 5, pi_lambda(T) <= (1+lambda)(1+lambda/2)^((n-1)/2).
   Only Mathlib definitions are used besides the four transcribed ones below. -/
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
  MS l (fun v => (G.degree v : ℝ)) G.edgeFinset

theorem pi_lam_le_tree {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : ℝ} (hl : 1 + √5 ≤ l) (hG : G.IsTree) :
    piL l G ≤ (1 + l) * (1 + l / 2) ^ (((Fintype.card V : ℝ) - 1) / 2) := by
  sorry

end

end LeanCherry
