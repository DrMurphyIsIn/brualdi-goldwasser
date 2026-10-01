/- Comparator challenge (imports only Mathlib, not LeanCherry): lambda = 1, trees on at least 2 vertices:
   pi_1(T) = per L(T) / prod_v deg v, with L = D - A transcribed below (diagonal deg, -1 on edges, 0 elsewhere)
   and Mathlib's Matrix.permanent. -/
import Mathlib

namespace LeanCherry

universe u

noncomputable section

def IsGMg {α : Type*} (M : Finset (Sym2 α)) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

open Classical in
def wS {α : Type*} (δ : α → ℝ) (l : ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u w => l / (δ u * δ w), fun u w => by simp only [mul_comm]⟩

open Classical in
def MS {α : Type*} (l : ℝ) (δ : α → ℝ) (E : Finset (Sym2 α)) : ℝ :=
  ∑ M ∈ E.powerset, if IsGMg M then ∏ e ∈ M, wS δ l e else 0

def piL {V : Type u} [Fintype V] [DecidableEq V] (l : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  MS l (fun v => (G.degree v : ℝ)) G.edgeFinset

end

namespace R3Copy

/-- the Laplacian D - A over ℝ -/
noncomputable def lapl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ :=
  fun i j => if i = j then (G.degree i : ℝ) else if G.Adj i j then -1 else 0

end R3Copy

theorem pi_one_eq_permanent_tree {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsTree) (h2 : 2 ≤ Fintype.card V) :
    piL 1 G = (R3Copy.lapl G).permanent / ∏ v, (G.degree v : ℝ) := by
  sorry

end LeanCherry
