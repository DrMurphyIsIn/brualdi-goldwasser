/- Comparator challenge, one-block part 3 (imports only Mathlib): pi_lambda(T) = sum over the matchings M
   (the empty one included) of prod_{uv in M} l/(deg u deg v), true degrees; M_n(l) = max of pi_lambda(T) over the
   trees on Fin n, 0 if there is none. -/
import Mathlib

open Finset

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

open Classical in
def Mn (l : ℝ) (n : ℕ) : ℝ :=
  if h : (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).Nonempty then
    (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).sup' h (fun G => piL l G)
  else 0

end

end LeanCherry
