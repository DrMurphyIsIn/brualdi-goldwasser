/- Comparator NEGATIVE CONTROL, must be REJECTED: identical to ChGraph.lean except that the growth rate is
   the wrong value sqrt(1 + l/3). Imports only Mathlib. -/
import Mathlib

open Finset Filter Topology

namespace LeanCherry

universe u

noncomputable section

/-- a set of edges is a matching -/
def IsGMg {α : Type*} (M : Finset (Sym2 α)) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

open Classical in
/-- weight lambda / (deg u deg w) of the edge uw -/
def wS {α : Type*} (δ : α → ℝ) (l : ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u w => l / (δ u * δ w), fun u w => by simp only [mul_comm]⟩

open Classical in
/-- sum over matchings in E of the product of edge weights -/
def MS {α : Type*} (l : ℝ) (δ : α → ℝ) (E : Finset (Sym2 α)) : ℝ :=
  ∑ M ∈ E.powerset, if IsGMg M then ∏ e ∈ M, wS δ l e else 0

/-- pi_lambda with the true Mathlib degrees -/
def piL {V : Type u} [Fintype V] [DecidableEq V] (l : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  MS l (fun v => (G.degree v : ℝ)) G.edgeFinset

open Classical in
/-- M_n(lambda): max of pi_lambda over all trees on the vertex set Fin n; 0 if there is none -/
def Mn (l : ℝ) (n : ℕ) : ℝ :=
  if h : (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).Nonempty then
    (univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).sup' h (fun G => piL l G)
  else 0

/-- the upper bound is strict on every finite tree -/
theorem pi_lam_lt_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : ℝ} (hl : 1 + √5 ≤ l) (hG : G.IsTree) :
    piL l G < (1 + l) * (1 + l / 2) ^ (((Fintype.card V : ℝ) - 1) / 2) := by
  sorry

/-- upper bound on M_n -/
theorem Mn_le {l : ℝ} (hl : 1 + √5 ≤ l) {n : ℕ} (hn : 1 ≤ n) :
    Mn l n ≤ (1 + l) * (1 + l / 2) ^ (((n : ℝ) - 1) / 2) := by
  sorry

/-- lower bound on M_n, natural exponent floor((n-1)/2) -/
theorem Mn_ge {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) : (1 + l / 2) ^ ((n - 1) / 2) ≤ Mn l n := by
  sorry

/-- growth rate -/
theorem Mn_rate {l : ℝ} (hl : 1 + √5 ≤ l) :
    Tendsto (fun n : ℕ => Mn l n ^ (1 / (n : ℝ))) atTop (𝓝 (√(1 + l / 3))) := by
  sorry

end

end LeanCherry
