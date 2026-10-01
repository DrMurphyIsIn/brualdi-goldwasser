/- Comparator challenge: the one-block formula.
   rho(l) = sup_b T_b^(1/|b|) over all finite planted branches; T_b^floor((n-1)/|b|) <= M_n <= (1+l) rho^(n-1)
   for every b and n >= 1; lim M_n^(1/n) = rho; and rho = sqrt(1 + l/2) for l >= 1 + sqrt 5. -/
import ChOneBlockTl
import ChOneBlockGraph

open Finset Filter Topology

namespace LeanCherry

noncomputable section

def rhoSet (l : ℝ) : Set ℝ := {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))}
def rhoB (l : ℝ) : ℝ := sSup (rhoSet l)

theorem Mn_ge_block {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) (b : Br) :
    Br.Tl l b ^ ((n - 1) / Br.size b) ≤ Mn l n := by
  sorry

theorem Mn_le_rho {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) : Mn l n ≤ (1 + l) * rhoB l ^ (n - 1) := by
  sorry

theorem Mn_tendsto_rho {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => Mn l n ^ (1 / (n : ℝ))) atTop (𝓝 (rhoB l)) := by
  sorry

theorem rhoB_eq_cherry {l : ℝ} (hl : 1 + √5 ≤ l) : rhoB l = √(1 + l / 2) := by
  sorry

theorem rhoSet_bdd {l : ℝ} (hl : 0 ≤ l) : BddAbove (rhoSet l) := by
  sorry

theorem rhoB_le {l : ℝ} (hl : 0 ≤ l) : rhoB l ≤ 1 + l := by
  sorry

theorem Br.Tl_le_pow {l : ℝ} (hl : 0 ≤ l) (b : Br) : Br.Tl l b ≤ (1 + l) ^ (Br.size b - 1) := by
  sorry

end

end LeanCherry
