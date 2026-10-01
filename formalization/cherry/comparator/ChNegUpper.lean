/- Comparator NEGATIVE CONTROL, must be REJECTED: identical to ChOneBlock.lean except that the upper bound
   has the exponent n instead of n - 1 (weaker, and true, but not the stated theorem). -/
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

theorem Mn_le_rho {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) : Mn l n ≤ (1 + l) * rhoB l ^ (n) := by
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
