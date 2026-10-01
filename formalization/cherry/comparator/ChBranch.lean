/- Comparator challenge, part 2: the cavity recursion with activity l (planted branch: d = #children + 1,
   R = sum of the children's messages), the branch ceiling for l >= 1 + sqrt 5 with its equality clause, and
   rho(l) = sup_b T_b^(1/|b|) = sqrt(1 + l/2). -/
import ChBr

namespace LeanCherry

namespace Br

noncomputable section

mutual
def msgl (l : ℝ) : Br → ℝ
  | .node cs => 1 / ((cs.length : ℝ) + 1 + l * sumYl l cs)
def sumYl (l : ℝ) : List Br → ℝ
  | [] => 0
  | c :: cs => msgl l c + sumYl l cs
end

mutual
def Tl (l : ℝ) : Br → ℝ
  | .node cs => prodTl l cs * (1 + l * sumYl l cs / ((cs.length : ℝ) + 1))
def prodTl (l : ℝ) : List Br → ℝ
  | [] => 1
  | c :: cs => Tl l c * prodTl l cs
end

/-- equality in the cherry-regime ceiling iff b is the cherry -/
theorem Tl_eq_cherry_iff (l : ℝ) (hl : 1 + √5 ≤ l) (b : Br) :
    Tl l b = (1 + l / 2) ^ ((size b : ℝ) / 2) ↔ b = .node [.node []] := by
  sorry

end

end Br

noncomputable section

/-- rho -/
theorem rho_eq {l : ℝ} (hl : 1 + √5 ≤ l) :
    sSup {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))} = √(1 + l / 2) := by
  sorry

theorem rho_isGreatest {l : ℝ} (hl : 1 + √5 ≤ l) :
    IsGreatest {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))} (√(1 + l / 2)) := by
  sorry

theorem rho_isLUB {l : ℝ} (hl : 1 + √5 ≤ l) :
    IsLUB {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))} (√(1 + l / 2)) := by
  sorry

end

end LeanCherry
