/- Comparator challenge, one-block part 2: the cavity recursion with activity l. The root of b with m
   children has d_b = m + 1; R_b = sum of the children's messages; T_b = (prod T_c)(1 + l R_b/d_b);
   y_b = 1/(d_b + l R_b). -/
import ChOneBlockBr

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

end

end Br

end LeanCherry
