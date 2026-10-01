/- Comparator challenge helper (mirrors the module shape of `WinArms.lean`): y_C = 1/(2+l), t = l/(2+l),
   s = sqrt(1+l/2), f_C = log s. -/
import ChPartB
namespace LeanCherry
noncomputable section
open Br
def yC (l : ℝ) : ℝ := 1 / (2 + l)
def tC (l : ℝ) : ℝ := l / (2 + l)
def sC (l : ℝ) : ℝ := √(1 + l / 2)
def fch (l : ℝ) : ℝ := Real.log (sC l)
end
end LeanCherry
