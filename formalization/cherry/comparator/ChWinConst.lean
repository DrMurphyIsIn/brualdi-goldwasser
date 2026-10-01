/- Comparator challenge helper (mirrors the module shape of `WinConst.lean`): eta = 1+sqrt5 - l, eps = 2(f* - f_C),
   ydag = (e^{f*}-1)/l, w = y_C - ydag, s1 = eps/w. -/
import ChWinArms
namespace LeanCherry
noncomputable section
open Br
def etaW (l : ℝ) : ℝ := 1 + √5 - l
def epsW (l : ℝ) : ℝ := 2 * (fstar l - fch l)
def ydag (l : ℝ) : ℝ := (Real.exp (fstar l) - 1) / l
def wW (l : ℝ) : ℝ := yC l - ydag l
def s1W (l : ℝ) : ℝ := epsW l / wW l
end
end LeanCherry
