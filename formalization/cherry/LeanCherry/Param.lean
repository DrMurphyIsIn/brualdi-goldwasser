/-
LeanCherry.Param -- the cavity recursion with the activity lam as a PARAMETER, and its lam-derivatives.

  Tl l (node cs) = (prod_c Tl l c) (1 + l R/d),   msgl l (node cs) = 1/(d + l R),   R = sum_c msgl l c,  d = #children + 1;
  Ml l b  = d/dl msgl l b = -(R + l R') msgl^2,   Dl l b = d/dl log Tl l b = sum_c Dl l c + (R + l R') msgl.

-/
import LeanCherry.Main

open Real

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

mutual
/-- derivative of msgl in l -/
def Ml (l : ℝ) : Br → ℝ
  | .node cs => -(sumYl l cs + l * sumMl l cs) * (1 / ((cs.length : ℝ) + 1 + l * sumYl l cs)) ^ 2
def sumMl (l : ℝ) : List Br → ℝ
  | [] => 0
  | c :: cs => Ml l c + sumMl l cs
end

mutual
/-- derivative of log Tl in l -/
def Dl (l : ℝ) : Br → ℝ
  | .node cs => sumDl l cs + (sumYl l cs + l * sumMl l cs) * (1 / ((cs.length : ℝ) + 1 + l * sumYl l cs))
def sumDl (l : ℝ) : List Br → ℝ
  | [] => 0
  | c :: cs => Dl l c + sumDl l cs
end

lemma msgl_node (l : ℝ) (cs : List Br) : msgl l (.node cs) = 1 / ((cs.length : ℝ) + 1 + l * sumYl l cs) := by
  rw [msgl]
lemma Tl_node (l : ℝ) (cs : List Br) :
    Tl l (.node cs) = prodTl l cs * (1 + l * sumYl l cs / ((cs.length : ℝ) + 1)) := by rw [Tl]
lemma Ml_node (l : ℝ) (cs : List Br) :
    Ml l (.node cs) = -(sumYl l cs + l * sumMl l cs) * (msgl l (.node cs)) ^ 2 := by rw [Ml, msgl_node]
lemma Dl_node (l : ℝ) (cs : List Br) :
    Dl l (.node cs) = sumDl l cs + (sumYl l cs + l * sumMl l cs) * msgl l (.node cs) := by rw [Dl, msgl_node]

mutual
lemma msgl_pos {l : ℝ} (hl : 0 ≤ l) : ∀ b : Br, 0 < msgl l b
  | .node cs => by
      have := sumYl_nonneg hl cs
      rw [msgl_node]
      have : 0 ≤ l * sumYl l cs := mul_nonneg hl this
      positivity
lemma sumYl_nonneg {l : ℝ} (hl : 0 ≤ l) : ∀ cs : List Br, 0 ≤ sumYl l cs
  | [] => by simp [sumYl]
  | c :: cs => by
      have := msgl_pos hl c; have := sumYl_nonneg hl cs
      simp only [sumYl]; linarith
end

lemma msgl_le_one {l : ℝ} (hl : 0 ≤ l) (b : Br) : msgl l b ≤ 1 := by
  cases b with
  | node cs =>
    rw [msgl_node]
    have := sumYl_nonneg hl cs
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ cs.length := by positivity
    nlinarith [mul_nonneg hl (sumYl_nonneg hl cs)]

mutual
lemma Tl_pos {l : ℝ} (hl : 0 ≤ l) : ∀ b : Br, 0 < Tl l b
  | .node cs => by
      have h1 := prodTl_pos hl cs
      have h2 := sumYl_nonneg hl cs
      rw [Tl_node]
      have : 0 ≤ l * sumYl l cs / ((cs.length : ℝ) + 1) := by positivity
      exact mul_pos h1 (by linarith)
lemma prodTl_pos {l : ℝ} (hl : 0 ≤ l) : ∀ cs : List Br, 0 < prodTl l cs
  | [] => by simp [prodTl]
  | c :: cs => by
      have := Tl_pos hl c; have := prodTl_pos hl cs
      simp only [prodTl]; positivity
end

/-! transfer to the fixed-activity recursion of LeanCherry.Tree at l = lam -/
mutual
lemma msgl_lam : ∀ b : Br, msgl lam b = msg b
  | .node cs => by rw [msgl_node, msg_node, sumYl_lam cs]
lemma sumYl_lam : ∀ cs : List Br, sumYl lam cs = sumY cs
  | [] => by simp [sumYl, sumY]
  | c :: cs => by simp only [sumYl, sumY]; rw [msgl_lam c, sumYl_lam cs]
end

mutual
lemma Tl_lam : ∀ b : Br, Tl lam b = T b
  | .node cs => by rw [Tl_node, sumYl_lam, prodTl_lam cs, T]
lemma prodTl_lam : ∀ cs : List Br, prodTl lam cs = prodT cs
  | [] => by simp [prodTl, prodT]
  | c :: cs => by simp only [prodTl, prodT]; rw [Tl_lam c, prodTl_lam cs]
end

end

end Br

end LeanCherry
