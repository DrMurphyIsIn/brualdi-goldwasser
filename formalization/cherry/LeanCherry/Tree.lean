/-
LeanCherry.Tree -- planted branches and the cavity recursion at lam = lam_c.

  T(leaf) = 1, msg(leaf) = 1;  T(node cs) = (prod_c T c) * (1 + lam R/d),  msg(node cs) = 1/(d + lam R),
  R = sum_c msg c,  d = #children + 1 (the planted root's phantom parent edge counts in d).
  ell b := log (T b) - size b * L.

-/
import LeanCherry.Zero

open Real

namespace LeanCherry

/-- planted branch (rose tree) -/
inductive Br where
  | node : List Br → Br

namespace Br

mutual
/-- number of vertices -/
def size : Br → ℕ
  | .node cs => sizeL cs + 1
def sizeL : List Br → ℕ
  | [] => 0
  | c :: cs => size c + sizeL cs
end

noncomputable section

mutual
/-- the weighted matching sum T_b(lam_c) via the cavity recursion -/
def T : Br → ℝ
  | .node cs => prodT cs * (1 + lam * sumY cs / ((cs.length : ℝ) + 1))
def prodT : List Br → ℝ
  | [] => 1
  | c :: cs => T c * prodT cs
/-- the cavity message y_b = 1/(d + lam R) -/
def msg : Br → ℝ
  | .node cs => 1 / ((cs.length : ℝ) + 1 + lam * sumY cs)
def sumY : List Br → ℝ
  | [] => 0
  | c :: cs => msg c + sumY cs
end

mutual
lemma msg_pos : ∀ b : Br, 0 < msg b
  | .node cs => by
      have := sumY_nonneg cs
      unfold msg
      have : 0 ≤ lam * sumY cs := mul_nonneg lam_pos.le this
      positivity
lemma sumY_nonneg : ∀ cs : List Br, 0 ≤ sumY cs
  | [] => by simp [sumY]
  | c :: cs => by
      have := msg_pos c; have := sumY_nonneg cs
      simp only [sumY]; linarith
end

mutual
lemma T_pos : ∀ b : Br, 0 < T b
  | .node cs => by
      have h1 := prodT_pos cs
      have h2 := sumY_nonneg cs
      unfold T
      have : 0 ≤ lam * sumY cs / ((cs.length : ℝ) + 1) := by
        have := lam_pos; positivity
      exact mul_pos h1 (by linarith)
lemma prodT_pos : ∀ cs : List Br, 0 < prodT cs
  | [] => by simp [prodT]
  | c :: cs => by
      have := T_pos c; have := prodT_pos cs
      simp only [prodT]; positivity
end

/-- ell b = log T b - |b| L -/
def ell (b : Br) : ℝ := Real.log (T b) - (size b : ℝ) * L

/-- sum of ell over a list -/
def sumEll : List Br → ℝ
  | [] => 0
  | c :: cs => ell c + sumEll cs

lemma log_prodT : ∀ cs : List Br, Real.log (prodT cs) = sumEll cs + (sizeL cs : ℝ) * L
  | [] => by simp [prodT, sumEll, sizeL]
  | c :: cs => by
      simp only [prodT, sumEll, sizeL]
      rw [Real.log_mul (T_pos c).ne' (prodT_pos cs).ne', log_prodT cs]
      unfold ell; push_cast; ring

/-- the ell recursion -/
lemma ell_node (cs : List Br) :
    ell (.node cs) = sumEll cs + Real.log (1 + lam * sumY cs / ((cs.length : ℝ) + 1)) - L := by
  have hpos : 0 < 1 + lam * sumY cs / ((cs.length : ℝ) + 1) := by
    have := sumY_nonneg cs; have := lam_pos
    have : 0 ≤ lam * sumY cs / ((cs.length : ℝ) + 1) := by positivity
    linarith
  unfold ell
  rw [show T (.node cs) = prodT cs * (1 + lam * sumY cs / ((cs.length : ℝ) + 1)) by rw [T]]
  rw [Real.log_mul (prodT_pos cs).ne' hpos.ne', log_prodT cs]
  simp only [size]; push_cast; ring

lemma msg_node (cs : List Br) : msg (.node cs) = 1 / ((cs.length : ℝ) + 1 + lam * sumY cs) := by
  rw [msg]

lemma ell_leaf : ell (.node []) = -L := by
  rw [ell_node]; simp [sumEll, sumY]

lemma msg_leaf : msg (.node []) = 1 := by rw [msg_node]; simp [sumY]

end

end Br

end LeanCherry
