/-
LeanCherry.LemmaMTree -- the recursive monomer-density inequality on planted branches:  for lam >= 2 and every b,
   F(msgl lam b) <= s_b := |b| alpha - lam * Dl lam b    (in particular  lam * Dl lam b <= |b| alpha).
-/
import LeanCherry.LemmaM

open Real

namespace LeanCherry

namespace Br

noncomputable section

variable {l : ℝ}

/-- s_b = |b| alpha - l * (d/dl) log T_b  ( = |b| alpha - E[#dimers] ) -/
def sl (l : ℝ) (b : Br) : ℝ := (size b : ℝ) * alpha l - l * Dl l b

def sumSl (l : ℝ) : List Br → ℝ
  | [] => 0
  | c :: cs => sl l c + sumSl l cs

/-- s summed over the children -/
def smOf (l : ℝ) : Br → ℝ
  | .node cs => sumSl l cs

lemma sumSl_eq (l : ℝ) : ∀ cs : List Br, sumSl l cs = (sizeL cs : ℝ) * alpha l - l * sumDl l cs
  | [] => by simp [sumSl, sizeL, sumDl]
  | c :: cs => by
      simp only [sumSl, sizeL, sumDl, sumSl_eq l cs, sl]; push_cast; ring

lemma sl_node (l : ℝ) (cs : List Br) :
    sl l (.node cs) = alpha l + sumSl l cs - msgl l (.node cs) * (l * (sumYl l cs + l * sumMl l cs)) := by
  rw [sumSl_eq]; unfold sl; rw [Dl_node]; simp only [size]; push_cast; ring

lemma child_id (l : ℝ) (b : Br) :
    msgl l b + l * Ml l b = msgl l b * (1 - alpha l - smOf l b + sl l b) := by
  cases b with
  | node gs =>
    have h := sl_node l gs
    rw [Ml_node]; simp only [smOf]
    have e : msgl l (.node gs) * (l * (sumYl l gs + l * sumMl l gs)) = alpha l + sumSl l gs - sl l (.node gs) := by
      linarith
    have : l * (-(sumYl l gs + l * sumMl l gs) * msgl l (.node gs) ^ 2)
        = - msgl l (.node gs) * (msgl l (.node gs) * (l * (sumYl l gs + l * sumMl l gs))) := by ring
    rw [this, e]; ring

/-! list bookkeeping -/
lemma sum_map_le' {β : Type*} {f g : β → ℝ} : ∀ cs : List β, (∀ c ∈ cs, f c ≤ g c) →
    (cs.map f).sum ≤ (cs.map g).sum
  | [], _ => by simp
  | c :: cs, h => by
      simp only [List.map_cons, List.sum_cons]
      have := h c List.mem_cons_self
      have := sum_map_le' cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
      linarith

lemma sum_lin {β : Type*} (f g : β → ℝ) (k : ℝ) : ∀ cs : List β,
    (cs.map f).sum - k * (cs.map g).sum = (cs.map (fun c => f c - k * g c)).sum
  | [] => by simp
  | c :: cs => by simp only [List.map_cons, List.sum_cons, ← sum_lin f g k cs]; ring

lemma sumYl_map (l : ℝ) : ∀ cs : List Br, sumYl l cs = (cs.map (msgl l)).sum
  | [] => by simp [sumYl]
  | c :: cs => by simp only [sumYl, List.map_cons, List.sum_cons, sumYl_map l cs]

lemma sumSl_map (l : ℝ) : ∀ cs : List Br, sumSl l cs = (cs.map (sl l)).sum
  | [] => by simp [sumSl]
  | c :: cs => by simp only [sumSl, List.map_cons, List.sum_cons, sumSl_map l cs]

lemma sumYM_map (l : ℝ) : ∀ cs : List Br,
    sumYl l cs + l * sumMl l cs = (cs.map (fun c => msgl l c + l * Ml l c)).sum
  | [] => by simp [sumYl, sumMl]
  | c :: cs => by
      simp only [sumYl, sumMl, List.map_cons, List.sum_cons, ← sumYM_map l cs]; ring

/-- the invariant -/
def Good3 (l : ℝ) (b : Br) : Prop := Fl l (msgl l b) ≤ sl l b ∧ 0 ≤ smOf l b

lemma good3_node (hl : 2 ≤ l) (cs : List Br) (h : ∀ c ∈ cs, Good3 l c) : Good3 l (.node cs) := by
  have hl0 : 0 < l := by linarith
  have hs0 : ∀ c ∈ cs, 0 ≤ sl l c := fun c hc => le_trans (Fl_nonneg l _) (h c hc).1
  refine ⟨?_, ?_⟩
  swap
  · -- smOf (node cs) = sum of s over children >= 0
    simp only [smOf]; rw [sumSl_map]
    have := sum_map_le' (f := fun _ => (0:ℝ)) (g := sl l) cs hs0
    simpa using this
  -- the main inequality
  set ys := cs.map (msgl l) with hys
  have hy : ∀ y ∈ ys, 0 ≤ y ∧ y ≤ 1 := by
    intro y hy'
    rw [hys, List.mem_map] at hy'
    obtain ⟨c, _, rfl⟩ := hy'
    exact ⟨(msgl_pos hl0.le c).le, msgl_le_one hl0.le c⟩
  have hone := onestep hl ys hy
  have hlen : (ys.length : ℝ) = (cs.length : ℝ) := by rw [hys, List.length_map]
  have hY : ys.sum = sumYl l cs := by rw [hys, sumYl_map]
  have hmsg : msgl l (.node cs) = 1 / ((ys.length : ℝ) + 1 + l * ys.sum) := by rw [msgl_node, hlen, hY]
  rw [hmsg]
  refine le_trans hone ?_
  -- rewrite the y-list sums as Br-list sums
  have e1 : (ys.map (Fl l)).sum = (cs.map (fun c => Fl l (msgl l c))).sum := by
    rw [hys, List.map_map]; rfl
  have e2 : (ys.map (fun y => y * (Fl l y + 1 - alpha l))).sum
      = (cs.map (fun c => msgl l c * (Fl l (msgl l c) + 1 - alpha l))).sum := by
    rw [hys, List.map_map]; rfl
  rw [e1, e2]
  set x := 1 / ((ys.length : ℝ) + 1 + l * ys.sum) with hx
  have hD : 0 < (ys.length : ℝ) + 1 + l * ys.sum := by
    have : 0 ≤ ys.sum := by rw [hY]; exact sumYl_nonneg hl0.le cs
    positivity
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  -- RHS: s_node = alpha + sum s - x * l * sum y (1 - alpha - sm + s)
  have hnode : sl l (.node cs) = alpha l + (cs.map (sl l)).sum
      - x * (l * (cs.map (fun c => msgl l c * (1 - alpha l - smOf l c + sl l c))).sum) := by
    rw [sl_node, sumSl_map, sumYM_map, hmsg]
    have : (cs.map (fun c => msgl l c + l * Ml l c)).sum
        = (cs.map (fun c => msgl l c * (1 - alpha l - smOf l c + sl l c))).sum := by
      congr 1; apply List.map_congr_left; intro c _; exact child_id l c
    rw [this]
  rw [hnode]
  -- per-child comparison
  have key : (cs.map (fun c => Fl l (msgl l c) - x * l * (msgl l c * (Fl l (msgl l c) + 1 - alpha l)))).sum
      ≤ (cs.map (fun c => sl l c - x * l * (msgl l c * (1 - alpha l - smOf l c + sl l c)))).sum := by
    apply sum_map_le'
    intro c hc
    obtain ⟨hF, hsm⟩ := h c hc
    have hyc := msgl_pos hl0.le c
    -- x * l * y_c <= 1
    have hyle : msgl l c ≤ ys.sum := by
      have := elem_le_sum (w := fun y => y) ys (fun z hz => (hy z hz).1) (msgl l c)
        (by rw [hys]; exact List.mem_map_of_mem hc)
      simpa using this
    have hxl : x * l * msgl l c ≤ 1 := by
      rw [hx, div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_one hD]
      have : (0:ℝ) ≤ ys.length := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hyle hl0.le]
    have h1 : 0 ≤ (sl l c - Fl l (msgl l c)) * (1 - x * l * msgl l c) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ x * l * msgl l c * smOf l c := by
      have : 0 ≤ x * l * msgl l c := by positivity
      exact mul_nonneg this hsm
    nlinarith
  have lhs : alpha l + (cs.map (fun c => Fl l (msgl l c))).sum
      - x * (l * (cs.map (fun c => msgl l c * (Fl l (msgl l c) + 1 - alpha l))).sum)
      = alpha l + (cs.map (fun c => Fl l (msgl l c) - x * l * (msgl l c * (Fl l (msgl l c) + 1 - alpha l)))).sum := by
    rw [← sum_lin]; ring
  have rhs : alpha l + (cs.map (sl l)).sum
      - x * (l * (cs.map (fun c => msgl l c * (1 - alpha l - smOf l c + sl l c))).sum)
      = alpha l + (cs.map (fun c => sl l c - x * l * (msgl l c * (1 - alpha l - smOf l c + sl l c)))).sum := by
    rw [← sum_lin]; ring
  rw [lhs, rhs]; linarith

mutual
theorem good3_all (hl : 2 ≤ l) : ∀ b : Br, Good3 l b
  | .node cs => good3_node hl cs (good3_list hl cs)
theorem good3_list (hl : 2 ≤ l) : ∀ cs : List Br, ∀ c ∈ cs, Good3 l c
  | [] => fun c hc => by simp at hc
  | d :: cs => fun c hc =>
      (List.mem_cons.mp hc).elim (fun e => e ▸ good3_all hl d) (fun h' => good3_list hl cs c h')
end

/-- The recursive monomer-density inequality: for l >= 2, l * (d/dl) log T_b <= |b| alpha(l), i.e. E[#dimers] <= |b| l/(2(2+l)). -/
theorem lemmaM (hl : 2 ≤ l) (b : Br) : l * Dl l b ≤ (size b : ℝ) * alpha l := by
  have h := (good3_all hl b).1
  have := Fl_nonneg l (msgl l b)
  unfold sl at h; linarith

end

end Br

end LeanCherry
