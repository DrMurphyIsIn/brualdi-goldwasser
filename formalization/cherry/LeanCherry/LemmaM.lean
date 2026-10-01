/-
LeanCherry.LemmaM -- the recursive monomer-density inequality for lam >= 2.

  alpha = lam/(2(2+lam)),  y_ch = 1/(2+lam),  c = lam/(2(1+lam)),  F(y) = max 0 (c (y - y_ch)),
  s_b = |b| alpha - lam * Dl lam b   ( = |b| alpha - E[#dimers] ),   invariant  F(msg b) <= s_b.

The one-step inequality reduces to two per-child linear inequalities I1, I2 (closed forms below).
-/
import LeanCherry.Deriv

open Real

namespace LeanCherry

noncomputable section

def alpha (l : ℝ) : ℝ := l / (2 * (2 + l))
def ycl (l : ℝ) : ℝ := 1 / (2 + l)
def cl (l : ℝ) : ℝ := l / (2 * (1 + l))
def Fl (l y : ℝ) : ℝ := max 0 (cl l * (y - ycl l))
/-- per-child diagonal term tau(y) = alpha w + F + F w - q, w = 1 + l y, q = l y (F + 1 - alpha) -/
def tau (l y : ℝ) : ℝ := alpha l * (1 + l * y) + Fl l y + Fl l y * (1 + l * y) - l * y * (Fl l y + 1 - alpha l)

section scalar
variable {l : ℝ}

lemma Fl_nonneg (l y : ℝ) : 0 ≤ Fl l y := le_max_left _ _

lemma cl_pos (hl : 0 < l) : 0 < cl l := by unfold cl; positivity
lemma ycl_pos (hl : 0 ≤ l) : 0 < ycl l := by unfold ycl; positivity
lemma alpha_nonneg (hl : 0 ≤ l) : 0 ≤ alpha l := by unfold alpha; positivity

lemma Fl_of_le (hl : 0 < l) {y : ℝ} (h : y ≤ ycl l) : Fl l y = 0 := by
  unfold Fl; apply max_eq_left
  exact mul_nonpos_of_nonneg_of_nonpos (cl_pos hl).le (by linarith)
lemma Fl_of_ge (hl : 0 < l) {y : ℝ} (h : ycl l ≤ y) : Fl l y = cl l * (y - ycl l) := by
  unfold Fl; apply max_eq_right
  exact mul_nonneg (cl_pos hl).le (by linarith)

lemma c_one_sub (hl : 0 ≤ l) : cl l * (1 - ycl l) = alpha l := by
  unfold cl ycl alpha
  have h1 : (0:ℝ) < 1 + l := by linarith
  have h2 : (0:ℝ) < 2 + l := by linarith
  field_simp; ring

lemma ycl_le (hl : 0 ≤ l) : ycl l ≤ 1 := by
  unfold ycl; rw [div_le_one (by linarith)]; linarith

lemma Fl_one (hl : 0 < l) : Fl l 1 = alpha l := by
  rw [Fl_of_ge hl (ycl_le hl.le), c_one_sub hl.le]

lemma Fl_le_alpha (hl : 0 < l) {y : ℝ} (hy : y ≤ 1) : Fl l y ≤ alpha l := by
  rcases le_total y (ycl l) with h | h
  · rw [Fl_of_le hl h]; exact alpha_nonneg hl.le
  · rw [Fl_of_ge hl h, ← c_one_sub hl.le]
    exact mul_le_mul_of_nonneg_left (by linarith) (cl_pos hl).le

/-- I1: tau(y) >= - c y_ch (1 + l y), for 0 <= y <= 1 -/
lemma I1 (hl : 2 ≤ l) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -(cl l * ycl l * (1 + l * y)) ≤ tau l y := by
  have hl0 : 0 < l := by linarith
  have h1 : (0:ℝ) < 1 + l := by linarith
  have h2 : (0:ℝ) < 2 + l := by linarith
  rcases le_total y (ycl l) with h | h
  · have key : tau l y + cl l * ycl l * (1 + l * y) = l * ((2 + l) - y * (4 + 3 * l)) / (2 * (2 + l) * (1 + l)) := by
      unfold tau; rw [Fl_of_le hl0 h]; unfold alpha ycl cl; field_simp; ring
    have hy' : y * (2 + l) ≤ 1 := by
      have := h; unfold ycl at this; rwa [le_div_iff₀ h2] at this
    have hnum : 0 ≤ (2 + l) - y * (4 + 3 * l) := by
      have : (2 + l) * ((2 + l) - y * (4 + 3 * l)) ≥ 0 := by
        nlinarith [mul_le_mul_of_nonneg_right hy' (by linarith : (0:ℝ) ≤ 4 + 3 * l)]
      nlinarith
    have : 0 ≤ l * ((2 + l) - y * (4 + 3 * l)) / (2 * (2 + l) * (1 + l)) := by positivity
    linarith
  · have key : tau l y + cl l * ycl l * (1 + l * y) = l ^ 2 * (1 - y) / (2 * (2 + l) * (1 + l)) := by
      unfold tau; rw [Fl_of_ge hl0 h]; unfold alpha ycl cl; field_simp; ring
    have : 0 ≤ l ^ 2 * (1 - y) / (2 * (2 + l) * (1 + l)) := by
      apply div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    linarith

/-- I2: tau(y) + F(y) >= 0, for 0 <= y <= 1 and l >= 2 -/
lemma I2 (hl : 2 ≤ l) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ tau l y + Fl l y := by
  have hl0 : 0 < l := by linarith
  have h1 : (0:ℝ) < 1 + l := by linarith
  have h2 : (0:ℝ) < 2 + l := by linarith
  rcases le_total y (ycl l) with h | h
  · have key : tau l y + Fl l y = l * (1 - 4 * y) / (2 * (2 + l)) := by
      unfold tau; rw [Fl_of_le hl0 h]; unfold alpha; field_simp; ring
    have hy' : y * (2 + l) ≤ 1 := by
      have := h; unfold ycl at this; rwa [le_div_iff₀ h2] at this
    have : 0 ≤ 1 - 4 * y := by nlinarith
    rw [key]; positivity
  · have key : tau l y + Fl l y = l * (l - 2) * (1 - y) / (2 * (2 + l) * (1 + l)) := by
      unfold tau; rw [Fl_of_ge hl0 h]; unfold alpha ycl cl; field_simp; ring
    rw [key]
    apply div_nonneg (mul_nonneg (mul_nonneg hl0.le (by linarith)) (by linarith)) (by positivity)

end scalar

section lists
variable {l : ℝ}

lemma sum_map_le {f g : ℝ → ℝ} : ∀ ys : List ℝ, (∀ y ∈ ys, f y ≤ g y) → (ys.map f).sum ≤ (ys.map g).sum
  | [], _ => by simp
  | y :: ys, h => by
      simp only [List.map_cons, List.sum_cons]
      have := h y List.mem_cons_self
      have := sum_map_le ys (fun z hz => h z (List.mem_cons_of_mem _ hz))
      linarith

lemma sum_w (l : ℝ) : ∀ ys : List ℝ, (ys.map (fun y => 1 + l * y)).sum = (ys.length : ℝ) + l * ys.sum
  | [] => by simp
  | y :: ys => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, sum_w l ys]; push_cast; ring

lemma sum_lin_c (k : ℝ) (w : ℝ → ℝ) : ∀ ys : List ℝ, (ys.map (fun y => -(k * w y))).sum = -(k * (ys.map w).sum)
  | [] => by simp
  | y :: ys => by simp only [List.map_cons, List.sum_cons, sum_lin_c k w ys]; ring

lemma elem_le_sum {w : ℝ → ℝ} : ∀ ys : List ℝ, (∀ z ∈ ys, 0 ≤ w z) → ∀ y ∈ ys, w y ≤ (ys.map w).sum
  | [], _, y, hy => by simp at hy
  | z :: ys, h, y, hy => by
      simp only [List.map_cons, List.sum_cons]
      have hz := h z List.mem_cons_self
      have hrest : 0 ≤ (ys.map w).sum := by
        have := sum_map_le (f := fun _ => (0:ℝ)) (g := w) ys (fun x hx => h x (List.mem_cons_of_mem _ hx))
        simpa using this
      rcases List.mem_cons.mp hy with rfl | hy'
      · linarith
      · have := elem_le_sum ys (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy'; linarith

lemma elem_plus_le_sum {w : ℝ → ℝ} : ∀ ys : List ℝ, (∀ z ∈ ys, 1 ≤ w z) → ∀ y ∈ ys,
    w y + ((ys.length : ℝ) - 1) ≤ (ys.map w).sum
  | [], _, y, hy => by simp at hy
  | z :: ys, h, y, hy => by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      have hz := h z List.mem_cons_self
      have hlen : (ys.length : ℝ) ≤ (ys.map w).sum := by
        have := sum_map_le (f := fun _ => (1:ℝ)) (g := w) ys (fun x hx => h x (List.mem_cons_of_mem _ hx))
        simpa using this
      rcases List.mem_cons.mp hy with rfl | hy'
      · linarith
      · have := elem_plus_le_sum ys (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy'; linarith

/-- the per-child expansion: (alpha + P)(1 + W) - Q = alpha + sum_y [tau y + F y (W - w y)] -/
lemma sum_e (l W : ℝ) : ∀ ys : List ℝ,
    (ys.map (fun y => tau l y + Fl l y * (W - (1 + l * y)))).sum
      = alpha l * (ys.map (fun y => 1 + l * y)).sum + (ys.map (Fl l)).sum + W * (ys.map (Fl l)).sum
        - l * (ys.map (fun y => y * (Fl l y + 1 - alpha l))).sum
  | [] => by simp
  | y :: ys => by
      simp only [List.map_cons, List.sum_cons, sum_e l W ys]
      unfold tau; ring


/-- (T2) of the one-step inequality: alpha + sum_y [tau y + F y (W - w y)] >= 0 -/
lemma T2_aux (hl : 2 ≤ l) : ∀ ys : List ℝ, (∀ y ∈ ys, 0 ≤ y ∧ y ≤ 1) →
    0 ≤ alpha l + (ys.map (fun y => tau l y + Fl l y * ((ys.map (fun y => 1 + l * y)).sum - (1 + l * y)))).sum
  | [], _ => by simp; exact alpha_nonneg (by linarith)
  | [y], hy1 => by
      have hl0 : 0 < l := by linarith
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sub_self, mul_zero]
      have := I2 hl (hy1 y (by simp)).1 (hy1 y (by simp)).2
      have := Fl_le_alpha hl0 (hy1 y (by simp)).2
      linarith
  | y1 :: y2 :: rest, hy1 => by
      have hl0 : 0 < l := by linarith
      set ys := y1 :: y2 :: rest with hys
      have hw1 : ∀ z ∈ ys, 1 ≤ 1 + l * z := fun z hz => by nlinarith [(hy1 z hz).1]
      have h0 : (ys.map (fun _ => (0:ℝ))).sum
          ≤ (ys.map (fun y => tau l y + Fl l y * ((ys.map (fun y => 1 + l * y)).sum - (1 + l * y)))).sum := by
        apply sum_map_le
        intro y hy'
        have hi := I2 hl (hy1 y hy').1 (hy1 y hy').2
        have hwy := elem_plus_le_sum (w := fun y => 1 + l * y) ys hw1 y hy'
        have hlen : (2:ℝ) ≤ ys.length := by
          have : (0:ℝ) ≤ rest.length := by positivity
          rw [hys]; simp only [List.length_cons]; push_cast; linarith
        have hge : 1 ≤ (ys.map (fun y => 1 + l * y)).sum - (1 + l * y) := by linarith
        have : Fl l y ≤ Fl l y * ((ys.map (fun y => 1 + l * y)).sum - (1 + l * y)) := by
          nlinarith [Fl_nonneg l y]
        linarith
      have hz : (ys.map (fun _ => (0:ℝ))).sum = 0 := by simp
      linarith [alpha_nonneg hl0.le]

/-- ONE-STEP INEQUALITY (children messages ys in [0,1]):
  F(x) <= alpha + sum F(y) - x * l * sum y (F(y) + 1 - alpha),   x = 1/(#ys + 1 + l sum ys). -/
lemma onestep (hl : 2 ≤ l) (ys : List ℝ) (hy : ∀ y ∈ ys, 0 ≤ y ∧ y ≤ 1) :
    Fl l (1 / ((ys.length : ℝ) + 1 + l * ys.sum))
      ≤ alpha l + (ys.map (Fl l)).sum
        - (1 / ((ys.length : ℝ) + 1 + l * ys.sum)) * (l * (ys.map (fun y => y * (Fl l y + 1 - alpha l))).sum) := by
  have hl0 : 0 < l := by linarith
  set W := (ys.map (fun y => 1 + l * y)).sum with hWdef
  have hW : W = (ys.length : ℝ) + l * ys.sum := sum_w l ys
  have hsum0 : 0 ≤ ys.sum := by
    have := sum_map_le (f := fun _ => (0:ℝ)) (g := fun y => y) ys (fun y h => (hy y h).1)
    simpa using this
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  set D := 1 + W with hD
  have hDpos : 0 < D := by linarith
  have hDeq : (ys.length : ℝ) + 1 + l * ys.sum = D := by rw [hD, hW]; ring
  rw [hDeq]
  set P := (ys.map (Fl l)).sum with hP
  set Q := (ys.map (fun y => y * (Fl l y + 1 - alpha l))).sum with hQ
  set E := (ys.map (fun y => tau l y + Fl l y * (W - (1 + l * y)))).sum with hE
  have hEid : E = alpha l * W + P + W * P - l * Q := by rw [hE, sum_e l W ys]
  have hrhs : alpha l + P - 1 / D * (l * Q) = (alpha l + E) / D := by
    rw [hEid, hD]; field_simp; ring
  rw [hrhs]
  have hw0 : ∀ z ∈ ys, 0 ≤ 1 + l * z := fun z hz => by nlinarith [(hy z hz).1]
  have hw1 : ∀ z ∈ ys, 1 ≤ 1 + l * z := fun z hz => by nlinarith [(hy z hz).1]
  -- (T1): E >= -c y_ch W
  have hT1 : -(cl l * ycl l * W) ≤ E := by
    have h1 : (ys.map (fun y => -(cl l * ycl l * (1 + l * y)))).sum ≤ E := by
      apply sum_map_le
      intro y hy'
      have hi := I1 hl (hy y hy').1 (hy y hy').2
      have hwy := elem_le_sum (w := fun y => 1 + l * y) ys hw0 y hy'
      have : 0 ≤ Fl l y * (W - (1 + l * y)) := mul_nonneg (Fl_nonneg l y) (by linarith)
      linarith
    have h2 : (ys.map (fun y => -(cl l * ycl l * (1 + l * y)))).sum = -(cl l * ycl l * W) := by
      rw [hWdef]; exact sum_lin_c (cl l * ycl l) (fun y => 1 + l * y) ys
    linarith
  -- (T2): alpha + E >= 0
  have hT2 : 0 ≤ alpha l + E := by rw [hE, hWdef]; exact T2_aux hl ys hy
  -- conclude
  unfold Fl
  apply max_le
  · exact div_nonneg hT2 hDpos.le
  · have hc : cl l * (1 / D - ycl l) = (alpha l - cl l * ycl l * W) / D := by
      rw [← c_one_sub hl0.le, hD]; field_simp; ring
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith) hDpos.le

end lists

end

end LeanCherry
