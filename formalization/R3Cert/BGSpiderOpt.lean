/-
  Two-level spider optimization (B2, 2026-09-24): the exchange inequalities, in exact ℚ arithmetic.

  MODEL.  A spider configuration is a list of the centre's children, each a cherry (a pendant 2-path) or an
  arm `A_j` (a vertex adjacent to the centre carrying `j` cherries; `A_0` is a leaf).  The value is the closed
  form of `Aobj` (= per(L)/∏deg) on that tree (cavity recursion at the centre, checked against the tree
  engine in `proof/verification/bg_spider_opt.py closedform`):

      g(cherry) = 3/2,              r(cherry) = 1/3,
      g(A_j)    = (3/2)^j α_j,      r(A_j)    = b_j,       α_j = (4j+3)/(3(j+1)),  b_j = 3/(4j+3),
      F(l) = ∏ g · (1 + (∑ r) / |l|).

  This file models the family by this function only; it is NOT connected to the tree graph.

  RESULTS (no `sorry`, no `native_decide`, axioms: propext, Classical.choice, Quot.sound).
  * `balance_identity`: with Q_c(x,y) = α_x α_y (c + b_x + b_y),
        Q_c(k+t+1, k+1) − Q_c(k+t+2, k) = (t+1)((c−3)(8k+4t+15)+3) / (9(k+1)(k+2)(k+t+2)(k+t+3)).
  * `F_balance_lt`: moving one cherry from arm A_{k+t+2} to arm A_k strictly increases F whenever the
    centre has at least one further child (D ≥ 3), whatever those children are.
  * `balanced_of_isMax`: hence in any F-maximizing configuration of fixed vertex count with D ≥ 3, any two
    arm sizes differ by at most 1 (leaves count as arms of size 0).
  * `F_leafpair_le` / `F_leafpair_lt`: two leaves → one cherry never decreases F, strictly if D ≥ 3.
  * `F_absorb_sub`: the exact sign identity for cherry absorption P + A_j → A_{j+1}.
  * `F_perm`: F depends only on the multiset of children.

  `conjecture1_proved = False` (this is the optimization inside one explicit family, not conjecture1).
-/
import Mathlib

namespace R3Cert
namespace BGSpiderOpt

/-- A child of the spider centre. -/
inductive Child
  | cherry
  | arm (j : ℕ)
  deriving DecidableEq

/-- `α_j = (4j+3)/(3(j+1))`. -/
def alpha (j : ℕ) : ℚ := (4 * (j : ℚ) + 3) / (3 * ((j : ℚ) + 1))

/-- `b_j = 3/(4j+3)`. -/
def bb (j : ℕ) : ℚ := 3 / (4 * (j : ℚ) + 3)

namespace Child

/-- Multiplicative weight of a child. -/
def g : Child → ℚ
  | cherry => 3 / 2
  | arm j => (3 / 2 : ℚ) ^ j * alpha j

/-- Cavity `r` of a child. -/
def r : Child → ℚ
  | cherry => 1 / 3
  | arm j => bb j

/-- Number of vertices of a child subtree. -/
def cost : Child → ℕ
  | cherry => 2
  | arm j => 2 * j + 1

end Child

/-- Closed-form `Aobj` of the spider with children `l`. -/
def F (l : List Child) : ℚ := (l.map Child.g).prod * (1 + (l.map Child.r).sum / l.length)

/-- Vertex count of the spider (centre + children). -/
def nv (l : List Child) : ℕ := 1 + (l.map Child.cost).sum

lemma alpha_pos (j : ℕ) : 0 < alpha j := by unfold alpha; positivity

lemma bb_pos (j : ℕ) : 0 < bb j := by unfold bb; positivity

lemma g_pos (c : Child) : 0 < c.g := by
  cases c with
  | cherry => norm_num [Child.g]
  | arm j => simp only [Child.g]; exact mul_pos (by positivity) (alpha_pos j)

lemma r_nonneg (c : Child) : 0 ≤ c.r := by
  cases c with
  | cherry => norm_num [Child.r]
  | arm j => exact (bb_pos j).le

lemma prod_g_pos (l : List Child) : 0 < (l.map Child.g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_pos (g_pos a) ih

lemma sum_r_nonneg (l : List Child) : 0 ≤ (l.map Child.r).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact add_nonneg (r_nonneg a) ih

/-- `F` only depends on the multiset of children. -/
theorem F_perm {l l' : List Child} (h : l.Perm l') : F l = F l' := by
  unfold F
  rw [(h.map Child.g).prod_eq, (h.map Child.r).sum_eq, h.length_eq]

lemma nv_perm {l l' : List Child} (h : l.Perm l') : nv l = nv l' := by
  unfold nv; rw [(h.map Child.cost).sum_eq]

lemma F_cons_cons (a b : Child) (rest : List Child) :
    F (a :: b :: rest) = a.g * b.g * (rest.map Child.g).prod *
      (1 + (a.r + b.r + (rest.map Child.r).sum) / ((rest.length : ℚ) + 2)) := by
  simp only [F, List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
  push_cast
  ring_nf

lemma F_cons (a : Child) (rest : List Child) :
    F (a :: rest) = a.g * (rest.map Child.g).prod *
      (1 + (a.r + (rest.map Child.r).sum) / ((rest.length : ℚ) + 1)) := by
  simp only [F, List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
  push_cast
  ring_nf

/-! ### Balance -/

/-- `Q_c(x,y) = α_x α_y (c + b_x + b_y)`: the pair factor of `F` at fixed centre degree. -/
def Q (c : ℚ) (x y : ℕ) : ℚ := alpha x * alpha y * (c + bb x + bb y)

/-- The balance identity. -/
theorem balance_identity (c : ℚ) (k t : ℕ) :
    Q c (k + t + 1) (k + 1) - Q c (k + t + 2) k =
      ((t : ℚ) + 1) * ((c - 3) * (8 * (k : ℚ) + 4 * t + 15) + 3) /
        (9 * ((k : ℚ) + 1) * ((k : ℚ) + 2) * ((k : ℚ) + t + 2) * ((k : ℚ) + t + 3)) := by
  unfold Q alpha bb
  push_cast
  have h1 : (4 * ((k : ℚ) + t + 1) + 3) ≠ 0 := by positivity
  have h2 : (4 * ((k : ℚ) + 1) + 3) ≠ 0 := by positivity
  have h3 : (4 * ((k : ℚ) + t + 2) + 3) ≠ 0 := by positivity
  have h4 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  have h5 : (3 * ((k : ℚ) + t + 1 + 1)) ≠ 0 := by positivity
  have h6 : (3 * ((k : ℚ) + 1 + 1)) ≠ 0 := by positivity
  have h7 : (3 * ((k : ℚ) + t + 2 + 1)) ≠ 0 := by positivity
  have h8 : (3 * ((k : ℚ) + 1)) ≠ 0 := by positivity
  have h9 : (9 * ((k : ℚ) + 1) * ((k : ℚ) + 2) * ((k : ℚ) + t + 2) * ((k : ℚ) + t + 3)) ≠ 0 := by
    positivity
  field_simp
  ring

lemma Q_lt_of_three_le (c : ℚ) (hc : 3 ≤ c) (k t : ℕ) :
    Q c (k + t + 2) k < Q c (k + t + 1) (k + 1) := by
  have h := balance_identity c k t
  have hpos : 0 < ((t : ℚ) + 1) * ((c - 3) * (8 * (k : ℚ) + 4 * t + 15) + 3) /
      (9 * ((k : ℚ) + 1) * ((k : ℚ) + 2) * ((k : ℚ) + t + 2) * ((k : ℚ) + t + 3)) := by
    apply div_pos
    · apply mul_pos (by positivity)
      have : 0 ≤ (c - 3) * (8 * (k : ℚ) + 4 * t + 15) := mul_nonneg (by linarith) (by positivity)
      linarith
    · positivity
  linarith

/-- **Balance.**  Moving one cherry from `A_{k+t+2}` to `A_k` strictly increases `F` as soon as the centre
has a further child. -/
theorem F_balance_lt (k t : ℕ) (rest : List Child) (hrest : rest ≠ []) :
    F (Child.arm (k + t + 2) :: Child.arm k :: rest) <
      F (Child.arm (k + t + 1) :: Child.arm (k + 1) :: rest) := by
  rw [F_cons_cons, F_cons_cons]
  set P := (rest.map Child.g).prod with hP
  set R0 := (rest.map Child.r).sum with hR0
  set L := (rest.length : ℚ) with hL
  have hPpos : 0 < P := prod_g_pos rest
  have hR0 : 0 ≤ R0 := sum_r_nonneg rest
  have hL1 : 1 ≤ L := by
    have : 1 ≤ rest.length := List.length_pos_iff.mpr hrest
    rw [hL]; exact_mod_cast this
  simp only [Child.g, Child.r]
  have hpow : (3 / 2 : ℚ) ^ (k + t + 1) * (3 / 2 : ℚ) ^ (k + 1) =
      (3 / 2 : ℚ) ^ (k + t + 2) * (3 / 2 : ℚ) ^ k := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hQ := Q_lt_of_three_le (L + 2 + R0) (by linarith) k t
  unfold Q at hQ
  set E := (3 / 2 : ℚ) ^ (k + t + 2) * (3 / 2 : ℚ) ^ k with hE
  have hEpos : 0 < E := by positivity
  have hD : 0 < L + 2 := by linarith
  -- both sides are  E * P / (L+2) * Q
  have key : ∀ x y : ℕ, (3 / 2 : ℚ) ^ x * alpha x * ((3 / 2 : ℚ) ^ y * alpha y) * P *
      (1 + (bb x + bb y + R0) / (L + 2)) =
      (3 / 2 : ℚ) ^ x * (3 / 2 : ℚ) ^ y * P / (L + 2) *
        (alpha x * alpha y * (L + 2 + R0 + bb x + bb y)) := by
    intro x y; field_simp; ring
  rw [key, key, hpow]
  have hc : 0 < E * P / (L + 2) := by positivity
  exact mul_lt_mul_of_pos_left hQ hc

/-! ### Leaves -/

/-- Two leaves → one cherry: the exact difference. -/
theorem F_leafpair_sub (rest : List Child) :
    F (Child.cherry :: rest) - F (Child.arm 0 :: Child.arm 0 :: rest) =
      (rest.map Child.g).prod *
        (((rest.length : ℚ)) ^ 2 + (rest.length : ℚ) * (rest.map Child.r).sum +
          4 * (rest.map Child.r).sum) /
        (2 * ((rest.length : ℚ) + 1) * ((rest.length : ℚ) + 2)) := by
  rw [F_cons, F_cons_cons]
  simp only [Child.g, Child.r, alpha, bb]
  have h1 : ((rest.length : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((rest.length : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem F_leafpair_le (rest : List Child) :
    F (Child.arm 0 :: Child.arm 0 :: rest) ≤ F (Child.cherry :: rest) := by
  have h := F_leafpair_sub rest
  have hP := prod_g_pos rest
  have hR := sum_r_nonneg rest
  have : 0 ≤ (rest.map Child.g).prod *
      (((rest.length : ℚ)) ^ 2 + (rest.length : ℚ) * (rest.map Child.r).sum +
        4 * (rest.map Child.r).sum) /
      (2 * ((rest.length : ℚ) + 1) * ((rest.length : ℚ) + 2)) := by positivity
  linarith

theorem F_leafpair_lt (rest : List Child) (hrest : rest ≠ []) :
    F (Child.arm 0 :: Child.arm 0 :: rest) < F (Child.cherry :: rest) := by
  have h := F_leafpair_sub rest
  have hP := prod_g_pos rest
  have hR := sum_r_nonneg rest
  have hL : (1 : ℚ) ≤ rest.length := by
    have : 1 ≤ rest.length := List.length_pos_iff.mpr hrest
    exact_mod_cast this
  have : 0 < (rest.map Child.g).prod *
      (((rest.length : ℚ)) ^ 2 + (rest.length : ℚ) * (rest.map Child.r).sum +
        4 * (rest.map Child.r).sum) /
      (2 * ((rest.length : ℚ) + 1) * ((rest.length : ℚ) + 2)) := by
    apply div_pos _ (by positivity)
    apply mul_pos hP
    nlinarith
  linarith

/-! ### Cherry absorption -/

/-- Cherry absorption `P + A_j → A_{j+1}`: the exact difference.  With `D0 = |rest|`, `R0 = ∑_rest r`, the
move improves `F` iff `3D0² + D0(3R0 − 4j² − 11j − 6) + R0(12j² + 33j + 24) − 4j² − 2j > 0`. -/
theorem F_absorb_sub (j : ℕ) (rest : List Child) :
    F (Child.arm (j + 1) :: rest) - F (Child.cherry :: Child.arm j :: rest) =
      (3 / 2 : ℚ) ^ (j + 1) * (rest.map Child.g).prod *
        (3 * (rest.length : ℚ) ^ 2 +
          (rest.length : ℚ) * (3 * (rest.map Child.r).sum - 4 * (j : ℚ) ^ 2 - 11 * j - 6) +
          (rest.map Child.r).sum * (12 * (j : ℚ) ^ 2 + 33 * j + 24) - 4 * (j : ℚ) ^ 2 - 2 * j) /
        (9 * ((j : ℚ) + 1) * ((j : ℚ) + 2) * ((rest.length : ℚ) + 1) * ((rest.length : ℚ) + 2)) := by
  rw [F_cons, F_cons_cons]
  simp only [Child.g, Child.r, alpha, bb]
  have h1 : ((rest.length : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((rest.length : ℚ) + 2) ≠ 0 := by positivity
  have h3 : (4 * ((j : ℚ) + 1) + 3) ≠ 0 := by positivity
  have h4 : (4 * (j : ℚ) + 3) ≠ 0 := by positivity
  have h5 : (3 * ((j : ℚ) + 1 + 1)) ≠ 0 := by positivity
  have h6 : (3 * ((j : ℚ) + 1)) ≠ 0 := by positivity
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-! ### Maximizers are balanced -/

/-- `l` maximizes `F` among configurations with the same vertex count. -/
def IsMax (l : List Child) : Prop := ∀ l' : List Child, nv l' = nv l → F l' ≤ F l

/-- **Maximizers are balanced.**  If `l` maximizes `F` at its vertex count and the centre has degree
`≥ 3`, then any two arm sizes differ by at most one (leaves are arms of size `0`). -/
theorem balanced_of_isMax (l : List Child) (hmax : IsMax l) (hlen : 3 ≤ l.length)
    (j k : ℕ) (hj : Child.arm j ∈ l) (hk : Child.arm k ∈ l) : j ≤ k + 1 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨t, rfl⟩ : ∃ t, j = k + t + 2 := ⟨j - k - 2, by omega⟩
  have hne : Child.arm (k + t + 2) ≠ Child.arm k := by
    intro h; injection h with h; omega
  -- l ~ arm j :: arm k :: rest
  set l1 := l.erase (Child.arm (k + t + 2)) with hl1
  have hp1 : l.Perm (Child.arm (k + t + 2) :: l1) := List.perm_cons_erase hj
  have hk1 : Child.arm k ∈ l1 := (List.mem_erase_of_ne (Ne.symm hne)).mpr hk
  set rest := l1.erase (Child.arm k) with hrest
  have hp2 : l1.Perm (Child.arm k :: rest) := List.perm_cons_erase hk1
  have hp : l.Perm (Child.arm (k + t + 2) :: Child.arm k :: rest) :=
    hp1.trans (List.Perm.cons _ hp2)
  have hlen' : rest.length + 2 = l.length := by
    have := hp.length_eq; simp at this; omega
  have hrest_ne : rest ≠ [] := by
    intro h; rw [h] at hlen'; simp at hlen'; omega
  have hlt := F_balance_lt k t rest hrest_ne
  have hnv : nv (Child.arm (k + t + 1) :: Child.arm (k + 1) :: rest) = nv l := by
    rw [nv_perm hp]
    simp only [nv, List.map_cons, List.sum_cons, Child.cost]
    omega
  have := hmax _ hnv
  rw [F_perm hp] at this
  linarith

/-- **At most one leaf.**  An `F`-maximizer with centre degree `≥ 3` has at most one leaf child. -/
theorem leaf_count_le_one_of_isMax (l : List Child) (hmax : IsMax l) (hlen : 3 ≤ l.length) :
    l.count (Child.arm 0) ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have h0 : Child.arm 0 ∈ l := List.count_pos_iff.mp (by omega)
  set l1 := l.erase (Child.arm 0) with hl1
  have hp1 : l.Perm (Child.arm 0 :: l1) := List.perm_cons_erase h0
  have hc1 : 0 < l1.count (Child.arm 0) := by
    rw [hl1, List.count_erase_self]; omega
  have h1 : Child.arm 0 ∈ l1 := List.count_pos_iff.mp hc1
  set rest := l1.erase (Child.arm 0) with hrest
  have hp : l.Perm (Child.arm 0 :: Child.arm 0 :: rest) :=
    hp1.trans (List.Perm.cons _ (List.perm_cons_erase h1))
  have hlen' : rest.length + 2 = l.length := by
    have := hp.length_eq; simp at this; omega
  have hrest_ne : rest ≠ [] := by
    intro h; rw [h] at hlen'; simp at hlen'; omega
  have hlt := F_leafpair_lt rest hrest_ne
  have hnv : nv (Child.cherry :: rest) = nv l := by
    rw [nv_perm hp]
    simp only [nv, List.map_cons, List.sum_cons, Child.cost]
    omega
  have := hmax _ hnv
  rw [F_perm hp] at this
  linarith

end BGSpiderOpt
end R3Cert
