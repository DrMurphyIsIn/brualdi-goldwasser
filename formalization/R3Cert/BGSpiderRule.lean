/-
  R3Cert.BGSpiderRule -- the explicit Brualdi-Goldwasser maximizer for n >= 492, assembled in Lean.

  Shared base for the spider-certificate formalization (2026-09-25).  It fixes
    * `W n`  -- the rule winner (proof/docs/BG_SPIDER_OPTIMIZATION_2026-09-24.md, section 5): with
                 s = 6(n-1) mod 11, the centre carries only arms; all have 5 cherries except
                   s = 1..4 : s arms of 6   (but for s = 3, n <= 722 and s = 4, n <= 2319: 11-s arms of 4),
                   s = 5..10: 11-s arms of 4;
    * `Cand` -- a bounded candidate set (<= 8 cherries, arms in {4,5,6}, never both 4 and 6, <= 10 of each);
    * the two open inputs as named `Prop`s:
        `StructProp N0` : every F-maximizer with >= N0 vertices lies in `Cand`       (file BGSpiderStruct)
        `CandProp N0`   : inside `Cand`, `W` wins for every size >= N0               (file BGSpiderCand)
  and proves everything else:
    * existence of an F-maximizer at every size (finitely many configurations),
    * the bridge `Aobj (spiderU l) = F l` from the closed form to the actual tree,
    * `spider_opt_of`: StructProp + CandProp => W n is optimal in the spider family,
    * `bg_maximizer_of`: with `BGMax.bg_spider_reduction`, W n maximizes per(L)/prod deg over ALL
      trees on n vertices, for every n >= max N0 492.
  Kernel-checked, no `sorry`.  The two `Prop`s are hypotheses here, not axioms.
-/
import Mathlib
import R3Cert.BGSpiderOpt
import R3Cert.BGMaximizer

namespace R3Cert
namespace BGSpiderRule

open BGSpiderOpt

/-! ### The rule winner -/

/-- The residue class: `n - 1 ≡ 2 s (mod 11)`. -/
def sres (n : ℕ) : ℕ := (6 * (n - 1)) % 11

/-- Number of 4-arms in the rule winner (0 if it uses 6-arms or only 5-arms). -/
def w4 (n : ℕ) : ℕ :=
  let s := sres n
  if s = 0 then 0
  else if s ≤ 4 ∧ ¬ ((s = 3 ∧ n ≤ 722) ∨ (s = 4 ∧ n ≤ 2319)) then 0
  else 11 - s

/-- Number of 6-arms in the rule winner. -/
def w6 (n : ℕ) : ℕ :=
  let s := sres n
  if s = 0 then 0
  else if s ≤ 4 ∧ ¬ ((s = 3 ∧ n ≤ 722) ∨ (s = 4 ∧ n ≤ 2319)) then s
  else 0

/-- Number of 5-arms in the rule winner. -/
def w5 (n : ℕ) : ℕ := (n - 1 - 9 * w4 n - 13 * w6 n) / 11

/-- **The rule winner**: a centre carrying `w4 n` arms of 4 cherries, `w6 n` arms of 6 and `w5 n` of 5. -/
def W (n : ℕ) : List Child :=
  List.replicate (w4 n) (Child.arm 4) ++ List.replicate (w6 n) (Child.arm 6) ++
    List.replicate (w5 n) (Child.arm 5)

theorem nv_append (a b : List Child) : nv (a ++ b) = nv a + nv b - 1 := by
  simp only [nv, List.map_append, List.sum_append]; omega

theorem cost_sum_replicate (k : ℕ) (c : Child) :
    ((List.replicate k c).map Child.cost).sum = k * c.cost := by
  simp [List.map_replicate, List.sum_replicate]

theorem nv_W (n : ℕ) (hn : 492 ≤ n) : nv (W n) = n := by
  simp only [nv, W, List.map_append, List.sum_append, cost_sum_replicate, Child.cost]
  have hs : sres n < 11 := Nat.mod_lt _ (by norm_num)
  have hmod : (n - 1) % 11 = (2 * sres n) % 11 := by
    unfold sres; omega
  unfold w5 w4 w6
  simp only
  split_ifs <;> omega

/-! ### The candidate set and the two open inputs -/

/-- The bounded candidate set. -/
def Cand (l : List Child) : Prop :=
  l.count Child.cherry ≤ 8 ∧
  (∀ c ∈ l, c = Child.cherry ∨ c = Child.arm 4 ∨ c = Child.arm 5 ∨ c = Child.arm 6) ∧
  ¬ (Child.arm 4 ∈ l ∧ Child.arm 6 ∈ l) ∧
  l.count (Child.arm 4) ≤ 10 ∧ l.count (Child.arm 6) ≤ 10

/-- **Open input 1 (structure).**  Every F-maximizer on at least `N0` vertices is a candidate. -/
def StructProp (N0 : ℕ) : Prop := ∀ l : List Child, N0 ≤ nv l → IsMax l → Cand l

/-- **Open input 2 (candidates).**  Inside `Cand`, the rule winner is optimal at every size `≥ N0`. -/
def CandProp (N0 : ℕ) : Prop := ∀ l : List Child, N0 ≤ nv l → Cand l → F l ≤ F (W (nv l))

/-! ### Existence of a maximizer -/

/-- Children of a given cost. -/
def ofCost (k : ℕ) : List Child :=
  (if k = 2 then [Child.cherry] else []) ++ (if k % 2 = 1 then [Child.arm (k / 2)] else [])

theorem cost_pos (c : Child) : 1 ≤ c.cost := by cases c <;> simp [Child.cost]

theorem mem_ofCost (c : Child) : c ∈ ofCost c.cost := by
  cases c with
  | cherry => simp [ofCost, Child.cost]
  | arm j =>
    simp only [ofCost, Child.cost, List.mem_append]
    right
    have h1 : (2 * j + 1) % 2 = 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    simp [h1, h2]

/-- All child lists of total cost `m`. -/
def lists : ℕ → List (List Child)
  | 0 => [[]]
  | m + 1 =>
    (List.range (m + 1)).attach.flatMap fun ⟨i, hi⟩ =>
      (ofCost (i + 1)).flatMap fun c =>
        (lists (m - i)).map fun l => c :: l
  termination_by m => m
  decreasing_by
    simp at hi
    omega

theorem mem_lists : ∀ l : List Child, l ∈ lists (l.map Child.cost).sum
  | [] => by simp [lists]
  | c :: t => by
    have ih := mem_lists t
    have hc := cost_pos c
    obtain ⟨k, hk⟩ : ∃ k, c.cost = k + 1 := ⟨c.cost - 1, by omega⟩
    simp only [List.map_cons, List.sum_cons]
    rw [hk, show k + 1 + (t.map Child.cost).sum = (k + (t.map Child.cost).sum) + 1 by ring, lists]
    simp only [List.mem_flatMap, List.mem_attach, true_and, List.mem_map, Subtype.exists,
      List.mem_range]
    refine ⟨k, by omega, c, by rw [← hk]; exact mem_ofCost c, t, ?_, rfl⟩
    rwa [show k + (t.map Child.cost).sum - k = (t.map Child.cost).sum by omega]

theorem ofCost_cost {c : Child} {k : ℕ} (h : c ∈ ofCost k) : c.cost = k := by
  simp only [ofCost, List.mem_append] at h
  rcases h with h | h
  · split_ifs at h with hk
    · simp at h; subst h; simp [Child.cost, hk]
    · simp at h
  · split_ifs at h with hk
    · simp at h; subst h; simp only [Child.cost]; omega
    · simp at h

theorem cost_of_mem_lists : ∀ (m : ℕ) (l : List Child), l ∈ lists m → (l.map Child.cost).sum = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro l hl
    cases m with
    | zero => simp [lists] at hl; subst hl; simp
    | succ m =>
      rw [lists] at hl
      simp only [List.mem_flatMap, List.mem_attach, true_and, List.mem_map, Subtype.exists,
        List.mem_range] at hl
      obtain ⟨i, hi, c, hc, t, ht, rfl⟩ := hl
      have := ih (m - i) (by omega) t ht
      simp only [List.map_cons, List.sum_cons, ofCost_cost hc, this]
      omega

theorem exists_max_F : ∀ (S : List (List Child)), S ≠ [] → ∃ x ∈ S, ∀ y ∈ S, F y ≤ F x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun y hy => by simp at hy; rw [hy]⟩
  | a :: b :: t, _ => by
    obtain ⟨x, hx, hmax⟩ := exists_max_F (b :: t) (by simp)
    rcases le_total (F a) (F x) with h | h
    · refine ⟨x, List.mem_cons_of_mem _ hx, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h
      · exact hmax y hy'
    · refine ⟨a, by simp, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact le_refl _
      · exact le_trans (hmax y hy') h

/-- **An F-maximizer exists at every size `n ≥ 1`.** -/
theorem exists_isMax (n : ℕ) (hn : 1 ≤ n) : ∃ l : List Child, nv l = n ∧ IsMax l := by
  have hne : lists (n - 1) ≠ [] := by
    intro h
    have := mem_lists (List.replicate (n - 1) (Child.arm 0))
    rw [cost_sum_replicate] at this
    simp [Child.cost, h] at this
  obtain ⟨x, hx, hmax⟩ := exists_max_F _ hne
  have hxc := cost_of_mem_lists _ _ hx
  refine ⟨x, by simp only [nv, hxc]; omega, fun l' hl' => hmax l' ?_⟩
  have := mem_lists l'
  have hc : (l'.map Child.cost).sum = n - 1 := by
    simp only [nv] at hl'; rw [hxc] at hl'; omega
  rwa [hc] at this

/-- **The spider-family optimum** from the two inputs. -/
theorem spider_opt_of {N0 : ℕ} (hS : StructProp N0) (hC : CandProp N0) :
    ∀ l : List Child, N0 ≤ nv l → F l ≤ F (W (nv l)) := by
  intro l hl
  obtain ⟨x, hx, hmax⟩ := exists_isMax (nv l) (by simp only [nv]; omega)
  have hcand : Cand x := hS x (by rw [hx]; exact hl) hmax
  have h1 : F l ≤ F x := hmax l hx.symm
  have h2 := hC x (by rw [hx]; exact hl) hcand
  rw [hx] at h2
  exact le_trans h1 h2

/-! ### The bridge to actual trees -/

open R3Cert.RTree R3Cert.Step3

/-- The tree of a child. -/
def childU : Child → UTree
  | Child.cherry => cherryU
  | Child.arm j => armU j

/-- The spider tree with the given centre children. -/
def spiderU (l : List Child) : UTree := UTree.node (l.map childU)

theorem Ztot_childU (c : Child) : Ztot (dtSub (childU c)) = (c.g : ℝ) := by
  cases c with
  | cherry => simp [childU, Child.g, Ztot_dtSub_cherryU]
  | arm j =>
    simp only [childU, Child.g, alpha, Ztot_dtSub_armU]
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

theorem qterm_childU (c : Child) :
    Zopen (dtSub (childU c)) / Ztot (dtSub (childU c)) / (udeg (childU c) : ℝ) = (c.r : ℝ) := by
  cases c with
  | cherry =>
    simp only [childU, Child.r, Ztot_dtSub_cherryU, Zopen_dtSub_cherryU, udeg_cherryU]
    norm_num
  | arm j =>
    simp only [childU, Child.r, bb, Ztot_dtSub_armU, Zopen_dtSub_armU, udeg_armU]
    have h32 : (0 : ℝ) < (3 / 2) ^ j := by positivity
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

theorem prod_childU (l : List Child) :
    ((l.map childU).map fun K => Ztot (dtSub K)).prod = ((l.map Child.g).prod : ℝ) := by
  induction l with
  | nil => simp
  | cons c t ih => simp only [List.map_cons, List.prod_cons, Ztot_childU, ih]; push_cast; ring

theorem qSum_childU (l : List Child) : qSum (l.map childU) = ((l.map Child.r).sum : ℝ) := by
  induction l with
  | nil => simp [qSum]
  | cons c t ih => rw [List.map_cons, qSum_cons, qterm_childU, ih]; simp

theorem Aobj_spiderU (l : List Child) : Aobj (spiderU l) = (F l : ℝ) := by
  rw [spiderU, Aobj_factor, F, prod_childU, qSum_childU, List.length_map]
  push_cast
  ring

theorem usize_spiderU (l : List Child) : usize (spiderU l) = nv l := by
  rw [spiderU, usize_node, nv]
  congr 1
  induction l with
  | nil => simp [usizeList]
  | cons c t ih =>
    rw [List.map_cons, usizeList_cons, ih, List.map_cons, List.sum_cons]
    cases c with
    | cherry => simp [childU, usize_cherryU, Child.cost]
    | arm j => simp [childU, usize_armU, Child.cost]; omega

/-- Every atom-child tree list is the image of a `Child` list. -/
theorem exists_child_list (cs : List UTree) (h : ∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) :
    ∃ l : List Child, cs = l.map childU := by
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons c t ih =>
    obtain ⟨l, hl⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rcases h c (by simp) with rfl | ⟨j, rfl⟩
    · exact ⟨Child.cherry :: l, by simp [hl, childU]⟩
    · exact ⟨Child.arm j :: l, by simp [hl, childU]⟩

/-- **The Brualdi-Goldwasser maximizer, from the two inputs.**  For every `n ≥ max N0 492`, the spider
    `W n` maximizes `Aobj = per(L)/∏deg` over all trees on `n` vertices. -/
theorem bg_maximizer_of {N0 : ℕ} (hS : StructProp N0) (hC : CandProp N0) (n : ℕ)
    (hn0 : N0 ≤ n) (hn : 492 ≤ n) :
    usize (spiderU (W n)) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (spiderU (W n)) := by
  refine ⟨by rw [usize_spiderU, nv_W n hn], fun t ht => ?_⟩
  obtain ⟨cs, hat, hsz, hle⟩ := BGMax.bg_spider_reduction t (by omega)
  obtain ⟨l, rfl⟩ := exists_child_list cs hat
  have hnv : nv l = n := by
    have := usize_spiderU l; rw [spiderU] at this; omega
  have hopt := spider_opt_of hS hC l (by omega)
  rw [hnv] at hopt
  calc Aobj t ≤ Aobj (UTree.node (l.map childU)) := hle
    _ = (F l : ℝ) := Aobj_spiderU l
    _ ≤ (F (W n) : ℝ) := by exact_mod_cast hopt
    _ = Aobj (spiderU (W n)) := (Aobj_spiderU _).symm

end BGSpiderRule
end R3Cert
