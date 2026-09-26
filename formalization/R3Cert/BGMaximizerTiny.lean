/-
  R3Cert.BGMaximizerTiny -- the Brualdi-Goldwasser maximizer for n = 4, 5, 6, by direct enumeration.

  `cavQ` is the BGSCL cavity recursion over ℚ (`cavQ_cast`: it agrees with `cav`), so `Aobj` of a tree is
  an explicit rational (`Aobj_eq_Q`).  `forestsF` enumerates every child list of a given total size by
  structural recursion (the kernel does not reduce well-founded recursion), and the kernel checks
  `Aobj t ≤ F (tab n)` for every tree on n = 4, 5, 6 vertices.
  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGMaximizerMid

namespace R3Cert
namespace BGMaximizerTiny

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL R3Cert.BGSpiderOpt R3Cert.BGSpiderRule R3Cert.BGSpiderTable BGMax

/-! ### The cavity recursion over ℚ -/

mutual
def cavQ : BGSCL.Branch → ℚ × ℚ
  | .node cs => ((cavAggQ cs).1, (cavAggQ cs).1 * (1 + (cavAggQ cs).2 / ((cs.length : ℚ) + 1)))
def cavAggQ : List BGSCL.Branch → ℚ × ℚ
  | [] => (1, 0)
  | c :: t => ((cavQ c).2 * (cavAggQ t).1,
               (cavQ c).1 / ((cavQ c).2 * ((bcc c : ℚ) + 1)) + (cavAggQ t).2)
end

mutual
theorem cavQ_cast : ∀ b : BGSCL.Branch,
    ((cavQ b).1 : ℝ) = (BGSCL.cav b).1 ∧ ((cavQ b).2 : ℝ) = (BGSCL.cav b).2
  | .node cs => by
    obtain ⟨h1, h2⟩ := cavAggQ_cast cs
    simp only [cavQ, BGSCL.cav]; push_cast; rw [h1, h2]; exact ⟨rfl, rfl⟩
theorem cavAggQ_cast : ∀ l : List BGSCL.Branch,
    ((cavAggQ l).1 : ℝ) = (cavAgg l).1 ∧ ((cavAggQ l).2 : ℝ) = (cavAgg l).2
  | [] => by simp [cavAggQ, cavAgg]
  | c :: t => by
    obtain ⟨c1, c2⟩ := cavQ_cast c
    obtain ⟨t1, t2⟩ := cavAggQ_cast t
    simp only [cavAggQ, cavAgg]; push_cast; rw [c1, c2, t1, t2]; exact ⟨rfl, rfl⟩
end

/-- `piRoot` over ℚ. -/
def piRootQ (cs : List BGSCL.Branch) : ℚ :=
  (cs.map (fun c => (cavQ c).2)).prod * (1 + (cs.map fun c => (cavQ c).1 / ((cavQ c).2 * ((bcc c : ℚ) + 1))).sum
    / (cs.length : ℚ))

theorem e2_cast (c : BGSCL.Branch) :
    ((((cavQ c).1 / ((cavQ c).2 * ((bcc c : ℚ) + 1))) : ℚ) : ℝ) = bY c := by
  rw [bY, bh]; push_cast; rw [(cavQ_cast c).1, (cavQ_cast c).2, div_div]

theorem prod_cast (cs : List BGSCL.Branch) :
    (((cs.map (fun c => (cavQ c).2)).prod : ℚ) : ℝ) = (cs.map (fun c => (BGSCL.cav c).2)).prod := by
  induction cs with
  | nil => simp
  | cons c t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Rat.cast_mul, (cavQ_cast c).2, ih]

theorem sum_cast (cs : List BGSCL.Branch) :
    (((cs.map fun c => (cavQ c).1 / ((cavQ c).2 * ((bcc c : ℚ) + 1))).sum : ℚ) : ℝ) = (cs.map bY).sum := by
  induction cs with
  | nil => simp
  | cons c t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Rat.cast_add, e2_cast c, ih]

theorem piRootQ_cast (cs : List BGSCL.Branch) : ((piRootQ cs : ℚ) : ℝ) = piRoot cs := by
  unfold piRootQ piRoot
  rw [Rat.cast_mul, prod_cast, Rat.cast_add, Rat.cast_one, Rat.cast_div, sum_cast, Rat.cast_natCast]

theorem Aobj_eq_Q (cs : List UTree) : Aobj (UTree.node cs) = ((piRootQ (cs.map fromU) : ℚ) : ℝ) := by
  rw [Aobj_eq_piRoot, piRootQ_cast]

/-! ### Enumeration by structural recursion -/

/-- All child lists of total size `m`, with fuel. -/
def forestsF : ℕ → ℕ → List (List UTree)
  | 0, _ => []
  | _ + 1, 0 => [[]]
  | f + 1, m + 1 =>
    (List.range (m + 1)).flatMap fun i =>
      (forestsF f i).flatMap fun a => (forestsF f (m - i)).map fun g => UTree.node a :: g

theorem mem_forestsF : ∀ (f : ℕ) (l : List UTree), usizeList l < f → l ∈ forestsF f (usizeList l) := by
  intro f
  induction f with
  | zero => intro l hl; omega
  | succ f ih =>
    intro l hl
    cases l with
    | nil => simp [forestsF, usizeList]
    | cons t r =>
      cases t with
      | node a =>
        have hs : usizeList (UTree.node a :: r) = (usizeList a + usizeList r) + 1 := by
          rw [usizeList_cons, usize_node]; ring
        rw [usizeList_cons, usize_node] at hl
        rw [hs, forestsF]
        simp only [List.mem_flatMap, List.mem_map, List.mem_range]
        refine ⟨usizeList a, by omega, a, ih a (by omega), r, ?_, rfl⟩
        rw [show usizeList a + usizeList r - usizeList a = usizeList r by omega]
        exact ih r (by omega)

/-- The kernel check at size `n`. -/
def tinyOK (n : ℕ) : Bool :=
  (forestsF n (n - 1)).all fun cs =>
    decide (piRootQ (cs.map fromU) * ((tabV n).2 : ℚ) ≤ ((tabV n).1 : ℚ))

theorem tinyOK_456 : tinyOK 4 = true ∧ tinyOK 5 = true ∧ tinyOK 6 = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The Brualdi-Goldwasser maximizer for `n = 4, 5, 6`.** -/
theorem bg_maximizer_tiny (n : ℕ) (h4 : 4 ≤ n) (h6 : n ≤ 6) :
    usize (spiderU (tab n)) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (spiderU (tab n)) := by
  obtain ⟨hnv, _⟩ := spider_opt_table n h4 (by omega)
  refine ⟨by rw [usize_spiderU, hnv], fun t ht => ?_⟩
  have hc : tinyOK n = true := by
    obtain ⟨a, b, c⟩ := tinyOK_456
    interval_cases n <;> assumption
  obtain ⟨cs⟩ := t
  rw [usize_node] at ht
  have hmem : cs ∈ forestsF n (n - 1) := by
    have := mem_forestsF n cs (by omega)
    rwa [show usizeList cs = n - 1 by omega] at this
  have hle := of_decide_eq_true ((List.all_eq_true.mp hc) cs hmem)
  have hc2 := checkN_all n h4 (by omega)
  simp only [checkN, Bool.and_eq_true] at hc2
  have hpos : 0 < (row n).1 + (row n).2.2.1 + (row n).2.2.2 := Nat.blt_eq.mp hc2.1.1.2
  have hq : (0 : ℚ) < (tabV n).2 := by exact_mod_cast fden_pos _ _ _ _ hpos
  rw [Aobj_eq_Q, Aobj_spiderU]
  have hF : F (tab n) = ((tabV n).1 : ℚ) / (tabV n).2 := by rw [tab, F_canon_eq _ _ _ _ hpos]; rfl
  have : piRootQ (cs.map fromU) ≤ F (tab n) := by rw [hF, le_div_iff₀ hq]; exact hle
  exact_mod_cast this

end BGMaximizerTiny
end R3Cert
