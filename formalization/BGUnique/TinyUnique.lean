import Mathlib
import R3Cert.BGMaximizerTiny
import BGUnique.RerootEquiv

namespace R3Cert
namespace TinyUnique

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL R3Cert.BGSpiderOpt R3Cert.BGSpiderRule R3Cert.BGSpiderTable BGMax
open R3Cert.BGMaximizerTiny R3Cert.RerootEquiv

/-! ### Recognizing paths -/

mutual
/-- `some k` when the subtree is the end-rooted path `pathU k`. -/
def plen : UTree → Option ℕ
  | .node cs => plenL cs
def plenL : List UTree → Option ℕ
  | [] => some 0
  | c :: t => if t.length = 0 then (plen c).map (· + 1) else none
end

theorem plen_sound : ∀ (k : ℕ) (t : UTree), plen t = some k → t = pathU k := by
  intro k
  induction k with
  | zero =>
    rintro ⟨cs⟩ h
    cases cs with
    | nil => rfl
    | cons c t =>
      simp only [plen, plenL] at h
      split_ifs at h with h0
      cases hp : plen c <;> simp [hp] at h
  | succ k ih =>
    rintro ⟨cs⟩ h
    cases cs with
    | nil => simp [plen, plenL] at h
    | cons c t =>
      simp only [plen, plenL] at h
      split_ifs at h with h0
      · cases hp : plen c with
        | none => simp [hp] at h
        | some k' =>
          simp only [hp, Option.map_some, Option.some.injEq] at h
          have hk : k' = k := by omega
          subst hk
          rw [List.length_eq_zero_iff] at h0
          subst h0
          rw [ih c hp]; rfl

/-- The child list of a path rooting: one or two end-rooted paths. -/
def pathForm : List UTree → Bool
  | [p] => (plen p).isSome
  | [p, q] => (plen p).isSome && (plen q).isSome
  | _ => false

/-- The strict tiny check: every rooted tree on `n` vertices is strictly below the table value, or is a
    rooting of a path. -/
def tinyX (n : ℕ) : Bool :=
  (forestsF n (n - 1)).all fun cs =>
    decide (piRootQ (cs.map fromU) * ((tabV n).2 : ℚ) < ((tabV n).1 : ℚ)) || pathForm cs

theorem tinyX_456 : tinyX 4 = true ∧ tinyX 5 = true ∧ tinyX 6 = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The table spider for `n = 4, 5, 6` is a rooting of the path on `n` vertices. -/
theorem tab_path (n : ℕ) (h4 : 4 ≤ n) (h6 : n ≤ 6) :
    RerootRel (spiderU (tab n)) (UTree.node [pathU (n - 2)]) := by
  interval_cases n
  · rw [show tab 4 = [Child.arm 1] by decide]
    exact Relation.ReflTransGen.refl
  · rw [show tab 5 = [Child.cherry, Child.cherry] by decide]
    exact path_two 1 1
  · rw [show tab 6 = [Child.cherry, Child.arm 1] by decide]
    exact path_two 1 2

/-- **Uniqueness of the maximizer for `n = 4, 5, 6`**: every maximizing tree is a rerooting of the table
    spider (the path). -/
theorem tiny_unique (n : ℕ) (h4 : 4 ≤ n) (h6 : n ≤ 6) (t : UTree) (ht : usize t = n)
    (hmax : ∀ t' : UTree, usize t' = n → Aobj t' ≤ Aobj t) : RerootRel t (spiderU (tab n)) := by
  obtain ⟨hnv, _⟩ := spider_opt_table n h4 (by omega)
  have hc : tinyX n = true := by
    obtain ⟨a, b, c⟩ := tinyX_456
    interval_cases n <;> assumption
  obtain ⟨cs⟩ := t
  have ht' := ht
  rw [usize_node] at ht'
  have hmem : cs ∈ forestsF n (n - 1) := by
    have := mem_forestsF n cs (by omega)
    rwa [show usizeList cs = n - 1 by omega] at this
  have hb := (List.all_eq_true.mp hc) cs hmem
  rw [Bool.or_eq_true] at hb
  have hc2 := checkN_all n h4 (by omega)
  simp only [checkN, Bool.and_eq_true] at hc2
  have hpos : 0 < (row n).1 + (row n).2.2.1 + (row n).2.2.2 := Nat.blt_eq.mp hc2.1.1.2
  have hq : (0 : ℚ) < (tabV n).2 := by exact_mod_cast fden_pos _ _ _ _ hpos
  have hF : F (tab n) = ((tabV n).1 : ℚ) / (tabV n).2 := by rw [tab, F_canon_eq _ _ _ _ hpos]; rfl
  rcases hb with hlt | hpf
  · exfalso
    have hlt' := of_decide_eq_true hlt
    have h1 : piRootQ (cs.map fromU) < F (tab n) := by rw [hF, lt_div_iff₀ hq]; exact hlt'
    have h2 := hmax (spiderU (tab n)) (by rw [usize_spiderU, hnv])
    rw [Aobj_eq_Q, Aobj_spiderU] at h2
    have h3 : ((piRootQ (cs.map fromU) : ℚ) : ℝ) < ((F (tab n) : ℚ) : ℝ) := by exact_mod_cast h1
    linarith
  · refine Relation.ReflTransGen.trans ?_ (symm (tab_path n h4 h6))
    match cs, hpf, ht' with
    | [p], hpf, ht' =>
      simp only [pathForm, Option.isSome_iff_exists] at hpf
      obtain ⟨a, ha⟩ := hpf
      rw [plen_sound a p ha] at ht' ⊢
      simp only [usizeList_cons, usizeList_nil, usize_pathU] at ht'
      rw [show n - 2 = a by omega]
    | [p, q], hpf, ht' =>
      simp only [pathForm, Bool.and_eq_true, Option.isSome_iff_exists] at hpf
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hpf
      rw [plen_sound a p ha, plen_sound b q hb] at ht' ⊢
      simp only [usizeList_cons, usizeList_nil, usize_pathU] at ht'
      rw [show n - 2 = a + b + 1 by omega]
      exact path_two a b
    | [], hpf, _ => simp [pathForm] at hpf
    | _ :: _ :: _ :: _, hpf, _ => simp [pathForm] at hpf

end TinyUnique
end R3Cert
