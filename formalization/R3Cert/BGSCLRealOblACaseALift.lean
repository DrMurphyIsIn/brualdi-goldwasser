/-
  RealObligationA — Case A: the DEGREE-CHANGING `Aobj` context-lift (the sole open residual).

  `BGSCLRealOblACaseAIdentity.lean` proved the ROOT-level `Aobj`-monotonicity `f2_aobj_monotone`
  (the move `node (leaf :: leaf :: rest) → node (stem :: rest)` acting AT the root).  The full
  `RealObligationA` straightening move also fires when the acted node `u` is a NON-root child of some
  parent.  `BGSCLRealOblACaseABook.lean` stated that whole-tree obligation as the (unproved) `Prop`
  `Aobj_flp_context_lift` and flagged it as genuinely degree-changing (`node [leaf,leaf]` has `udeg 3`,
  `flpStem` has `udeg 2`), hence NOT an instance of the degree-preserving `Aobj_child_replace_le`.

  MEASUREMENT CORRECTION (this file).  The literal `Aobj_flp_context_lift` as written in the Book file
  — replacing a child `node [flpLeaf, flpLeaf]` (with NO further children) wholesale by `flpStem` —
  is FALSE in the cavity model: a 20k-case random sweep finds a whole-tree `Aobj` DECREASE in ~94% of
  contexts.  The reason: stripped of siblings the acted child's realized `Ztot(dtSub)` DROPS (5/3 →
  3/2), and the parent-edge weight gain does not compensate.  The genuine leaf-path-extension move
  keeps the acted node's OTHER children `crest`: the acted child is `node (flpLeaf :: flpLeaf :: crest)`
  → `node (flpStem :: crest)`.  THAT move is monotone (0 violations over the same sweep, all `crest`),
  because the child's own `Ztot(dtSub)` and `Zopen(dtSub)` both RISE while `udeg` drops by 1.

  What is PROVED here (no `sorry`, axiom-clean):
    * `Aobj_child_replace_le_deg`      — any-position degree-changing child-replacement `Aobj`-mono
                                          (lifts `Aobj_tail_child_replace_le_deg` via `Aobj_node_perm`).
    * `Ztot_dtSub_flpChildBefore/After`, `Zopen_dtSub_flpChildBefore/After` — the concrete cavity values
      of the acted child before/after, PARAMETRIC in `crest`.
    * `aobj_flp_context_lift_crest` — the CORRECTED context-lift: the leaf-path-extension acting at a
      non-root child (which retains its other children `crest`) does not decrease whole-tree `Aobj`.
    * `flp_context_lift_root_false` — a witnessed COUNTEREXAMPLE to the literal Book `Prop` at `crest=[]`,
      documenting that the residual as originally stated is not the theorem.

  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47RootRate
import R3Cert.R47R7DegMono
import R3Cert.R47R7ChildMono
import R3Cert.BGSCLRealOblACaseAIdentity
import R3Cert.BGSCLRealOblACaseABook

namespace R3Cert
namespace Step3

open RTree

/-! ### 1. Any-position degree-changing child-replacement is `Aobj`-monotone. -/

/-- **Any-position degree-changing child-replacement.**  Replacing an arbitrary root child `T`
    (siblings `pre`/`post`) by `T'` with not-smaller `Ztot(dtSub)` and not-smaller WEIGHTED
    `Zopen(dtSub)` (`(1/(d·udeg))·Zopen`, `d = |pre|+|post|+1` the common root degree) does not
    decrease `Aobj`.  The degree-changing analogue of `Aobj_child_replace_le`; reduces to the tail
    case `Aobj_tail_child_replace_le_deg` by permuting `T` to the tail via `Aobj_node_perm`. -/
theorem Aobj_child_replace_le_deg (pre post : List UTree) (T T' : UTree)
    (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T'))
    (hweighted : (1 / ((((pre.length + post.length + 1 : ℕ)) : ℝ) * (udeg T : ℝ))) * Zopen (dtSub T)
               ≤ (1 / ((((pre.length + post.length + 1 : ℕ)) : ℝ) * (udeg T' : ℝ))) * Zopen (dtSub T')) :
    Aobj (UTree.node (pre ++ T :: post)) ≤ Aobj (UTree.node (pre ++ T' :: post)) := by
  have hperm : ∀ X : UTree, (pre ++ X :: post).Perm ((pre ++ post) ++ [X]) := by
    intro X
    have h1 : (X :: post).Perm (post ++ [X]) := by
      simpa using (List.perm_append_comm (l₁ := [X]) (l₂ := post))
    have h2 := h1.append_left pre
    rw [List.append_assoc]
    exact h2
  have hlen : (pre ++ post).length + 1 = pre.length + post.length + 1 := by
    rw [List.length_append]
  calc Aobj (UTree.node (pre ++ T :: post))
      = Aobj (UTree.node ((pre ++ post) ++ [T])) := Aobj_node_perm (hperm T)
    _ ≤ Aobj (UTree.node ((pre ++ post) ++ [T'])) := by
        apply Aobj_tail_child_replace_le_deg (pre ++ post) T T' hzt
        rw [hlen]; exact hweighted
    _ = Aobj (UTree.node (pre ++ T' :: post)) := (Aobj_node_perm (hperm T')).symm

/-! ### 2. The acted child's cavity values (parametric in `crest`). -/

/-- The acted child BEFORE the move: two pendant leaves plus the retained children `crest`. -/
abbrev flpChildBefore (crest : List UTree) : UTree := UTree.node (flpLeaf :: flpLeaf :: crest)
/-- The acted child AFTER the move: the two leaves merged into a `flpStem`, `crest` retained. -/
abbrev flpChildAfter (crest : List UTree) : UTree := UTree.node (flpStem :: crest)

theorem udeg_flpChildBefore (crest : List UTree) :
    udeg (flpChildBefore crest) = crest.length + 3 := by
  simp [flpChildBefore, udeg_node]

theorem udeg_flpChildAfter (crest : List UTree) :
    udeg (flpChildAfter crest) = crest.length + 2 := by
  simp [flpChildAfter, udeg_node]

/-- `Zopen(dtSub)` of the acted child BEFORE: the child-product `P = ∏ Ztot(dtSub crest)`
    (the two leaves contribute `1`). -/
theorem Zopen_dtSub_flpChildBefore (crest : List UTree) :
    Zopen (dtSub (flpChildBefore crest)) = (crest.map fun K => Ztot (dtSub K)).prod := by
  rw [flpChildBefore, dtSub_node]
  have h : Zopen (RTree.node (dtChildren ((flpLeaf :: flpLeaf :: crest).length + 1)
      (flpLeaf :: flpLeaf :: crest)))
      = Popen (dtChildren ((flpLeaf :: flpLeaf :: crest).length + 1) (flpLeaf :: flpLeaf :: crest)) :=
    rfl
  rw [h, Popen_dtChildren]
  simp only [List.map_cons, List.prod_cons, Ztot_dtSub_flpLeaf, one_mul]

/-- `Zopen(dtSub)` of the acted child AFTER: `(3/2)·P` (the merged stem contributes `3/2`). -/
theorem Zopen_dtSub_flpChildAfter (crest : List UTree) :
    Zopen (dtSub (flpChildAfter crest)) = (3 / 2) * (crest.map fun K => Ztot (dtSub K)).prod := by
  rw [flpChildAfter, dtSub_node]
  have h : Zopen (RTree.node (dtChildren ((flpStem :: crest).length + 1) (flpStem :: crest)))
      = Popen (dtChildren ((flpStem :: crest).length + 1) (flpStem :: crest)) := rfl
  rw [h, Popen_dtChildren]
  simp only [List.map_cons, List.prod_cons, Ztot_dtSub_flpStem]

/-- `Ztot(dtSub)` of the acted child BEFORE, via the root-degree factorization at degree `|crest|+3`:
    `P·(1 + (2 + Q)/(|crest|+3))`, `P = ∏ Ztot(dtSub crest)`, `Q = qSum crest`. -/
theorem Ztot_dtSub_flpChildBefore (crest : List UTree) :
    Ztot (dtSub (flpChildBefore crest))
      = (crest.map fun K => Ztot (dtSub K)).prod
        * (1 + (1 / ((crest.length : ℝ) + 3)) * (2 + qSum crest)) := by
  rw [flpChildBefore, dtSub_node]
  have hlen : (flpLeaf :: flpLeaf :: crest).length + 1 = crest.length + 3 := by
    simp only [List.length_cons]
  rw [hlen, Ztot_node_deg]
  simp only [List.map_cons, List.prod_cons, Ztot_dtSub_flpLeaf, one_mul, qSum_cons,
    Zopen_dtSub_flpLeaf, udeg_flpLeaf, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    div_one, one_div_one]
  ring

/-- `Ztot(dtSub)` of the acted child AFTER, via the root-degree factorization at degree `|crest|+2`:
    `(3/2)·P·(1 + (1/3 + Q)/(|crest|+2))`. -/
theorem Ztot_dtSub_flpChildAfter (crest : List UTree) :
    Ztot (dtSub (flpChildAfter crest))
      = (3 / 2) * (crest.map fun K => Ztot (dtSub K)).prod
        * (1 + (1 / ((crest.length : ℝ) + 2)) * (1 / 3 + qSum crest)) := by
  rw [flpChildAfter, dtSub_node]
  have hlen : (flpStem :: crest).length + 1 = crest.length + 2 := by
    simp [List.length_cons]
  rw [hlen, Ztot_node_deg]
  simp only [List.map_cons, List.prod_cons, Ztot_dtSub_flpStem, qSum_cons,
    Zopen_dtSub_flpStem, udeg_flpStem, Nat.cast_add, Nat.cast_ofNat]
  ring

/-! ### 3. The two child-cavity gains (`Ztot` and weighted `Zopen`) are nonnegative. -/

/-- Common abbreviation: the retained-children product `P` and cavity sum `Q` are nonnegative. -/
theorem flp_crest_P_nonneg (crest : List UTree) :
    0 ≤ (crest.map fun K => Ztot (dtSub K)).prod := by
  apply List.prod_nonneg; intro x hx
  obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le

/-- **The acted child's `Ztot(dtSub)` RISES.**  `Ztot(dtSub before) ≤ Ztot(dtSub after)`: the closed-form
    increment is `P·(Q·n + 5·Q + n² + 2·n + 1)/(2(n+2)(n+3)) ≥ 0` (`n = |crest|`, `P,Q ≥ 0`). -/
theorem Ztot_dtSub_flp_child_le (crest : List UTree) :
    Ztot (dtSub (flpChildBefore crest)) ≤ Ztot (dtSub (flpChildAfter crest)) := by
  rw [Ztot_dtSub_flpChildBefore, Ztot_dtSub_flpChildAfter]
  set P : ℝ := (crest.map fun K => Ztot (dtSub K)).prod with hP
  set Q : ℝ := qSum crest with hQ
  set n : ℝ := (crest.length : ℝ) with hn
  have hPnn : 0 ≤ P := flp_crest_P_nonneg crest
  have hQnn : 0 ≤ Q := by rw [hQ]; exact qSum_nonneg crest
  have hnnn : 0 ≤ n := by rw [hn]; exact Nat.cast_nonneg _
  have h2 : (0 : ℝ) < n + 2 := by linarith
  have h3 : (0 : ℝ) < n + 3 := by linarith
  -- Reduce to a polynomial inequality via the closed increment form.
  have key : (3 / 2) * P * (1 + 1 / (n + 2) * (1 / 3 + Q))
      - P * (1 + 1 / (n + 3) * (2 + Q))
      = P * (Q * n + 5 * Q + n ^ 2 + 2 * n + 1) / (2 * (n + 2) * (n + 3)) := by
    field_simp
    ring
  have hnum : (0 : ℝ) ≤ Q * n + 5 * Q + n ^ 2 + 2 * n + 1 := by nlinarith [hQnn, hnnn]
  have hden : (0 : ℝ) < 2 * (n + 2) * (n + 3) := by positivity
  have hge : (0 : ℝ) ≤ P * (Q * n + 5 * Q + n ^ 2 + 2 * n + 1) / (2 * (n + 2) * (n + 3)) :=
    div_nonneg (mul_nonneg hPnn hnum) hden.le
  linarith [key, hge]

/-- **The acted child's WEIGHTED `Zopen(dtSub)` RISES** at any common root degree `d`.  With the
    parent-edge weight `1/(d·udeg)`, `(1/(d·udeg before))·Zopen before ≤ (1/(d·udeg after))·Zopen after`.
    The `udeg` DROP (n+3 → n+2) and the `Zopen` RISE (`P → (3/2)P`) both push the same direction:
    `(3/2)/(n+2) ≥ 1/(n+3)` ⟺ `n ≥ -5`. -/
theorem Zopen_weighted_flp_child_le (crest : List UTree) (d : ℕ) :
    (1 / ((d : ℝ) * (udeg (flpChildBefore crest) : ℝ))) * Zopen (dtSub (flpChildBefore crest))
      ≤ (1 / ((d : ℝ) * (udeg (flpChildAfter crest) : ℝ))) * Zopen (dtSub (flpChildAfter crest)) := by
  rw [Zopen_dtSub_flpChildBefore, Zopen_dtSub_flpChildAfter,
      udeg_flpChildBefore, udeg_flpChildAfter]
  set P : ℝ := (crest.map fun K => Ztot (dtSub K)).prod with hP
  set n : ℕ := crest.length with hn
  have hPnn : 0 ≤ P := flp_crest_P_nonneg crest
  have hDnn : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hcb : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
  have hca : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcb, hca]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; simp
  · have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- 1·P · (d·(n+2)) ≤ 1·((3/2)P) · (d·(n+3))
    have hexp : (3 / 2) * P * ((d : ℝ) * ((n : ℝ) + 3)) - P * ((d : ℝ) * ((n : ℝ) + 2))
        = (d : ℝ) * P * ((n : ℝ) + 5) / 2 := by ring
    nlinarith [mul_nonneg (mul_nonneg hDnn hPnn) (by positivity : (0:ℝ) ≤ (n : ℝ) + 5), hexp]

/-! ### 4. The corrected context-lift. -/

/-- **The corrected Case-A `Aobj` context-lift.**  The leaf-path-extension acting at a NON-root child
    `u = node (flpLeaf :: flpLeaf :: crest)` (which RETAINS its other children `crest`, going to
    `node (flpStem :: crest)`) does not decrease the whole tree's `Aobj`, in ANY sibling context
    `pre`/`post`.  This is the true residual obligation; it composes the degree-changing any-position
    child-replacement `Aobj_child_replace_le_deg` with the two nonnegative child-cavity gains
    (`Ztot_dtSub_flp_child_le`, `Zopen_weighted_flp_child_le`).  Contrast `flp_context_lift_book_false`:
    the literal Book `Prop` (which drops the two leaves to a single leaf, `node [flpLeaf,flpLeaf] →
    flpStem = node [flpLeaf]`, not to `node [flpStem]`) is FALSE. -/
theorem aobj_flp_context_lift_crest (pre post : List UTree) (crest : List UTree) :
    Aobj (UTree.node (pre ++ flpChildBefore crest :: post))
      ≤ Aobj (UTree.node (pre ++ flpChildAfter crest :: post)) := by
  apply Aobj_child_replace_le_deg pre post (flpChildBefore crest) (flpChildAfter crest)
    (Ztot_dtSub_flp_child_le crest)
  exact Zopen_weighted_flp_child_le crest (pre.length + post.length + 1)

/-! ### 5. The literal Book `Prop` is refuted by a concrete witness. -/

/-- **The literal Book residual is FALSE.**  `Aobj_flp_context_lift` (the Book `def`) asserts that
    replacing a child `node [flpLeaf, flpLeaf]` WHOLESALE by `flpStem = node [flpLeaf]` never decreases
    `Aobj`.  Witness `pre = []`, `post = [flpLeaf]`: the tree `node [node [leaf, leaf], leaf]` has
    `Aobj = 8/3`, but `node [flpStem, leaf]` has `Aobj = 5/2 < 8/3`.  (Stripped of its siblings the
    acted child's realized `Ztot(dtSub)` DROPS `5/3 → 3/2`; the retained-`crest` form
    `aobj_flp_context_lift_crest` is the corrected, TRUE statement.) -/
theorem flp_context_lift_book_false : ¬ Aobj_flp_context_lift := by
  intro h
  have hbad := h [] [flpLeaf]
  simp only [List.nil_append] at hbad
  -- Concrete cavity values of the acted child `node [leaf, leaf]` (the `crest = []` instances).
  have hZtb : Ztot (dtSub (UTree.node [flpLeaf, flpLeaf])) = 5 / 3 := by
    have := Ztot_dtSub_flpChildBefore []
    simp only [flpChildBefore, List.map_nil, List.prod_nil, List.length_nil, Nat.cast_zero,
      qSum, add_zero] at this ⊢
    rw [this]; norm_num
  have hZob : Zopen (dtSub (UTree.node [flpLeaf, flpLeaf])) = 1 := by
    have := Zopen_dtSub_flpChildBefore []
    simpa only [flpChildBefore, List.map_nil, List.prod_nil] using this
  have hudb : udeg (UTree.node [flpLeaf, flpLeaf]) = 3 := by simp [udeg_node]
  -- Compute both objectives explicitly via the root-degree factorization.
  have hbefore : Aobj (UTree.node (UTree.node [flpLeaf, flpLeaf] :: [flpLeaf])) = 8 / 3 := by
    rw [Aobj_factor]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, qSum_cons, Ztot_dtSub_flpLeaf, Zopen_dtSub_flpLeaf,
      udeg_flpLeaf, qSum, List.map_nil, List.sum_nil, add_zero, hZtb, hZob, hudb,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    norm_num
  have hafter : Aobj (UTree.node (flpStem :: [flpLeaf])) = 5 / 2 := by
    rw [Aobj_factor]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, qSum_cons, Ztot_dtSub_flpStem, Zopen_dtSub_flpStem,
      udeg_flpStem, Ztot_dtSub_flpLeaf, Zopen_dtSub_flpLeaf, udeg_flpLeaf, qSum,
      List.map_nil, List.sum_nil, add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    norm_num
  rw [hbefore, hafter] at hbad
  norm_num at hbad

end Step3
end R3Cert
