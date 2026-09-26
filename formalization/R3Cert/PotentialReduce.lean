/-
  General-case infrastructure, piece 3: THE CLASSIFICATION REDUCTION — trees to four numbers.

  For any plain child list `ch` there are `a` (arms), `nl` (leaves), `m` (generic children) and
  `Sg` (generic cavity mass) with
    `ch.length = a + nl + m`,   `cavSum ch = a/3 + nl + Sg`,   `0 ≤ Sg ≤ m/2`,
    `a·(−ω) + nl·L + (11/50)·(Sg − m·T0)₊ ≤ Σ_{b ∈ ch} Pval (cav b)`.
  Proof: structural induction; arms/leaves contribute their exact `Pval` values, and a generic child
  contributes `Pval(cav b) = (11/50)·(cav b − T0)₊` (never on the special points `{1/3, 1}` by the
  cavity lemmas), folded into the running positive part by `posPart_add_le`.

  With `eroot_plain_node` and `cav_plain_node` this reduces the crux `ValidPotentialPlain Pval` to a
  statement about `(a, nl, m, Sg) ∈ ℕ³ × ℝ` — no more trees.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar
import R3Cert.PlainFormula
import R3Cert.Plainify
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialClassify

namespace R3Cert

open Real

theorem cavSum_nil : cavSum ([] : List Branch) = 0 := rfl

theorem cavSum_cons (b : Branch) (l : List Branch) : cavSum (b :: l) = cav b + cavSum l := rfl

/-- A generic (non-arm, non-leaf) plain child never sits on the `Pval` special points: single
    non-leaf child case (`1/3 < cav < 1/2`). -/
theorem Pval_cav_generic_one (c' : ℕ) (z : Branch) (r : List Branch) :
    Pval (cav (Branch.node 0 [Branch.node c' (z :: r)]))
      = (11 / 50) * max 0 (cav (Branch.node 0 [Branch.node c' (z :: r)]) - T0) := by
  refine Pval_struct _ (ne_of_gt (cav_one_generic_gt_third c' z r)) (ne_of_lt ?_)
  exact cav_cons_lt_one 0 _ _

/-- ... and the two-or-more-children case (`cav < 1/3`). -/
theorem Pval_cav_generic_two (x y : Branch) (rest : List Branch) :
    Pval (cav (Branch.node 0 (x :: y :: rest)))
      = (11 / 50) * max 0 (cav (Branch.node 0 (x :: y :: rest)) - T0) := by
  refine Pval_struct _ (ne_of_lt (cav_two_lt_third 0 x y rest)) (ne_of_lt ?_)
  exact cav_cons_lt_one 0 _ _

/-- The generic-child fold step: absorb one `(y − T0)₊` into the running positive part. -/
theorem fold_step (Sg y : ℝ) (m : ℕ) :
    (11 / 50) * max 0 (Sg + y - ((m : ℝ) + 1) * T0)
      ≤ (11 / 50) * max 0 (y - T0) + (11 / 50) * max 0 (Sg - (m : ℝ) * T0) := by
  have heq : Sg + y - ((m : ℝ) + 1) * T0 = (y - T0) + (Sg - (m : ℝ) * T0) := by ring
  rw [heq]
  linarith [posPart_add_le (y - T0) (Sg - (m : ℝ) * T0)]

/-- **The classification reduction.**  Any plain child list is described, for the purposes of the
    super-solution, by four numbers `(a, nl, m, Sg)`. -/
theorem classify_reduce (ch : List Branch) (hch : IsPlainList ch) :
    ∃ (a nl m : ℕ) (Sg : ℝ),
      (ch.length : ℝ) = (a : ℝ) + nl + m ∧
      cavSum ch = (a : ℝ) / 3 + nl + Sg ∧
      0 ≤ Sg ∧ Sg ≤ (m : ℝ) / 2 ∧
      (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval + (11 / 50) * max 0 (Sg - (m : ℝ) * T0)
        ≤ ((ch.map (fun b => Pval (cav b))).sum) := by
  induction ch with
  | nil =>
    refine ⟨0, 0, 0, 0, by simp, by rw [cavSum_nil]; norm_num, le_refl 0, by norm_num, ?_⟩
    rw [List.map_nil, List.sum_nil]
    simp
  | cons b rest ih =>
    obtain ⟨hb, hrest⟩ := hch
    obtain ⟨a, nl, m, Sg, hlen, hsum, hSg0, hSgh, hPle⟩ := ih hrest
    obtain ⟨c₀, ch₀⟩ := b
    obtain ⟨hc₀, hch₀⟩ := hb
    subst hc₀
    cases ch₀ with
    | nil =>
      -- LEAF child: cav = 1, Pval = Lval
      refine ⟨a, nl + 1, m, Sg, ?_, ?_, hSg0, hSgh, ?_⟩
      · rw [List.length_cons]; push_cast; linarith [hlen]
      · rw [cavSum_cons, cav_leaf, hsum]; push_cast; ring
      · rw [List.map_cons, List.sum_cons, cav_leaf, Pval_one]; push_cast
        linarith [hPle]
    | cons x xs =>
      cases xs with
      | nil =>
        -- single child [x]
        obtain ⟨cx, chx⟩ := x
        obtain ⟨hcx, _hchx⟩ := hch₀.1
        subst hcx
        cases chx with
        | nil =>
          -- ARM child: cav = 1/3, Pval = -omegaVal
          have hcavb : cav (Branch.node 0 [Branch.node 0 []]) = 1 / 3 := cav_arm
          refine ⟨a + 1, nl, m, Sg, ?_, ?_, hSg0, hSgh, ?_⟩
          · rw [List.length_cons]; push_cast; linarith [hlen]
          · rw [cavSum_cons, hcavb, hsum]; push_cast; ring
          · rw [List.map_cons, List.sum_cons, hcavb, Pval_third]; push_cast
            linarith [hPle]
        | cons z r =>
          -- GENERIC child, single non-leaf: 1/3 < cav < 1/2
          have hyh : cav (Branch.node 0 [Branch.node 0 (z :: r)]) < 1 / 2 :=
            cav_cons_lt_half 0 _ _
          have hyp : 0 < cav (Branch.node 0 [Branch.node 0 (z :: r)]) := cav_pos _
          have hPv := Pval_cav_generic_one 0 z r
          refine ⟨a, nl, m + 1, Sg + cav (Branch.node 0 [Branch.node 0 (z :: r)]), ?_, ?_,
            by linarith, ?_, ?_⟩
          · rw [List.length_cons]; push_cast; linarith [hlen]
          · rw [cavSum_cons, hsum]; push_cast; ring
          · push_cast; linarith [hSgh, hyh]
          · rw [List.map_cons, List.sum_cons, hPv]; push_cast
            linarith [hPle, fold_step Sg (cav (Branch.node 0 [Branch.node 0 (z :: r)])) m]
      | cons w t =>
        -- GENERIC child, two or more children: cav < 1/3
        have hyh : cav (Branch.node 0 (x :: w :: t)) < 1 / 2 := cav_cons_lt_half 0 _ _
        have hyp : 0 < cav (Branch.node 0 (x :: w :: t)) := cav_pos _
        have hPv := Pval_cav_generic_two x w t
        refine ⟨a, nl, m + 1, Sg + cav (Branch.node 0 (x :: w :: t)), ?_, ?_,
          by linarith, ?_, ?_⟩
        · rw [List.length_cons]; push_cast; linarith [hlen]
        · rw [cavSum_cons, hsum]; push_cast; ring
        · push_cast; linarith [hSgh, hyh]
        · rw [List.map_cons, List.sum_cons, hPv]; push_cast
          linarith [hPle, fold_step Sg (cav (Branch.node 0 (x :: w :: t))) m]

end R3Cert
