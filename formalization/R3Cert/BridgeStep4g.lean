/-
  Bridge STEP 4g: the GOOD-TREE weight invariant.

  The construction degrees of the literal trees are exactly the touching counts (4f); this
  file packages the WEIGHT side: `GoodTree d t` says every child edge of `t` carries the
  weight `1/(d * (childCount child + 1))` -- the parent's full degree times the child's full
  degree (its children plus its parent edge) -- recursively.  Then:

  * `litRealize_good`  -- `GoodTree (dB K) (litRealize K)` (the branch realization follows
    the convention: `childCount (litRealize K') + 1 = dB K'`, cherries have degree 2, cherry
    leaves degree 1);
  * `litHub_good`      -- `GoodTree (c + ch.length) (litHub c ch)` (the TRUE root: its degree
    is its child count, no parent edge);
  * `rEdges_count_notSuffix` -- an emission is blind to addresses outside its suffix cone
    (the last isolation lemma needed by the induction).

  The final piece (4h) is the induction: `GoodTree` + the 4f counts give, for every edge of
  the realized list, `w = 1/(count(parent) * count(child))` -- the `hw` hypothesis of
  `isEdgeEnum_liftEdges` -- and then the composed real-graph statement.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4d
import R3Cert.BridgeStep4f

namespace R3Cert
namespace Step3

open RTree

/-! ### The weight convention -/

/-- Every child edge of `t` carries `1/(d * (childCount child + 1))`, recursively; `d` is
    this node's full degree in the ambient tree.  (The weight condition and the recursive
    condition are separate premises: the kernel rejects a recursive occurrence nested in
    `And`.) -/
inductive GoodTree : ℕ → RTree → Prop
  | node (d : ℕ) (cs : List (ℝ × RTree))
      (hwt : ∀ p ∈ cs, p.1 = 1 / ((d : ℝ) * ((childCount p.2 : ℝ) + 1)))
      (hrec : ∀ p ∈ cs, GoodTree (childCount p.2 + 1) p.2) :
      GoodTree d (RTree.node cs)

theorem GoodTree.members {d : ℕ} {cs : List (ℝ × RTree)} (h : GoodTree d (RTree.node cs)) :
    ∀ p ∈ cs, p.1 = 1 / ((d : ℝ) * ((childCount p.2 : ℝ) + 1))
      ∧ GoodTree (childCount p.2 + 1) p.2 := by
  cases h with
  | node _ _ hwt hrec => exact fun p hp => ⟨hwt p hp, hrec p hp⟩

theorem goodTree_leaf (d : ℕ) : GoodTree d (RTree.node []) :=
  GoodTree.node d [] (by intro p hp; simp at hp) (by intro p hp; simp at hp)

theorem childCount_cherryMid : childCount cherryMid = 1 := by
  simp [cherryMid, childCount]

theorem goodTree_cherryMid : GoodTree 2 cherryMid := by
  refine GoodTree.node 2 [(1 / 2, RTree.node [])] ?_ ?_
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    show (1 / 2 : ℝ) = 1 / (((2 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 1))
    norm_num
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact goodTree_leaf _

/-! ### The literal realizations follow the convention -/

theorem litChildren_length (d : ℕ) (ch : List Branch) :
    (litChildren d ch).length = ch.length := by
  induction ch with
  | nil => rw [litChildren_nil]; rfl
  | cons K rest ih => rw [litChildren_cons, List.length_cons, List.length_cons, ih]

/-- The literal child count is the construction degree minus the parent edge. -/
theorem childCount_litRealize_succ (K : Branch) :
    childCount (litRealize K) + 1 = dB K := by
  cases K with
  | node c ch =>
    rw [litRealize_node, childCount, dB_node, List.length_append, List.length_replicate,
      litChildren_length]
    omega

/-- Full-pair version of `mem_litChildren`. -/
theorem mem_litChildren_full {d : ℕ} {ch : List Branch} {p : ℝ × RTree} :
    p ∈ litChildren d ch → ∃ K ∈ ch, p = (1 / ((d : ℝ) * (dB K : ℝ)), litRealize K) := by
  induction ch with
  | nil => intro hp; rw [litChildren_nil] at hp; exact absurd hp (by simp)
  | cons K rest ih =>
    intro hp
    rw [litChildren_cons] at hp
    rcases List.mem_cons.mp hp with h | h
    · exact ⟨K, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨K', hK', hK'2⟩ := ih h
      exact ⟨K', List.mem_cons.mpr (Or.inr hK'), hK'2⟩

mutual
theorem litRealize_good : ∀ K : Branch, GoodTree (dB K) (litRealize K)
  | .node c ch => by
    rw [litRealize_node]
    refine GoodTree.node _ _ ?_ ?_
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · have hpe : p = litCherry (dB (Branch.node c ch)) := List.eq_of_mem_replicate h
        subst hpe
        show 1 / ((dB (Branch.node c ch) : ℝ) * 2)
          = 1 / ((dB (Branch.node c ch) : ℝ) * (((1 : ℕ) : ℝ) + 1))
        norm_num
      · exact (litChildren_good (dB (Branch.node c ch)) ch p h).1
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · have hpe : p = litCherry (dB (Branch.node c ch)) := List.eq_of_mem_replicate h
        subst hpe
        exact goodTree_cherryMid
      · exact (litChildren_good (dB (Branch.node c ch)) ch p h).2
theorem litChildren_good : ∀ (d : ℕ) (ch : List Branch), ∀ p ∈ litChildren d ch,
    p.1 = 1 / ((d : ℝ) * ((childCount p.2 : ℝ) + 1)) ∧ GoodTree (childCount p.2 + 1) p.2
  | d, [], p, hp => by
    rw [litChildren_nil] at hp
    exact absurd hp (by simp)
  | d, K :: rest, p, hp => by
    rw [litChildren_cons] at hp
    rcases List.mem_cons.mp hp with h | h
    · subst h
      have hcast : ((dB K : ℝ)) = (childCount (litRealize K) : ℝ) + 1 := by
        exact_mod_cast (childCount_litRealize_succ K).symm
      constructor
      · show 1 / ((d : ℝ) * (dB K : ℝ))
          = 1 / ((d : ℝ) * ((childCount (litRealize K) : ℝ) + 1))
        rw [hcast]
      · show GoodTree (childCount (litRealize K) + 1) (litRealize K)
        rw [childCount_litRealize_succ K]
        exact litRealize_good K
    · exact litChildren_good d rest p h
end

/-- **The literal hub follows the convention with its TRUE root degree** (child count, no
    parent edge). -/
theorem litHub_good (c : ℕ) (ch : List Branch) :
    GoodTree (c + ch.length) (litHub c ch) := by
  rw [litHub]
  refine GoodTree.node _ _ ?_ ?_
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · have hpe : p = litCherry (c + ch.length) := List.eq_of_mem_replicate h
      subst hpe
      show 1 / (((c + ch.length : ℕ) : ℝ) * 2)
        = 1 / (((c + ch.length : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1))
      norm_num
    · exact (litChildren_good (c + ch.length) ch p h).1
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · have hpe : p = litCherry (c + ch.length) := List.eq_of_mem_replicate h
      subst hpe
      exact goodTree_cherryMid
    · exact (litChildren_good (c + ch.length) ch p h).2

/-! ### The last isolation lemma -/

/-- An emission is blind to any address outside its suffix cone. -/
theorem rEdges_count_notSuffix (b : List ℕ) (c : RTree) (x : List ℕ) (hx : ¬ b <:+ x) :
    (rEdges b c).countP (touchB x) = 0 := by
  rw [List.countP_eq_zero]
  intro f hf
  obtain ⟨h1, h2⟩ := rEdges_allSuffix b c f hf
  rw [touchB_eq_true]
  rintro (h | h)
  · exact hx (h ▸ h1)
  · exact hx (h ▸ h2)

end Step3
end R3Cert
