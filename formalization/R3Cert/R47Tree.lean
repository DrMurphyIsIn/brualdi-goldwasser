/-
  R4-R7 campaign, PHASE 1: the tree objects and the machine-checked objective.

  `UTree` = bare rooted trees (the rewrite layer's objects).  `dtRealize` equips a tree
  with its TRUE-degree weights (root degree = child count; internal degree = child count
  + 1; each edge weighted `1/(d * d')`) -- the `GoodTree` convention of the bridge.  The
  objective of the whole R4-R7 layer is

      `Aobj t := Ztot (dtRealize t)`

  a pure rational recursion; the P1 capstone `pi_utree` machine-checks that this IS the
  real quantity -- the Laplacian permanent ratio of the realized SimpleGraph -- for EVERY
  rooted tree, by instantiating the (already generic) bridge machinery: `realize_weights`
  + `isEdgeEnum_liftEdges` + `pi_eq_msum` + `msum_liftEdges` + `Ztot_eq_msum` +
  `aGraph_realize_isAcyclic`.  No permanent ever needs to be touched again in P2-P7.

  Scope note (campaign doc): `Aobj` is defined on ROOTED trees; root-invariance (the
  unrooted objective) is deferred to the P2 design.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.BridgeStep4j

namespace R3Cert
namespace Step3

open RTree

/-! ### Bare rooted trees -/

/-- A bare rooted tree: the R4-R7 rewrite layer's object. -/
inductive UTree where
  | node : List UTree → UTree

/-- Degree of a NON-ROOT node: its children plus the parent edge. -/
def udeg : UTree → ℕ
  | .node cs => cs.length + 1

theorem udeg_node (cs : List UTree) : udeg (UTree.node cs) = cs.length + 1 := by
  rw [udeg]

/-! ### The true-degree realization -/

mutual
/-- Realize a NON-ROOT subtree (its own degree is `udeg`). -/
noncomputable def dtSub : UTree → RTree
  | .node cs => RTree.node (dtChildren (cs.length + 1) cs)
/-- The weighted children of a node of full degree `d`. -/
noncomputable def dtChildren : ℕ → List UTree → List (ℝ × RTree)
  | _, [] => []
  | d, K :: rest => (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K) :: dtChildren d rest
end

/-- Realize the ROOT (true degree = child count, no parent edge). -/
noncomputable def dtRealize : UTree → RTree
  | .node cs => RTree.node (dtChildren cs.length cs)

theorem dtSub_node (cs : List UTree) :
    dtSub (UTree.node cs) = RTree.node (dtChildren (cs.length + 1) cs) := by
  rw [dtSub]

theorem dtRealize_node (cs : List UTree) :
    dtRealize (UTree.node cs) = RTree.node (dtChildren cs.length cs) := by
  rw [dtRealize]

theorem dtChildren_nil (d : ℕ) : dtChildren d [] = [] := by rw [dtChildren]

theorem dtChildren_cons (d : ℕ) (K : UTree) (rest : List UTree) :
    dtChildren d (K :: rest)
      = (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K) :: dtChildren d rest := by
  rw [dtChildren]

theorem dtChildren_length (d : ℕ) (ch : List UTree) :
    (dtChildren d ch).length = ch.length := by
  induction ch with
  | nil => rw [dtChildren_nil]; rfl
  | cons K rest ih => rw [dtChildren_cons, List.length_cons, List.length_cons, ih]

/-- The realized child count of a non-root node is its degree minus the parent edge. -/
theorem childCount_dtSub_succ (K : UTree) : childCount (dtSub K) + 1 = udeg K := by
  cases K with
  | node cs =>
    rw [dtSub_node, childCount, dtChildren_length, udeg_node]

/-! ### The realization follows the `GoodTree` convention -/

mutual
theorem dtSub_good : ∀ K : UTree, GoodTree (udeg K) (dtSub K)
  | .node cs => by
    rw [dtSub_node, udeg_node]
    refine GoodTree.node _ _ ?_ ?_
    · intro p hp
      exact (dtChildren_good (cs.length + 1) cs p hp).1
    · intro p hp
      exact (dtChildren_good (cs.length + 1) cs p hp).2
theorem dtChildren_good : ∀ (d : ℕ) (ch : List UTree), ∀ p ∈ dtChildren d ch,
    p.1 = 1 / ((d : ℝ) * ((childCount p.2 : ℝ) + 1)) ∧ GoodTree (childCount p.2 + 1) p.2
  | d, [], p, hp => by
    rw [dtChildren_nil] at hp
    exact absurd hp (by simp)
  | d, K :: rest, p, hp => by
    rw [dtChildren_cons] at hp
    rcases List.mem_cons.mp hp with h | h
    · subst h
      have hcast : ((udeg K : ℝ)) = (childCount (dtSub K) : ℝ) + 1 := by
        exact_mod_cast (childCount_dtSub_succ K).symm
      constructor
      · show 1 / ((d : ℝ) * (udeg K : ℝ))
          = 1 / ((d : ℝ) * ((childCount (dtSub K) : ℝ) + 1))
        rw [hcast]
      · show GoodTree (childCount (dtSub K) + 1) (dtSub K)
        rw [childCount_dtSub_succ K]
        exact dtSub_good K
    · exact dtChildren_good d rest p h
end

/-- **The root realization is `GoodTree` at its own child count** (true root). -/
theorem dtRealize_good : ∀ t : UTree, GoodTree (childCount (dtRealize t)) (dtRealize t)
  | .node cs => by
    rw [dtRealize_node, childCount, dtChildren_length]
    refine GoodTree.node _ _ ?_ ?_
    · intro p hp
      exact (dtChildren_good cs.length cs p hp).1
    · intro p hp
      exact (dtChildren_good cs.length cs p hp).2

/-! ### The objective, and the P1 capstone -/

/-- **The R4-R7 objective**: the raw matching partition function of the true-degree
    realization.  A pure rational recursion. -/
noncomputable def Aobj (t : UTree) : ℝ := Ztot (dtRealize t)

theorem dt_hw (t : UTree) :
    ∀ q ∈ liftEdges (realize (dtRealize t)), q.2.2
      = 1 / (((aGraph (realize (dtRealize t))).degree q.1 : ℝ)
          * ((aGraph (realize (dtRealize t))).degree q.2.1 : ℝ)) := by
  intro q hq
  obtain ⟨e, heE, h1, h2, h3⟩ := of_mem_liftEdges hq
  have hdeg1 : (aGraph (realize (dtRealize t))).degree q.1
      = (realize (dtRealize t)).countP (touchB e.1) := by
    rw [degree_eq_card_touching _ (realize_hloop _) (realize_keys _),
      card_touching_eq_countP _ (realize_nodup _), h1]
  have hdeg2 : (aGraph (realize (dtRealize t))).degree q.2.1
      = (realize (dtRealize t)).countP (touchB e.2.1) := by
    rw [degree_eq_card_touching _ (realize_hloop _) (realize_keys _),
      card_touching_eq_countP _ (realize_nodup _), h2]
  rw [h3, hdeg1, hdeg2]
  exact realize_weights (dtRealize t) (childCount (dtRealize t)) (dtRealize_good t) rfl
    e heE

theorem dt_isEdgeEnum (t : UTree) :
    IsEdgeEnum (aGraph (realize (dtRealize t))) (liftEdges (realize (dtRealize t))) :=
  isEdgeEnum_liftEdges _ (realize_nodup _) (realize_hloop _) (realize_keys _) (dt_hw t)

/-- **P1 CAPSTONE: `Aobj` IS the Laplacian permanent ratio of the real tree graph, for
    EVERY rooted tree.**  The whole rewrite layer may now work in the `Ztot` recursion. -/
theorem pi_utree (t : UTree) :
    (lapl (aGraph (realize (dtRealize t)))).permanent
        / (∏ v, ((aGraph (realize (dtRealize t))).degree v : ℝ))
      = Aobj t := by
  rw [pi_eq_msum _ (aGraph_realize_isAcyclic _)
      (aGraph_degree_ne _ (realize_hloop _) (realize_keys _)) (dt_isEdgeEnum t),
    msum_liftEdges, ← Ztot_eq_msum]
  rfl

end Step3
end R3Cert
