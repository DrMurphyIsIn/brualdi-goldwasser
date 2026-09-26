/-
  Bridge STEP 3f (= STEP4C_DESIGN item (iii-b), combinatorial half): the realized edge lists
  satisfy the `isEdgeEnum_liftEdges` hypotheses.

  KEY INVARIANT (`EdgeShape`): every edge emitted by `rEdges` has the shape `(a, j :: a, w)` --
  the child endpoint is the parent address with one index consed on.  Consequences:
  * `realize_hloop`  -- no loops (lengths differ);
  * `realize_keys`   -- unordered-key uniqueness: the cross-orientation case is impossible by
    length (`e.1 = jf :: je :: e.1`), and the same-orientation case reduces to the child
    endpoint, which DETERMINES the edge by `childNodup`;
  * `realize_nodup`  -- from `childNodup` via `Nodup.of_map`.
  `childNodup` (the child endpoints of `realize t` are pairwise distinct) is the one real
  induction: root-level children are `i :: a` with strictly increasing indices; subtree edges
  have strictly longer child endpoints; distinct subtrees have distinct level-`|a|+1`
  suffixes (the existing address-suffix machinery of `BridgeStep3`).

  What remains of item (iii) after this file is the DEGREE computation (`hw`) for the
  `litHub` realizations, and the final composition (`BridgeStep4e`).

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep3e

namespace R3Cert
namespace Step3

/-! ### The edge-shape invariant -/

mutual
theorem rEdges_shape (a : List ℕ) (t : RTree) :
    ∀ e ∈ rEdges a t, ∃ j, e.2.1 = j :: e.1 := by
  cases t with
  | node cs =>
    rw [rEdges]
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact rRoot_shape a 0 cs e h
    · exact rSub_shape a 0 cs e h
theorem rRoot_shape (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    ∀ e ∈ rRoot a i cs, ∃ j, e.2.1 = j :: e.1 := by
  cases cs with
  | nil => rw [rRoot]; intro e he; simp at he
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    rw [rRoot]
    intro e he
    rcases List.mem_cons.mp he with h | h
    · subst h; exact ⟨i, rfl⟩
    · exact rRoot_shape a (i + 1) rest e h
theorem rSub_shape (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    ∀ e ∈ rSub a i cs, ∃ j, e.2.1 = j :: e.1 := by
  cases cs with
  | nil => rw [rSub]; intro e he; simp at he
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    rw [rSub]
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact rEdges_shape (i :: a) c e h
    · exact rSub_shape a (i + 1) rest e h
end

/-! ### Index lower bounds -/

theorem rRoot_child_eq (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), ∀ f ∈ rRoot a j cs, ∃ k, j ≤ k ∧ f.2.1 = k :: a := by
  induction cs with
  | nil => intro j f hf; rw [rRoot] at hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro j f hf
    rw [rRoot] at hf
    rcases List.mem_cons.mp hf with h | h
    · subst h; exact ⟨j, le_refl j, rfl⟩
    · obtain ⟨k, hk, hkeq⟩ := ih (j + 1) f h
      exact ⟨k, by omega, hkeq⟩

theorem rSub_parent_suffix (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ (j : ℕ), ∀ f ∈ rSub a j cs, ∃ k, j ≤ k ∧ (k :: a) <:+ f.1 := by
  induction cs with
  | nil => intro j f hf; rw [rSub] at hf; simp at hf
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro j f hf
    rw [rSub] at hf
    rcases List.mem_append.mp hf with h | h
    · exact ⟨j, le_refl j, (rEdges_allSuffix (j :: a) c f h).1⟩
    · obtain ⟨k, hk, hks⟩ := ih (j + 1) f h
      exact ⟨k, by omega, hks⟩

/-! ### The child endpoints are pairwise distinct -/

theorem rRoot_childNodup (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ (i : ℕ), ((rRoot a i cs).map (fun e => e.2.1)).Nodup := by
  induction cs with
  | nil => intro i; rw [rRoot]; simp
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro i
    rw [rRoot, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (i + 1)⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨f, hf, hfx⟩ := hmem
    obtain ⟨k, hk, hkeq⟩ := rRoot_child_eq a rest (i + 1) f hf
    rw [hkeq] at hfx
    simp only [List.cons.injEq] at hfx
    obtain ⟨hki, -⟩ := hfx
    omega

mutual
theorem rEdges_childNodup (a : List ℕ) (t : RTree) :
    ((rEdges a t).map (fun e => e.2.1)).Nodup := by
  cases t with
  | node cs =>
    rw [rEdges, List.map_append]
    refine List.Nodup.append (rRoot_childNodup a cs 0) (rSub_childNodup a 0 cs) ?_
    intro x hx1 hx2
    rw [List.mem_map] at hx1 hx2
    obtain ⟨f, hf, rfl⟩ := hx1
    obtain ⟨g, hg, hgx⟩ := hx2
    obtain ⟨k, -, hk⟩ := rRoot_child_eq a cs 0 f hf
    obtain ⟨k', -, hks⟩ := rSub_parent_suffix a cs 0 g hg
    obtain ⟨jg, hjg⟩ := rSub_shape a 0 cs g hg
    have h1 : f.2.1.length = a.length + 1 := by rw [hk]; simp
    have h2 : a.length + 1 ≤ g.1.length := by
      have := hks.length_le
      simpa using this
    have h3 : g.2.1.length = g.1.length + 1 := by rw [hjg]; simp
    rw [hgx] at h3
    omega
theorem rSub_childNodup (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    ((rSub a i cs).map (fun e => e.2.1)).Nodup := by
  cases cs with
  | nil => rw [rSub]; simp
  | cons p rest =>
    obtain ⟨w, c⟩ := p
    rw [rSub, List.map_append]
    refine List.Nodup.append (rEdges_childNodup (i :: a) c)
      (rSub_childNodup a (i + 1) rest) ?_
    intro x hx1 hx2
    rw [List.mem_map] at hx1 hx2
    obtain ⟨f, hf, rfl⟩ := hx1
    obtain ⟨g, hg, hgx⟩ := hx2
    have hfs : (i :: a) <:+ f.2.1 := (rEdges_allSuffix (i :: a) c f hf).2
    obtain ⟨k, hk, hks⟩ := rSub_parent_suffix a rest (i + 1) g hg
    obtain ⟨jg, hjg⟩ := rSub_shape a (i + 1) rest g hg
    have hgs : (k :: a) <:+ g.2.1 := by
      rw [hjg]
      exact hks.trans (List.suffix_cons jg g.1)
    rw [hgx] at hgs
    have heq : (i :: a) = (k :: a) := suffix_eq_of_length hfs hgs (by simp)
    simp only [List.cons.injEq] at heq
    obtain ⟨hik, -⟩ := heq
    omega
end

/-! ### The three `isEdgeEnum_liftEdges` hypotheses, at the `realize` level -/

theorem realize_childNodup (t : RTree) : ((realize t).map (fun e => e.2.1)).Nodup := by
  rw [realize]; exact rEdges_childNodup [] t

theorem realize_shape (t : RTree) : ∀ e ∈ realize t, ∃ j, e.2.1 = j :: e.1 := by
  rw [realize]; exact rEdges_shape [] t

/-- **`hnodup`**: the realized edge list is duplicate-free. -/
theorem realize_nodup (t : RTree) : (realize t).Nodup :=
  List.Nodup.of_map _ (realize_childNodup t)

/-- **`hloop`**: no realized edge is a loop. -/
theorem realize_hloop (t : RTree) : ∀ e ∈ realize t, e.1 ≠ e.2.1 := by
  intro e he heq
  obtain ⟨j, hj⟩ := realize_shape t e he
  rw [← heq] at hj
  have hlen := congrArg List.length hj
  simp only [List.length_cons] at hlen
  omega

/-- **`hkeys`**: an unordered key determines the realized edge.  Same orientation: the child
    endpoint determines the edge (`childNodup`); cross orientation: impossible by length. -/
theorem realize_keys (t : RTree) : ∀ e ∈ realize t, ∀ f ∈ realize t,
    (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e := by
  intro e he f hf hor
  rcases hor with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact List.inj_on_of_nodup_map (realize_childNodup t) hf he h2
  · exfalso
    obtain ⟨je, hje⟩ := realize_shape t e he
    obtain ⟨jf, hjf⟩ := realize_shape t f hf
    rw [h2, h1, hje] at hjf
    have hlen := congrArg List.length hjf
    simp only [List.length_cons] at hlen
    omega

end Step3
end R3Cert
