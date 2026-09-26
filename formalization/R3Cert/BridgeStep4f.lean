/-
  Bridge STEP 4f: the COUNT CORE for the construction-degree computation.

  `degree_eq_card_touching` (4e) reduces graph degrees to touching-edge counts.  This file
  provides the counting toolkit over the `rEdges/rRoot/rSub` emitters:

  * `card_touching_eq_countP` -- the Finset card is a `List.countP` (Nodup lists);
  * `rEdges_countRoot` -- the emitted list touches its own root exactly `childCount t` times
    (every root edge has `e.1 = a`; subtree edges are strictly longer);
  * `count_head_child` -- the head child's address is touched exactly `1 + childCount c`
    times (its parent edge + its own root edges) -- THE degree identity for child vertices;
  * zero-count lemmas (`rRoot_count_child`, `rSub_count_child`, `rRoot_count_deep`,
    `rSub_count_other`) isolating each address to the emission that owns it.

  With these, the remaining work is the `litRealize`/`litHub` weight induction (each
  constructed weight `1/(d * d')` matches the counts) and the final composition.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4e

namespace R3Cert
namespace Step3

/-- Bool: edge `e` touches vertex `x`. -/
def touchB (x : List ℕ) (e : AEdge) : Bool := decide (e.1 = x) || decide (e.2.1 = x)

theorem touchB_eq_true {x : List ℕ} {e : AEdge} :
    touchB x e = true ↔ e.1 = x ∨ e.2.1 = x := by
  simp [touchB]

/-- The number of children of the root. -/
def childCount : RTree → ℕ
  | .node cs => cs.length

/-! ### The Finset card is a list count -/

theorem card_touching_eq_countP (E : List AEdge) (hnd : E.Nodup) (x : List ℕ) :
    (E.toFinset.filter (fun e => e.1 = x ∨ e.2.1 = x)).card = E.countP (touchB x) := by
  classical
  have h1 : E.toFinset.filter (fun e => e.1 = x ∨ e.2.1 = x)
      = (E.filter (touchB x)).toFinset := by
    ext e
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, touchB_eq_true]
  rw [h1, List.toFinset_card_of_nodup (hnd.filter _), List.countP_eq_length_filter]

/-! ### Root and child counts of the emitters -/

theorem rRoot_countRoot (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ i, (rRoot a i cs).countP (touchB a) = cs.length := by
  induction cs with
  | nil => intro i; rw [rRoot]; rfl
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    intro i
    have ht : touchB a (a, i :: a, w) = true := by simp [touchB]
    rw [rRoot, List.countP_cons, ih (i + 1), ht, if_pos rfl, List.length_cons]

theorem rSub_countRoot (a : List ℕ) (i : ℕ) (cs : List (ℝ × RTree)) :
    (rSub a i cs).countP (touchB a) = 0 := by
  rw [List.countP_eq_zero]
  intro f hf
  obtain ⟨h1, h2⟩ := rSub_endpoints_long a cs i f hf
  rw [touchB_eq_true]
  rintro (h | h)
  · rw [h] at h1; omega
  · rw [h] at h2; omega

/-- **The emitted list touches its own root exactly `childCount` times.** -/
theorem rEdges_countRoot (a : List ℕ) (t : RTree) :
    (rEdges a t).countP (touchB a) = childCount t := by
  cases t with
  | node cs =>
    rw [rEdges, List.countP_append, rRoot_countRoot a cs 0, rSub_countRoot a 0 cs, childCount]
    omega

/-! ### Zero counts away from the owning emission -/

theorem rRoot_count_child (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ i k, k < i → (rRoot a i cs).countP (touchB (k :: a)) = 0 := by
  intro i k hk
  rw [List.countP_eq_zero]
  intro f hf
  have hf1 : f.1 = a := rRoot_first a cs i f hf
  obtain ⟨j, hj, hjeq⟩ := rRoot_child_eq a cs i f hf
  rw [touchB_eq_true]
  rintro (h | h)
  · rw [hf1] at h
    have := congrArg List.length h
    simp only [List.length_cons] at this
    omega
  · rw [hjeq] at h
    simp only [List.cons.injEq] at h
    omega

theorem rSub_count_child (a : List ℕ) (cs : List (ℝ × RTree)) (k i : ℕ) (hki : k < i) :
    (rSub a i cs).countP (touchB (k :: a)) = 0 := by
  rw [List.countP_eq_zero]
  intro f hf
  have hc := rSub_no_touch a k cs i hki f hf
  unfold conflict at hc
  have hprops := of_decide_eq_false hc
  push_neg at hprops
  rw [touchB_eq_true]
  rintro (h | h)
  · exact hprops.2.1 h
  · exact hprops.2.2.2 h

theorem rRoot_count_deep (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ i x, a.length + 1 < x.length → (rRoot a i cs).countP (touchB x) = 0 := by
  intro i x hx
  rw [List.countP_eq_zero]
  intro f hf
  have hf1 : f.1 = a := rRoot_first a cs i f hf
  obtain ⟨k, -, hkeq⟩ := rRoot_child_eq a cs i f hf
  rw [touchB_eq_true]
  rintro (h | h)
  · rw [hf1] at h
    have := congrArg List.length h
    omega
  · rw [hkeq] at h
    have := congrArg List.length h
    simp only [List.length_cons] at this
    omega

theorem rSub_count_other (a : List ℕ) (cs : List (ℝ × RTree)) :
    ∀ i k x, k < i → (k :: a) <:+ x → (rSub a i cs).countP (touchB x) = 0 := by
  intro i k x hki hkx
  rw [List.countP_eq_zero]
  intro f hf
  obtain ⟨j, hj, hjs⟩ := rSub_parent_suffix a cs i f hf
  obtain ⟨m, hm⟩ := rSub_shape a i cs f hf
  have hjs2 : (j :: a) <:+ f.2.1 := by
    rw [hm]
    exact hjs.trans (List.suffix_cons m f.1)
  rw [touchB_eq_true]
  rintro (h | h)
  · rw [h] at hjs
    have heq : (k :: a) = (j :: a) := suffix_eq_of_length hkx hjs (by simp)
    simp only [List.cons.injEq] at heq
    omega
  · rw [h] at hjs2
    have heq : (k :: a) = (j :: a) := suffix_eq_of_length hkx hjs2 (by simp)
    simp only [List.cons.injEq] at heq
    omega

/-! ### The head-child degree identity -/

/-- **The head child's address is touched exactly `1 + childCount c` times** in its node's
    full emission: once by its parent edge, `childCount c` times by its own root edges. -/
theorem count_head_child (a : List ℕ) (i : ℕ) (w : ℝ) (c : RTree)
    (rest : List (ℝ × RTree)) :
    (rRoot a i ((w, c) :: rest) ++ rSub a i ((w, c) :: rest)).countP (touchB (i :: a))
      = 1 + childCount c := by
  have ht : touchB (i :: a) (a, i :: a, w) = true := by simp [touchB]
  rw [rRoot, rSub, List.cons_append, List.countP_cons, List.countP_append,
    List.countP_append, ht, if_pos rfl,
    rRoot_count_child a rest (i + 1) i (by omega),
    rEdges_countRoot (i :: a) c,
    rSub_count_child a rest i (i + 1) (by omega)]
  omega

end Step3
end R3Cert
