/-
  H2b -- the tree-induction WRAPPER around `cavity_recursion`.

  An inductive rooted tree with a real weight on each parent-child edge.  The weighted matching partition
  functions `Zopen` (root unmatched) and `Ztot` (all matchings) are defined by the standard rose-tree
  recursion -- division-free, so they are well-defined unconditionally:

    Zopen(node cs) = ∏_children Ztot(c)                                    (root unmatched ⇒ every child free)
    Ztot (node cs) = Zopen(node cs) + ∑_i w_i · Zopen(c_i) · ∏_{j≠i} Ztot(c_j)   (root unmatched, or matched to
                                                                                  child i whose root is open)

  The auxiliary list functions `Popen cs = ∏ Ztot(child)` and `Matched cs = ∑_i w_i Zopen(c_i) ∏_{j≠i} Ztot(c_j)`
  build the leave-one-out matched sum WITHOUT division (accumulating `w·Zopen·Popen + Ztot·Matched`).

  MAIN THEOREM `tree_cavity_recursion`: for every rooted tree whose child totals are nonzero, the node cavity
  ratio satisfies the recursion end-to-end:

    Zopen(node cs) / Ztot(node cs) = 1 / (1 + ∑_children w · (Zopen c / Ztot c)).

  Proof: `Matched cs = Popen cs · ∑ w·(Zopen/Ztot)` (list induction, `Matched_factor`), so
  `Ztot = Popen·(1 + S)` and the ratio collapses by `cavity_step` (Matching.lean).  This closes the H2b
  structural-induction wrapper: it is the per-node `cavity_recursion` identity realized on the actual inductive
  matching partition functions, applied at every node.
-/
import Mathlib
import R3Cert.Matching

namespace R3Cert

/-- A rooted tree with a real weight on each parent-child edge. -/
inductive RTree where
  | node : List (ℝ × RTree) → RTree

namespace RTree

/- `Zopen t` / `Ztot t` -- the matching partition functions of the rooted tree `t` (root unmatched / all
   matchings); `Popen cs` = `∏ Ztot(child)`, `Matched cs` = the leave-one-out matched sum (division-free). -/
mutual
  def Zopen : RTree → ℝ
    | .node cs => Popen cs
  def Ztot : RTree → ℝ
    | .node cs => Popen cs + Matched cs
  def Popen : List (ℝ × RTree) → ℝ
    | [] => 1
    | (_, c) :: rest => Ztot c * Popen rest
  def Matched : List (ℝ × RTree) → ℝ
    | [] => 0
    | (w, c) :: rest => w * Zopen c * Popen rest + Ztot c * Matched rest
end

/-- `Popen cs ≠ 0` when every child total is nonzero (product of nonzeros). -/
theorem Popen_ne_zero : ∀ (cs : List (ℝ × RTree)), (∀ p ∈ cs, Ztot p.2 ≠ 0) → Popen cs ≠ 0 := by
  intro cs
  induction cs with
  | nil => intro _; simp [Popen]
  | cons p rest ih =>
      intro hne
      obtain ⟨w, c⟩ := p
      have ht : Ztot c ≠ 0 := hne (w, c) (by simp)
      have hrest : ∀ q ∈ rest, Ztot q.2 ≠ 0 := fun q hq => hne q (List.mem_cons_of_mem _ hq)
      simp only [Popen]
      exact mul_ne_zero ht (ih hrest)

/-- **The matched-sum factorization** (list induction): `Matched cs = Popen cs · ∑_child w·(Zopen c / Ztot c)`
    whenever every child total is nonzero -- the leave-one-out sum equals the total product times the cavity
    sum.  This is the list-native form of the leave-one-out step in `cavity_recursion`. -/
theorem Matched_factor : ∀ (cs : List (ℝ × RTree)), (∀ p ∈ cs, Ztot p.2 ≠ 0) →
    Matched cs = Popen cs * (cs.map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum := by
  intro cs
  induction cs with
  | nil => intro _; simp [Matched, Popen]
  | cons p rest ih =>
      intro hne
      obtain ⟨w, c⟩ := p
      have ht : Ztot c ≠ 0 := hne (w, c) (by simp)
      have hrest : ∀ q ∈ rest, Ztot q.2 ≠ 0 := fun q hq => hne q (List.mem_cons_of_mem _ hq)
      simp only [Matched, Popen, List.map_cons, List.sum_cons]
      rw [ih hrest]
      field_simp

/-- **(H2b) the tree cavity recursion -- end to end (THEOREM, no `sorry`).**  For every rooted tree `node cs`
    all of whose child totals are nonzero, the node cavity ratio obeys the recursion
    `Zopen / Ztot = 1 / (1 + ∑_children w · (Zopen c / Ztot c))`.  This applies `cavity_recursion`'s identity at
    the node, realized on the inductive matching partition functions `Zopen`/`Ztot`; iterating it over the tree
    gives `π(T) = Σ_M ∏_{ij∈M} 1/(deg i deg j)` (H2). -/
theorem tree_cavity_recursion (cs : List (ℝ × RTree)) (hne : ∀ p ∈ cs, Ztot p.2 ≠ 0) :
    Zopen (node cs) / Ztot (node cs)
      = 1 / (1 + (cs.map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum) := by
  have hPne : Popen cs ≠ 0 := Popen_ne_zero cs hne
  have hM : Matched cs = Popen cs * (cs.map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum :=
    Matched_factor cs hne
  have hfac : Popen cs + Matched cs
      = Popen cs * (1 + (cs.map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum) := by
    rw [hM]; ring
  simp only [Zopen, Ztot]
  rw [hfac]
  exact cavity_step (Popen cs) _ hPne

end RTree

end R3Cert
