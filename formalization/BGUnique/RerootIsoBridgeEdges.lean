import Mathlib
import BGUnique.RerootIsoComplete
import R3Cert.R47Tree

/-!
The edges of the realization `realize (dtRealize t)`.

`realize` writes the address of child `k` of a vertex at address `a` as `k :: a`, so a realized
address is the REVERSE of a root-first address of `RerootIso`.  The edges of `realize (dtRealize t)`
are exactly the pairs `(p.reverse, (p ++ [k]).reverse)` with `p ++ [k]` a valid address of `t`.
-/

namespace R3Cert
namespace RerootIso

open R3Cert.Step3

/-! ### Membership in the root and subtree edge lists -/

theorem mem_rRoot {a : List ℕ} {e : List ℕ × List ℕ × ℝ} :
    ∀ (i : ℕ) (L : List (ℝ × RTree)),
      e ∈ rRoot a i L ↔ ∃ j, ∃ h : j < L.length, e = (a, (i + j) :: a, L[j].1)
  | i, [] => by rw [rRoot]; simp
  | i, (w, c) :: rest => by
    rw [rRoot, List.mem_cons, mem_rRoot (i + 1) rest]
    constructor
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · refine ⟨j + 1, by simpa using hj, ?_⟩
        simp only [List.getElem_cons_succ, show i + 1 + j = i + (j + 1) by omega]
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | zero => left; simp
      | succ j =>
        right
        refine ⟨j, by simpa using hj, ?_⟩
        simp only [List.getElem_cons_succ, show i + (j + 1) = i + 1 + j by omega]

theorem mem_rSub {a : List ℕ} {e : List ℕ × List ℕ × ℝ} :
    ∀ (i : ℕ) (L : List (ℝ × RTree)),
      e ∈ rSub a i L ↔ ∃ j, ∃ h : j < L.length, e ∈ rEdges ((i + j) :: a) L[j].2
  | i, [] => by rw [rSub]; simp
  | i, (w, c) :: rest => by
    rw [rSub, List.mem_append, mem_rSub (i + 1) rest]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · refine ⟨j + 1, by simpa using hj, ?_⟩
        simp only [List.getElem_cons_succ]
        rwa [show i + (j + 1) = i + 1 + j by omega]
    · rintro ⟨j, hj, h⟩
      cases j with
      | zero => left; simpa using h
      | succ j =>
        right
        refine ⟨j, by simpa using hj, ?_⟩
        simp only [List.getElem_cons_succ] at h
        rwa [show i + 1 + j = i + (j + 1) by omega]

theorem rEdges_node (a : List ℕ) (L : List (ℝ × RTree)) :
    rEdges a (RTree.node L) = rRoot a 0 L ++ rSub a 0 L := by
  rw [rEdges]

/-! ### The children of a realization -/

theorem dtChildren_getElem (d : ℕ) (cs : List UTree) (j : ℕ) (h : j < (dtChildren d cs).length) :
    ((dtChildren d cs)[j]).2 = dtSub (cs[j]'(by rwa [dtChildren_length] at h)) := by
  induction cs generalizing j with
  | nil => simp [dtChildren_nil] at h
  | cons K rest ih =>
    simp only [dtChildren_cons] at h ⊢
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem_cons_succ]
      exact ih j (by simpa using h)

/-! ### The edge characterization -/

/-- Every realized edge joins a valid address to one of its children (reversed, after the base). -/
theorem rEdges_sound : ∀ (n : ℕ) (cs : List UTree), usize (UTree.node cs) ≤ n → ∀ (d : ℕ) (a : List ℕ)
    (e : List ℕ × List ℕ × ℝ), e ∈ rEdges a (RTree.node (dtChildren d cs)) →
      ∃ p k, Valid (UTree.node cs) (p ++ [k]) ∧ e.1 = p.reverse ++ a ∧ e.2.1 = k :: (p.reverse ++ a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro cs hn d a e he
    rw [rEdges_node, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨j, hj, rfl⟩ := (mem_rRoot 0 _).mp he
      rw [dtChildren_length] at hj
      refine ⟨[], j, ?_, by simp, by simp⟩
      exact valid_cons.mpr ⟨hj, valid_nil _⟩
    · obtain ⟨j, hj, he⟩ := (mem_rSub 0 _).mp he
      have hj' : j < cs.length := by rwa [dtChildren_length] at hj
      rw [dtChildren_getElem] at he
      rcases hc : cs[j] with ⟨ds⟩
      rw [hc, dtSub_node] at he
      have hlt : usize (UTree.node ds) < n := by
        have := usize_child_lt hj'; rw [hc] at this; omega
      obtain ⟨p, k, hv, h1, h2⟩ := ih _ hlt ds le_rfl _ _ e he
      refine ⟨j :: p, k, ?_, ?_, ?_⟩
      · rw [List.cons_append]
        exact valid_cons.mpr ⟨hj', by rw [hc]; exact hv⟩
      · rw [h1]; simp
      · rw [h2]; simp

/-- Every child edge of a valid address is realized. -/
theorem rEdges_complete : ∀ (p : List ℕ) (k : ℕ) (cs : List UTree) (d : ℕ) (a : List ℕ),
    Valid (UTree.node cs) (p ++ [k]) →
      ∃ e ∈ rEdges a (RTree.node (dtChildren d cs)), e.1 = p.reverse ++ a ∧ e.2.1 = k :: (p.reverse ++ a)
  | [], k, cs, d, a, hv => by
    obtain ⟨hk, -⟩ := valid_cons.mp hv
    refine ⟨(a, (0 + k) :: a, ((dtChildren d cs)[k]'(by rwa [dtChildren_length])).1), ?_, by simp, by simp⟩
    rw [rEdges_node, List.mem_append]
    exact Or.inl ((mem_rRoot 0 _).mpr ⟨k, by rwa [dtChildren_length], rfl⟩)
  | j :: q, k, cs, d, a, hv => by
    rw [List.cons_append] at hv
    obtain ⟨hj, hv⟩ := valid_cons.mp hv
    rcases hc : cs[j] with ⟨ds⟩
    rw [hc] at hv
    obtain ⟨e, he, h1, h2⟩ := rEdges_complete q k ds (ds.length + 1) (j :: a) hv
    refine ⟨e, ?_, ?_, ?_⟩
    · rw [rEdges_node, List.mem_append]
      right
      refine (mem_rSub 0 _).mpr ⟨j, by rwa [dtChildren_length], ?_⟩
      rw [dtChildren_getElem]
      simp only [hc, dtSub_node, zero_add]
      exact he
    · rw [h1]; simp
    · rw [h2]; simp

end RerootIso
end R3Cert
