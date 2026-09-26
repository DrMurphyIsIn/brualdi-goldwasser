/-
  R4-R7 campaign, PHASE 2a3: the degree-parameterized hub-node assembly.

  The core lemma `Ztot_hubNode` computes the partition function of a hub node -- arms, own
  cherries, and an arbitrary further child block -- for ANY full degree `d`, via
  `Matched_factor` and the P2a2 toolkit.  Instantiating `d` at the internal degree gives the
  chain recursion; at the root child-count it gives `Aobj` of a backbone (P2a4).  Also:
  `tailU` equation lemmas for `backboneU` (the match-in-def), the generic `mem_dtChildren`
  and `Popen_dtChildren`.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47HubForms

namespace R3Cert
namespace Step3

open RTree

/-! ### `backboneU` equation lemmas -/

/-- The chain tail as a child list. -/
def tailU : List Hub → List UTree
  | [] => []
  | h :: t => [backboneU (h :: t)]

theorem backboneU_eq (arms : List ℕ) (c : ℕ) (rest : List Hub) :
    backboneU ((arms, c) :: rest)
      = UTree.node (arms.map armU ++ List.replicate c cherryU ++ tailU rest) := by
  cases rest with
  | nil => rfl
  | cons h t => rfl

/-! ### Generic `dtChildren` membership and product -/

theorem mem_dtChildren {d : ℕ} {ch : List UTree} {p : ℝ × RTree} :
    p ∈ dtChildren d ch →
      ∃ K ∈ ch, p.1 = 1 / ((d : ℝ) * (udeg K : ℝ)) ∧ p.2 = dtSub K := by
  induction ch with
  | nil => intro hp; rw [dtChildren_nil] at hp; exact absurd hp (by simp)
  | cons K rest ih =>
    intro hp
    rw [dtChildren_cons] at hp
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact ⟨K, List.mem_cons.mpr (Or.inl rfl), rfl, rfl⟩
    · obtain ⟨K', hK', hK'1, hK'2⟩ := ih h
      exact ⟨K', List.mem_cons.mpr (Or.inr hK'), hK'1, hK'2⟩

theorem Popen_dtChildren (d : ℕ) (ch : List UTree) :
    Popen (dtChildren d ch) = (ch.map (fun K => Ztot (dtSub K))).prod := by
  induction ch with
  | nil => rw [dtChildren_nil, Popen, List.map_nil, List.prod_nil]
  | cons K rest ih =>
    rw [dtChildren_cons, Popen_cons, ih, List.map_cons, List.prod_cons]

/-! ### The degree-parameterized hub-node assembly -/

/-- **The hub-node partition function** for any full degree `d`: arms + own cherries + an
    arbitrary further child block `ts` (the chain tail, or nothing). -/
theorem Ztot_hubNode (d : ℕ) (hd : 0 < d) (arms : List ℕ) (c : ℕ) (ts : List UTree)
    (hts : ∀ K ∈ ts, 0 < Ztot (dtSub K)) :
    Ztot (RTree.node (dtChildren d (arms.map armU ++ List.replicate c cherryU ++ ts)))
      = (((arms.map armU).map (fun K => Ztot (dtSub K))).prod * (3 / 2) ^ c
          * (ts.map (fun K => Ztot (dtSub K))).prod)
        * (1 + ((arms.map (fun j : ℕ => 3 / ((d : ℝ) * (4 * (j : ℝ) + 3)))).sum
            + (c : ℝ) * (1 / (3 * (d : ℝ)))
            + ((dtChildren d ts).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum)) := by
  have hne : ∀ p ∈ dtChildren d (arms.map armU ++ List.replicate c cherryU ++ ts),
      Ztot p.2 ≠ 0 := by
    intro p hp
    obtain ⟨K, hK, -, hp2⟩ := mem_dtChildren hp
    rw [hp2]
    rcases List.mem_append.mp hK with hK' | hKts
    · rcases List.mem_append.mp hK' with hKa | hKc
      · obtain ⟨j, -, hj⟩ := List.mem_map.mp hKa
        rw [← hj]
        exact (Ztot_dtSub_armU_pos j).ne'
      · have hKch : K = cherryU := List.eq_of_mem_replicate hKc
        rw [hKch, Ztot_dtSub_cherryU]
        norm_num
    · exact (hts K hKts).ne'
  rw [Ztot, Matched_factor _ hne, dtChildren_append, dtChildren_append,
    Popen_append, Popen_append, Popen_dtChildren, Popen_dtChildren, Popen_dtChildren,
    List.map_append, List.map_append, List.sum_append, List.sum_append,
    sum_wQ_arms d hd arms, sum_wQ_cherries d hd c]
  have hcherry : ((List.replicate c cherryU).map (fun K => Ztot (dtSub K))).prod
      = (3 / 2) ^ c := by
    rw [List.map_replicate, Ztot_dtSub_cherryU, List.prod_replicate]
  rw [hcherry]
  ring

end Step3
end R3Cert
