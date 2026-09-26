/-
  RealObligationA — Case A: the STRUCTURAL leaf-path-extension Aobj-increment identity.

  `BGSCLRealOblACaseA.lean` banked the sign fact `0 ≤ P·(n²+nQ+4Q)/(2(n+1)(n+2))`.  This file makes that
  atom LOAD-BEARING: it proves, in the exact cavity model (`R47Tree` / `R47RootRate`), that the leaf-path-
  extension move's ACTUAL `Aobj` increment EQUALS that closed form.

  The move (rooted so the acted node is the root, by `Aobj` root-invariance): a pendant leaf `w` is relocated
  onto a leaf sibling `v`, extending a path.  With `rest` the node's other children,

      before = node (leaf :: leaf :: rest)          -- the two leaves v, w
      after  = node (stem :: rest),  stem = node [leaf]   -- v extended into a stem carrying w

  Using the root-degree factorization `Aobj (node cs) = P(cs)·(1 + qSum(cs)/|cs|)` (`Ztot_node_deg`), and the
  concrete cavity values `Ztot(dtSub leaf)=1, qContrib(leaf)=1`, `Ztot(dtSub stem)=3/2, qContrib(stem)=1/3`,
  the increment is the exact rational identity (verified numerically in `telperion/scratch/a3_F2_closed.py`
  against 2000 random `rest` blocks, and here KERNEL-proved):

      Aobj(after) − Aobj(before)
        = P · (n² + n·Q + 4·Q) / (2·(n+1)·(n+2)),   P = ∏_{K∈rest} Ztot(dtSub K),  Q = qSum rest,  n = |rest|.

  Composed with `f2_aobj_increment_nonneg` (0 ≤ that form; `P ≥ 0`, `Q ≥ 0`, `n ≥ 0`) this gives the Case-A
  `Aobj`-monotonicity `Aobj(before) ≤ Aobj(after)` in the cavity model — the load-bearing `Aobj` clause of the
  leaf-path-extension straightening step (92% of defective trees, per the taxonomy sweep).

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47Tree
import R3Cert.R47Head
import R3Cert.R47RootRate
import R3Cert.BGSCLRealOblACaseA

namespace R3Cert
namespace Step3

open RTree

/-- The bare leaf `node []`. -/
def flpLeaf : UTree := UTree.node []
/-- The stem `node [leaf]` (a degree-2 path vertex) — the target leaf after path-extension. -/
def flpStem : UTree := UTree.node [flpLeaf]

theorem Ztot_dtSub_flpLeaf : Ztot (dtSub flpLeaf) = 1 := by
  rw [flpLeaf, dtSub_node, dtChildren_nil, Ztot, Popen, Matched]; norm_num
theorem Zopen_dtSub_flpLeaf : Zopen (dtSub flpLeaf) = 1 := by
  rw [flpLeaf, dtSub_node, dtChildren_nil, Zopen, Popen]
theorem udeg_flpLeaf : udeg flpLeaf = 1 := by simp [flpLeaf, udeg]

theorem udeg_flpStem : udeg flpStem = 2 := by simp [flpStem, udeg]
theorem Ztot_dtSub_flpStem : Ztot (dtSub flpStem) = 3 / 2 := by
  rw [flpStem, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched, Popen_cons, Popen, Ztot_dtSub_flpLeaf, Zopen_dtSub_flpLeaf,
    udeg_flpLeaf]
  norm_num
theorem Zopen_dtSub_flpStem : Zopen (dtSub flpStem) = 1 := by
  rw [flpStem, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Zopen, Popen_cons, Popen, Ztot_dtSub_flpLeaf]; norm_num

/-- `qSum` cons: the head child's dressed cavity plus the tail's `qSum`. -/
theorem qSum_cons (a : UTree) (cs : List UTree) :
    qSum (a :: cs) = Zopen (dtSub a) / Ztot (dtSub a) / (udeg a : ℝ) + qSum cs := by
  simp only [qSum, List.map_cons, List.sum_cons]

/-- `Aobj` as the root-degree factorization (corollary of `Ztot_node_deg` + `dtRealize_node`). -/
theorem Aobj_factor (cs : List UTree) :
    Aobj (UTree.node cs)
      = (cs.map fun K => Ztot (dtSub K)).prod * (1 + 1 / (cs.length : ℝ) * qSum cs) := by
  rw [Aobj, dtRealize_node, Ztot_node_deg]

/-- **The leaf-path-extension `Aobj`-increment identity** (Case A, the structural core):
    `Aobj(after) − Aobj(before) = P·(n²+nQ+4Q)/(2(n+1)(n+2))`, `P = ∏ Ztot(dtSub rest)`, `Q = qSum rest`,
    `n = |rest|`. -/
theorem f2_increment_identity (rest : List UTree) :
    Aobj (UTree.node (flpStem :: rest)) - Aobj (UTree.node (flpLeaf :: flpLeaf :: rest))
      = (rest.map fun K => Ztot (dtSub K)).prod
        * ((rest.length : ℝ) ^ 2 + (rest.length : ℝ) * qSum rest + 4 * qSum rest)
        / (2 * ((rest.length : ℝ) + 1) * ((rest.length : ℝ) + 2)) := by
  rw [Aobj_factor, Aobj_factor]
  simp only [List.map_cons, List.prod_cons, qSum_cons, Ztot_dtSub_flpStem, Ztot_dtSub_flpLeaf,
    Zopen_dtSub_flpStem, Zopen_dtSub_flpLeaf, udeg_flpStem, udeg_flpLeaf, List.length_cons,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hn1 : ((rest.length : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((rest.length : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **Case-A `Aobj`-monotonicity in the cavity model**: the leaf-path-extension does not decrease `Aobj`.
    Combines the increment identity with the banked sign certificate `f2_aobj_increment_nonneg`. -/
theorem f2_aobj_monotone (rest : List UTree) :
    Aobj (UTree.node (flpLeaf :: flpLeaf :: rest)) ≤ Aobj (UTree.node (flpStem :: rest)) := by
  have hid := f2_increment_identity rest
  have hP : 0 ≤ (rest.map fun K => Ztot (dtSub K)).prod := by
    apply List.prod_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨K, _, rfl⟩ := hx
    exact le_of_lt (Ztot_dt_pos K)
  have hQ : 0 ≤ qSum rest := qSum_nonneg rest
  have hn : 0 ≤ (rest.length : ℝ) := Nat.cast_nonneg _
  have hsign := R3Cert.BGSCL.f2_aobj_increment_nonneg
    (rest.map fun K => Ztot (dtSub K)).prod (qSum rest) (rest.length : ℝ) hP hQ hn
  linarith [hid, hsign]

end Step3
end R3Cert
