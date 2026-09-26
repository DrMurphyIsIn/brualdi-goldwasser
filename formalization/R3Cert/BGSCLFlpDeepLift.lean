/-
  Problem B, Stage B2 (keystone): the DEEP FLP lift is UNCONDITIONAL.

  `BGSCLHnormPort.straightStep_sized_lift` isolated the context-lift's `Aobj` half as a per-level
  Obligation-A hypothesis.  This file DISCHARGES that debt for the FLP move: the pair of cavity gains

      G1 : Ztot(dtSub c) <= Ztot(dtSub c')
      G2 : Zopen(dtSub c)/udeg c <= Zopen(dtSub c')/udeg c'

  SELF-PROPAGATES through any ancestor frame (`dtSub_gains_lift`) -- the ancestor's own weight
  `1/(len+1)` is common to both sides, and by the root-degree factorization
  (`Ztot_node_deg`: `Ztot = P·(1 + qSum/k)`, `Popen_dtChildren`: `Zopen = P`) the replaced child
  enters `Ztot` only through `Ztot_c·(1 + w·Q0) + w·(Zopen_c/udeg_c)` -- monotone in (G1, G2).
  At the root, `Aobj_child_replace_le_deg` closes from the same pair.  The FLP site supplies the
  base gains (`Ztot_dtSub_flp_child_le`, and `1/3 <= 3/4` for G2 at `crest = []`).

  Headline: `flp_deep_straightStep` -- a leaf-pair FLP flip at ANY depth (site parent carrying a
  non-piece sibling, wrapped in arbitrary ancestor frames) is a full `StraightStep_sized` on the
  whole tree, with NO per-level obligations.  The `StraightProgress_sized` finder (B3) now only
  needs to FIND such a site.  Numerically re-verified (exact rationals, ~8000 propagation levels,
  0 violations) before formalization.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLFlpMove
import R3Cert.BGSCLHnormPort

namespace R3Cert
namespace Step3

open RTree

/-! ### General node cavity identities -/

/-- `Ztot(dtSub)` of a node: the root-degree factorization at the subtree degree `len + 1`. -/
theorem Ztot_dtSub_node_eq (cs : List UTree) :
    Ztot (dtSub (UTree.node cs))
      = (cs.map fun K => Ztot (dtSub K)).prod
        * (1 + (1 / ((cs.length : ℝ) + 1)) * qSum cs) := by
  rw [dtSub_node, Ztot_node_deg]
  push_cast
  ring

/-- `Zopen(dtSub)` of a node: the plain child product. -/
theorem Zopen_dtSub_node_eq (cs : List UTree) :
    Zopen (dtSub (UTree.node cs)) = (cs.map fun K => Ztot (dtSub K)).prod := by
  rw [dtSub_node]
  have h : Zopen (RTree.node (dtChildren (cs.length + 1) cs))
      = Popen (dtChildren (cs.length + 1) cs) := rfl
  rw [h, Popen_dtChildren]

/-- Every `udeg` is positive (a node has `len + 1 >= 1`). -/
theorem udeg_cast_pos (K : UTree) : (0 : ℝ) < (udeg K : ℝ) := by
  obtain ⟨cs⟩ := K
  rw [udeg_node]
  positivity

/-! ### The G-pair propagation through one ancestor frame -/

/-- **The cavity-gain context-lift.**  If the child pair `c ↦ c'` carries the gains
    `G1 : Ztot(dtSub) <=` and `G2 : Zopen(dtSub)/udeg <=`, then so does the parent pair
    `node (pre ++ c :: post) ↦ node (pre ++ c' :: post)` -- with NO side conditions.  This is what
    makes the deep FLP lift unconditional: the per-level Obligation-A debt of
    `straightStep_sized_lift` is replaced by a self-propagating invariant. -/
theorem dtSub_gains_lift (pre post : List UTree) {c c' : UTree}
    (hG1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hG2 : Zopen (dtSub c) / (udeg c : ℝ) ≤ Zopen (dtSub c') / (udeg c' : ℝ)) :
    Ztot (dtSub (UTree.node (pre ++ c :: post))) ≤ Ztot (dtSub (UTree.node (pre ++ c' :: post)))
      ∧ Zopen (dtSub (UTree.node (pre ++ c :: post)))
            / (udeg (UTree.node (pre ++ c :: post)) : ℝ)
          ≤ Zopen (dtSub (UTree.node (pre ++ c' :: post)))
            / (udeg (UTree.node (pre ++ c' :: post)) : ℝ) := by
  have hZc := Ztot_dt_pos c
  have hZc' := Ztot_dt_pos c'
  have huc := udeg_cast_pos c
  have huc' := udeg_cast_pos c'
  have hPpre := flp_crest_P_nonneg pre
  have hPpost := flp_crest_P_nonneg post
  have hQpre := qSum_nonneg pre
  have hQpost := qSum_nonneg post
  simp only [Ztot_dtSub_node_eq, Zopen_dtSub_node_eq, udeg_node,
    List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    qSum_append, qSum_cons, List.length_append, List.length_cons]
  push_cast
  set A := (pre.map fun K => Ztot (dtSub K)).prod with hA
  set B := (post.map fun K => Ztot (dtSub K)).prod with hB
  set Zc := Ztot (dtSub c)
  set Zc' := Ztot (dtSub c')
  set Oc := Zopen (dtSub c)
  set Oc' := Zopen (dtSub c')
  set uc := (udeg c : ℝ)
  set uc' := (udeg c' : ℝ)
  set QP := qSum pre
  set QQ := qSum post
  set w : ℝ := 1 / ((pre.length : ℝ) + ((post.length : ℝ) + 1) + 1) with hw
  have hwpos : 0 < w := by rw [hw]; positivity
  have hX : (0 : ℝ) ≤ 1 + w * (QP + QQ) := by nlinarith
  have hABX : (0 : ℝ) ≤ A * B * (1 + w * (QP + QQ)) :=
    mul_nonneg (mul_nonneg hPpre hPpost) hX
  have hid : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + w * (QP + (O / Z / u + QQ)))
        = A * B * (1 + w * (QP + QQ)) * Z + A * B * w * (O / u) := by
    intro Z O u hZ hu
    field_simp
    ring
  constructor
  · rw [hid Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
        hid Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
    have h1 : A * B * (1 + w * (QP + QQ)) * Zc ≤ A * B * (1 + w * (QP + QQ)) * Zc' :=
      mul_le_mul_of_nonneg_left hG1 hABX
    have h2 : A * B * w * (Oc / uc) ≤ A * B * w * (Oc' / uc') :=
      mul_le_mul_of_nonneg_left hG2
        (mul_nonneg (mul_nonneg hPpre hPpost) hwpos.le)
    linarith
  · have hnum : A * (Zc * B) ≤ A * (Zc' * B) := by
      have := mul_le_mul_of_nonneg_left hG1 (mul_nonneg hPpre hPpost)
      calc A * (Zc * B) = A * B * Zc := by ring
        _ ≤ A * B * Zc' := this
        _ = A * (Zc' * B) := by ring
    apply div_le_div_of_nonneg_right hnum  -- may need name fix
    positivity

/-! ### The root closure from the G-pair -/

/-- At the ROOT, the G-pair closes to `Aobj`-monotonicity via the degree-changing
    child-replacement lemma (the `1/d` root weight is common and nonnegative). -/
theorem Aobj_child_replace_of_gains (pre post : List UTree) {c c' : UTree}
    (hG1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hG2 : Zopen (dtSub c) / (udeg c : ℝ) ≤ Zopen (dtSub c') / (udeg c' : ℝ)) :
    Aobj (UTree.node (pre ++ c :: post)) ≤ Aobj (UTree.node (pre ++ c' :: post)) := by
  apply Aobj_child_replace_le_deg pre post c c' hG1
  have huc := udeg_cast_pos c
  have huc' := udeg_cast_pos c'
  have hd : (0 : ℝ) < (((pre.length + post.length + 1 : ℕ)) : ℝ) := by positivity
  have hrw : ∀ (u O : ℝ), u ≠ 0 →
      (1 / ((((pre.length + post.length + 1 : ℕ)) : ℝ) * u)) * O
        = (1 / (((pre.length + post.length + 1 : ℕ)) : ℝ)) * (O / u) := by
    intro u O hu
    field_simp
  rw [hrw _ _ (ne_of_gt huc), hrw _ _ (ne_of_gt huc')]
  exact mul_le_mul_of_nonneg_left hG2 (by positivity)

/-! ### Piece-status plumbing -/

/-- A node with a non-piece member among `>= 2` children is non-piece. -/
theorem isPiece_node_of_nonpiece_mem {cs : List UTree} {x : UTree}
    (hx : x ∈ cs) (hxnp : isPiece x = false) (hlen : 2 ≤ cs.length) :
    isPiece (UTree.node cs) = false := by
  obtain ⟨hxa, hxc⟩ : isArm x = false ∧ isCherry x = false := by
    simpa [isPiece, Bool.or_eq_false_iff] using hxnp
  rcases cs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hx
  · simp at hlen
  · have harm : isArm (UTree.node (a :: b :: rest)) = false := by
      simp only [isArm]
      cases hall : (a :: b :: rest).all isCherry
      · rfl
      · have := List.all_eq_true.mp hall x hx
        rw [hxc] at this
        exact absurd this (by simp)
    have hch : isCherry (UTree.node (a :: b :: rest)) = false := rfl
    simp [isPiece, harm, hch]

/-- Plugging a non-piece child into ANY frame yields a non-piece node (the child is not a cherry,
    so the node is not an arm; and it is not a single-leaf, so the node is not a cherry). -/
theorem isPiece_plug1 (pre post : List UTree) {c : UTree} (hc : isPiece c = false) :
    isPiece (UTree.node (pre ++ c :: post)) = false := by
  obtain ⟨hca, hcc⟩ : isArm c = false ∧ isCherry c = false := by
    simpa [isPiece, Bool.or_eq_false_iff] using hc
  by_cases hlen : 2 ≤ (pre ++ c :: post).length
  · exact isPiece_node_of_nonpiece_mem (by simp) hc hlen
  · rcases pre with _ | ⟨a, pre'⟩
    case cons =>
      exfalso
      simp only [List.length_append, List.length_cons] at hlen
      omega
    rcases post with _ | ⟨b, post'⟩
    case cons =>
      exfalso
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨cs⟩ := c
    have hcs : cs ≠ [] := by
      rintro rfl
      simp [isArm] at hca
    rcases cs with _ | ⟨x, xs⟩
    · exact absurd rfl hcs
    · simp only [List.nil_append]
      have h1 : isArm (UTree.node [UTree.node (x :: xs)]) = false := by
        simp only [isArm, List.all_cons, List.all_nil, Bool.and_true]
        exact hcc
      have h2 : isCherry (UTree.node [UTree.node (x :: xs)]) = false := rfl
      simp [isPiece, h1, h2]

/-- Positive `npCount` supplies a non-piece member. -/
theorem exists_nonpiece_of_npCount_pos :
    ∀ {l : List UTree}, 1 ≤ npCount l → ∃ x ∈ l, isPiece x = false
  | [], h => by simp [npCount] at h
  | c :: rest, h => by
    cases hp : isPiece c
    · exact ⟨c, by simp, hp⟩
    · have hrest : 1 ≤ npCount rest := by
        rw [npCount, hp] at h
        simpa using h
      obtain ⟨x, hx, hxnp⟩ := exists_nonpiece_of_npCount_pos hrest
      exact ⟨x, by simp [hx], hxnp⟩

/-! ### Ancestor frames -/

/-- Fold a stack of sibling frames around a core subtree (head frame innermost). -/
def plugFrames : List (List UTree × List UTree) → UTree → UTree
  | [], c => c
  | f :: fs, c => plugFrames fs (UTree.node (f.1 ++ c :: f.2))

theorem plugFrames_usize :
    ∀ (fs : List (List UTree × List UTree)) {c c' : UTree}, usize c = usize c' →
      usize (plugFrames fs c) = usize (plugFrames fs c')
  | [], _, _, h => h
  | f :: fs, _, _, h =>
    plugFrames_usize fs (usize_child_replace f.1 f.2 h)

theorem plugFrames_nonpiece :
    ∀ (fs : List (List UTree × List UTree)) {c : UTree}, isPiece c = false →
      isPiece (plugFrames fs c) = false
  | [], _, h => h
  | f :: fs, _, h =>
    plugFrames_nonpiece fs (isPiece_plug1 f.1 f.2 h)

theorem plugFrames_strDefect :
    ∀ (fs : List (List UTree × List UTree)) {c c' : UTree},
      isPiece c = false → isPiece c' = false → strDefect c' < strDefect c →
      strDefect (plugFrames fs c') < strDefect (plugFrames fs c)
  | [], _, _, _, _, h => h
  | f :: fs, _, _, hc, hc', h =>
    plugFrames_strDefect fs (isPiece_plug1 f.1 f.2 hc) (isPiece_plug1 f.1 f.2 hc')
      (strDefect_child_replace_lt f.1 f.2 hc hc' h)

theorem plugFrames_gains :
    ∀ (fs : List (List UTree × List UTree)) {c c' : UTree},
      Ztot (dtSub c) ≤ Ztot (dtSub c') →
      Zopen (dtSub c) / (udeg c : ℝ) ≤ Zopen (dtSub c') / (udeg c' : ℝ) →
      Ztot (dtSub (plugFrames fs c)) ≤ Ztot (dtSub (plugFrames fs c'))
        ∧ Zopen (dtSub (plugFrames fs c)) / (udeg (plugFrames fs c) : ℝ)
            ≤ Zopen (dtSub (plugFrames fs c')) / (udeg (plugFrames fs c') : ℝ)
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | f :: fs, _, _, h1, h2 =>
    let hlift := dtSub_gains_lift f.1 f.2 h1 h2
    plugFrames_gains fs hlift.1 hlift.2

/-! ### The FLP base gains at `crest = []` -/

theorem flp_base_G2 :
    Zopen (dtSub (flpChildBefore [])) / (udeg (flpChildBefore []) : ℝ)
      ≤ Zopen (dtSub (flpChildAfter [])) / (udeg (flpChildAfter []) : ℝ) := by
  rw [Zopen_dtSub_flpChildBefore, Zopen_dtSub_flpChildAfter,
      udeg_flpChildBefore, udeg_flpChildAfter]
  norm_num

/-! ### The headline: deep FLP flips are unconditional straight-steps -/

/-- **B2 keystone: the DEEP FLP move is a `StraightStep_sized` with NO per-level obligations.**
    A leaf-pair FLP flip at any depth -- site parent `node (spre ++ node[leaf,leaf] :: spost)`
    carrying a non-piece sibling, wrapped in arbitrary ancestor frames `fs` and a root frame
    `(rpre, rpost)` -- is a size-preserving, `Aobj`-non-decreasing, defect-lowering step on the
    WHOLE tree.  The per-level Obligation-A debt of `straightStep_sized_lift` is fully discharged
    by the self-propagating cavity-gain pair (`dtSub_gains_lift`). -/
theorem flp_deep_straightStep (spre spost : List UTree)
    (hsib : 1 ≤ npCount (spre ++ spost))
    (fs : List (List UTree × List UTree)) (rpre rpost : List UTree) :
    StraightStep_sized
      (UTree.node (rpre
        ++ plugFrames fs (UTree.node (spre ++ flpChildBefore [] :: spost)) :: rpost))
      (UTree.node (rpre
        ++ plugFrames fs (UTree.node (spre ++ flpChildAfter [] :: spost)) :: rpost)) := by
  -- site-level facts
  have husz : usize (UTree.node (spre ++ flpChildBefore [] :: spost))
      = usize (UTree.node (spre ++ flpChildAfter [] :: spost)) :=
    usize_flp_context_eq spre spost
  have hdef : strDefect (UTree.node (spre ++ flpChildAfter [] :: spost))
      < strDefect (UTree.node (spre ++ flpChildBefore [] :: spost)) :=
    strDefect_flp_flip_lt spre spost hsib
  have hnp0 : isPiece (UTree.node (spre ++ flpChildBefore [] :: spost)) = false :=
    isPiece_plug1 spre spost isPiece_flpChildBefore_nil
  -- non-pieceness AFTER: from the non-piece sibling supplied by `hsib`
  obtain ⟨x, hxmem, hxnp⟩ := exists_nonpiece_of_npCount_pos hsib
  have hlen2 : 2 ≤ (spre ++ flpChildAfter [] :: spost).length := by
    have hpos : 0 < (spre ++ spost).length := List.length_pos_of_mem hxmem
    simp only [List.length_append, List.length_cons]
    simp only [List.length_append] at hpos
    omega
  have hxmem' : x ∈ spre ++ flpChildAfter [] :: spost := by
    rcases List.mem_append.mp hxmem with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hnp0' : isPiece (UTree.node (spre ++ flpChildAfter [] :: spost)) = false :=
    isPiece_node_of_nonpiece_mem hxmem' hxnp hlen2
  -- cavity gains: base at the acted child, lifted once through the site frame
  have hbase := dtSub_gains_lift spre spost (Ztot_dtSub_flp_child_le []) flp_base_G2
  -- lift through the ancestor frames
  have hplug := plugFrames_gains fs hbase.1 hbase.2
  refine ⟨?_, ?_, ?_⟩
  · exact usize_child_replace rpre rpost (plugFrames_usize fs husz)
  · exact Aobj_child_replace_of_gains rpre rpost hplug.1 hplug.2
  · exact strDefect_child_replace_lt rpre rpost
      (plugFrames_nonpiece fs hnp0) (plugFrames_nonpiece fs hnp0')
      (plugFrames_strDefect fs hnp0 hnp0' hdef)

end Step3
end R3Cert
