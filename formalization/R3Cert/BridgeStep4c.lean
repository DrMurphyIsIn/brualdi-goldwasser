/-
  Bridge STEP 4c (the raw-amplitude seam, items (i)+(ii) of STEP4C_DESIGN.md):
  `Phi` is a FINITE LOCAL product of raw matching cavities -- no second limit.

  The LITERAL realization `litRealize` expands cherries as genuine 2-paths (mid degree 2, leaf
  degree 1) and carries the RAW weights `1/(deg u * deg v)`, with the parent/hub edge counted in
  the root degree (`dB = n_ch + 1 + c`, exactly the DEC `d`).  Main results:

    * `q_lit_eq_d_cav`   :  Zopen/Ztot (litRealize b) = dB b * cav b        (the raw-cavity lemma:
      the cherry-folding is ONE LINE -- each expanded cherry edge contributes `1/(3d)` because the
      cherry mid has raw cavity `2/3`; the raw analogue of Step 2's `q_realize_eq_rho0`).
    * `Ztot_lit_eq_Wb`   :  Ztot (litRealize b) = Wb b                       (the amplitude-level
      folding, a PURE RATIONAL identity: `Wb b = Phi(b) * rhoB^{V(b)}` defined by the DEC node
      recursion with the `rhoB` factors stripped -- `ac * rhoB^(1+2c) = (3/2)^c (1 + c/(3d))`).
    * `logPhi_eq_log_Wb` :  logPhi b = log (Wb b) - Vb b * Lval              (the log-side link to
      the capstone `phi_le_one`), and the exponential form
      `exp_logPhi_mul_rhoB_pow : exp (logPhi b) * rhoB ^ Vb b = Ztot (litRealize b)`.

  So the DEC amplitude IS the raw literal-tree matching partition function, node by node; the
  "measured non-clean log_rhoB(pi/Phi) offsets" of BRIDGE_DESIGN.md were an artifact of comparing
  against finite trees whose ROOT lacks the phantom parent edge.  Exact-arithmetic witnesses:
  `raw_amplitude_seam.py` (S1: 486/486 branches every node; S2: 486/486, ground-truth cross-check
  error 0.0).

  Remaining for Step 4c after this file: item (iii) the `litEdges`/`IsEdgeEnum` instantiation
  (Ztot -> per L / prod deg via BridgeStep3d), and item (iv) the hub seam + `2/(p+1)` squeeze
  (`amplitude_bridge`).  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep2
import R3Cert.NearStar

namespace R3Cert

open RTree

/-! ### The literal degree and vertex count -/

/-- Root degree of a branch in the literal tree, phantom parent edge included:
    `d = n_ch + 1 + c` -- exactly the DEC `d`. -/
def dB : Branch → ℕ
  | .node c ch => ch.length + 1 + c

theorem dB_node (c : ℕ) (ch : List Branch) : dB (Branch.node c ch) = ch.length + 1 + c := rfl

theorem dB_pos (b : Branch) : 0 < dB b := by
  cases b with
  | node c ch => rw [dB_node]; omega

mutual
/-- Literal vertex count: the node, two vertices per cherry, and the children. -/
def Vb : Branch → ℕ
  | .node c ch => 1 + 2 * c + VbSum ch
def VbSum : List Branch → ℕ
  | [] => 0
  | K :: rest => Vb K + VbSum rest
end

/-! ### The literal cherry gadget -/

/-- The cherry mid vertex (degree 2) with its leaf (degree 1); mid-leaf raw weight `1/(2*1)`. -/
noncomputable def cherryMid : RTree := RTree.node [(1 / 2, RTree.node [])]

/-- A cherry as a child of a degree-`d` root: root-mid raw weight `1/(d*2)`. -/
noncomputable def litCherry (d : ℕ) : ℝ × RTree := (1 / ((d : ℝ) * 2), cherryMid)

theorem litCherry_eq (d : ℕ) : litCherry d = (1 / ((d : ℝ) * 2), cherryMid) := rfl

theorem Zopen_cherryMid : Zopen cherryMid = 1 := by
  norm_num [cherryMid, Zopen, Ztot, Popen, Matched]

theorem Ztot_cherryMid : Ztot cherryMid = 3 / 2 := by
  norm_num [cherryMid, Ztot, Zopen, Popen, Matched]

theorem Zopen_litCherry_snd (d : ℕ) : Zopen (litCherry d).2 = 1 := Zopen_cherryMid

theorem Ztot_litCherry_snd (d : ℕ) : Ztot (litCherry d).2 = 3 / 2 := Ztot_cherryMid

/-! ### The literal realization -/

mutual
/-- The literal (cherry-expanded, raw-weight) realization of a branch. -/
noncomputable def litRealize : Branch → RTree
  | .node c ch =>
      RTree.node (List.replicate c (litCherry (ch.length + 1 + c)) ++
        litChildren (ch.length + 1 + c) ch)
noncomputable def litChildren : ℕ → List Branch → List (ℝ × RTree)
  | _, [] => []
  | d, K :: rest => (1 / ((d : ℝ) * (dB K : ℝ)), litRealize K) :: litChildren d rest
end

theorem litRealize_node (c : ℕ) (ch : List Branch) :
    litRealize (Branch.node c ch)
      = RTree.node (List.replicate c (litCherry (ch.length + 1 + c)) ++
          litChildren (ch.length + 1 + c) ch) := by
  rw [litRealize]

theorem litChildren_nil (d : ℕ) : litChildren d [] = [] := by rw [litChildren]

theorem litChildren_cons (d : ℕ) (K : Branch) (rest : List Branch) :
    litChildren d (K :: rest)
      = (1 / ((d : ℝ) * (dB K : ℝ)), litRealize K) :: litChildren d rest := by
  rw [litChildren]

/-! ### List-level partition-function algebra (generic; reusable for the hub seam) -/

theorem Popen_cons (w : ℝ) (t : RTree) (rest : List (ℝ × RTree)) :
    Popen ((w, t) :: rest) = Ztot t * Popen rest := by rw [Popen]

theorem Matched_cons (w : ℝ) (t : RTree) (rest : List (ℝ × RTree)) :
    Matched ((w, t) :: rest) = w * Zopen t * Popen rest + Ztot t * Matched rest := by rw [Matched]

theorem Popen_append (l₁ l₂ : List (ℝ × RTree)) :
    Popen (l₁ ++ l₂) = Popen l₁ * Popen l₂ := by
  induction l₁ with
  | nil => simp [Popen]
  | cons p rest ih =>
      obtain ⟨w, t⟩ := p
      rw [List.cons_append, Popen_cons, Popen_cons, ih]
      ring

theorem Matched_append (l₁ l₂ : List (ℝ × RTree)) :
    Matched (l₁ ++ l₂) = Matched l₁ * Popen l₂ + Popen l₁ * Matched l₂ := by
  induction l₁ with
  | nil => simp [Matched, Popen]
  | cons p rest ih =>
      obtain ⟨w, t⟩ := p
      rw [List.cons_append, Matched_cons, Matched_cons, Popen_cons, Popen_append, ih]
      ring

/-! ### Closed forms over the replicated cherries -/

theorem Popen_cons_cherry (d : ℕ) (rest : List (ℝ × RTree)) :
    Popen (litCherry d :: rest) = (3 / 2) * Popen rest := by
  rw [litCherry_eq, Popen_cons, Ztot_cherryMid]

theorem Matched_cons_cherry (d : ℕ) (rest : List (ℝ × RTree)) :
    Matched (litCherry d :: rest)
      = 1 / ((d : ℝ) * 2) * Popen rest + (3 / 2) * Matched rest := by
  rw [litCherry_eq, Matched_cons, Zopen_cherryMid, Ztot_cherryMid]
  ring

theorem Popen_replicate_cherry (d c : ℕ) :
    Popen (List.replicate c (litCherry d)) = (3 / 2) ^ c := by
  induction c with
  | zero => rw [List.replicate_zero, Popen]; norm_num
  | succ n ih => rw [List.replicate_succ, Popen_cons_cherry, ih]; ring

theorem Matched_replicate_cherry (d c : ℕ) (hd : 0 < d) :
    Matched (List.replicate c (litCherry d)) = (3 / 2) ^ c * ((c : ℝ) / (3 * (d : ℝ))) := by
  have hdne : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  induction c with
  | zero => rw [List.replicate_zero, Matched]; norm_num
  | succ n ih =>
      rw [List.replicate_succ, Matched_cons_cherry, ih, Popen_replicate_cherry]
      push_cast
      field_simp [hdne]
      ring

/-! ### Positivity of the literal partition functions -/

mutual
theorem Zopen_lit_pos : ∀ b : Branch, 0 < Zopen (litRealize b)
  | .node c ch => by
    rw [litRealize_node, Zopen, Popen_append, Popen_replicate_cherry]
    have h32 : (0 : ℝ) < (3 / 2) ^ c := by positivity
    exact mul_pos h32 (Popen_litCh_pos (ch.length + 1 + c) ch)
theorem Ztot_lit_pos : ∀ b : Branch, 0 < Ztot (litRealize b)
  | .node c ch => by
    rw [litRealize_node, Ztot, Popen_append, Matched_append, Popen_replicate_cherry,
      Matched_replicate_cherry (ch.length + 1 + c) c (by omega)]
    have hP := Popen_litCh_pos (ch.length + 1 + c) ch
    have hM := Matched_litCh_nonneg (ch.length + 1 + c) ch
    have h32 : (0 : ℝ) < (3 / 2) ^ c := by positivity
    have hc : (0 : ℝ) ≤ (3 / 2) ^ c * ((c : ℝ) / (3 * ((ch.length + 1 + c : ℕ) : ℝ))) := by
      positivity
    have h1 := mul_pos h32 hP
    have h2 := mul_nonneg hc hP.le
    have h3 := mul_nonneg h32.le hM
    linarith
theorem Popen_litCh_pos : ∀ (d : ℕ) (ch : List Branch), 0 < Popen (litChildren d ch)
  | _, [] => by rw [litChildren_nil, Popen]; norm_num
  | d, K :: rest => by
    rw [litChildren_cons, Popen_cons]
    exact mul_pos (Ztot_lit_pos K) (Popen_litCh_pos d rest)
theorem Matched_litCh_nonneg : ∀ (d : ℕ) (ch : List Branch), 0 ≤ Matched (litChildren d ch)
  | _, [] => by simp [litChildren_nil, Matched]
  | d, K :: rest => by
    rw [litChildren_cons, Matched_cons]
    have hw : (0 : ℝ) ≤ 1 / ((d : ℝ) * (dB K : ℝ)) := by positivity
    have h1 : 0 ≤ 1 / ((d : ℝ) * (dB K : ℝ)) * Zopen (litRealize K) *
        Popen (litChildren d rest) :=
      mul_nonneg (mul_nonneg hw (Zopen_lit_pos K).le) (Popen_litCh_pos d rest).le
    have h2 : 0 ≤ Ztot (litRealize K) * Matched (litChildren d rest) :=
      mul_nonneg (Ztot_lit_pos K).le (Matched_litCh_nonneg d rest)
    linarith
end

theorem Ztot_lit_ne (b : Branch) : Ztot (litRealize b) ≠ 0 := (Ztot_lit_pos b).ne'

/-- Every element of `litChildren d ch` realizes some child `K ∈ ch`. -/
theorem mem_litChildren {d : ℕ} {ch : List Branch} {p : ℝ × RTree} :
    p ∈ litChildren d ch → ∃ K ∈ ch, p.2 = litRealize K := by
  induction ch with
  | nil => intro hp; rw [litChildren_nil] at hp; simp at hp
  | cons K rest ih =>
    intro hp
    rw [litChildren_cons] at hp
    rcases List.mem_cons.mp hp with h | h
    · exact ⟨K, List.mem_cons.mpr (Or.inl rfl), by rw [h]⟩
    · obtain ⟨K', hK', hK'2⟩ := ih h
      exact ⟨K', List.mem_cons.mpr (Or.inr hK'), hK'2⟩

theorem hne_litCh (d : ℕ) (ch : List Branch) :
    ∀ p ∈ litChildren d ch, Ztot p.2 ≠ 0 := by
  intro p hp
  obtain ⟨K, _, hK2⟩ := mem_litChildren hp
  rw [hK2]; exact Ztot_lit_ne K

theorem hne_lit (d c : ℕ) (ch : List Branch) :
    ∀ p ∈ List.replicate c (litCherry d) ++ litChildren d ch, Ztot p.2 ≠ 0 := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · rw [List.eq_of_mem_replicate h, Ztot_litCherry_snd]; norm_num
  · exact hne_litCh d ch p h

/-! ### (S1) The raw-cavity lemma: `Zopen/Ztot (litRealize b) = dB b * cav b` -/

/-- One expanded cherry contributes `1/(3d)` to the root cavity load: the mid's raw cavity is
    `2/3` and the root-mid weight is `1/(2d)`. -/
theorem cherry_term (d : ℕ) (hd : 0 < d) :
    (litCherry d).1 * (Zopen (litCherry d).2 / Ztot (litCherry d).2) = 1 / (3 * (d : ℝ)) := by
  have hdne : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Zopen_litCherry_snd, Ztot_litCherry_snd, litCherry_eq]
  field_simp [hdne]

mutual
theorem q_lit_eq_d_cav : ∀ b : Branch,
    Zopen (litRealize b) / Ztot (litRealize b) = (dB b : ℝ) * cav b
  | .node c ch => by
    have hdpos : 0 < ch.length + 1 + c := by omega
    have hsum : ((List.replicate c (litCherry (ch.length + 1 + c)) ++
        litChildren (ch.length + 1 + c) ch).map
          (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
        = (c : ℝ) * (1 / (3 * ((ch.length + 1 + c : ℕ) : ℝ)))
          + cavSum ch / ((ch.length + 1 + c : ℕ) : ℝ) := by
      simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
        nsmul_eq_mul]
      rw [cherry_term _ hdpos, litCh_sum _ ch hdpos]
    rw [litRealize_node, tree_cavity_recursion _ (hne_lit (ch.length + 1 + c) c ch), hsum,
      dB_node, cav_eq]
    push_cast
    have hd' : (0 : ℝ) < (ch.length : ℝ) + 1 + (c : ℝ) := by positivity
    have hstep : 1 + ((c : ℝ) * (1 / (3 * ((ch.length : ℝ) + 1 + (c : ℝ))))
          + cavSum ch / ((ch.length : ℝ) + 1 + (c : ℝ)))
        = (3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch)
          / (3 * ((ch.length : ℝ) + 1 + (c : ℝ))) := by
      field_simp [hd'.ne']
      ring
    rw [hstep, one_div_div]
    ring
theorem litCh_sum : ∀ (d : ℕ) (ch : List Branch), 0 < d →
    ((litChildren d ch).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
      = cavSum ch / (d : ℝ)
  | d, [], _ => by simp [litChildren_nil, cavSum]
  | d, K :: rest, hd => by
    have hsplit : ((litChildren d (K :: rest)).map
          (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
        = 1 / ((d : ℝ) * (dB K : ℝ)) * (Zopen (litRealize K) / Ztot (litRealize K))
          + ((litChildren d rest).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum := by
      rw [litChildren_cons]; simp
    rw [hsplit, q_lit_eq_d_cav K, litCh_sum d rest hd, cavSum]
    have hK : ((dB K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (dB_pos K).ne'
    have hd' : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    field_simp [hK, hd']
end

/-! ### (S2) The amplitude identity: `Ztot (litRealize b) = Wb b`, a pure rational fact -/

mutual
/-- `W(b) = Phi(b) * rhoB^{V(b)}`: the DEC amplitude with the `rhoB` normalization stripped
    (`ac * rhoB^(1+2c) = (3/2)^c * (1 + c/(3d))`), defined by the node recursion. -/
noncomputable def Wb : Branch → ℝ
  | .node c ch =>
      (3 / 2) ^ c * (1 + (c : ℝ) / (3 * ((ch.length : ℝ) + 1 + (c : ℝ))))
        * (1 + zc c ch.length * cavSum ch) * WbProd ch
noncomputable def WbProd : List Branch → ℝ
  | [] => 1
  | K :: rest => Wb K * WbProd rest
end

mutual
theorem Ztot_lit_eq_Wb : ∀ b : Branch, Ztot (litRealize b) = Wb b
  | .node c ch => by
    have hdpos : 0 < ch.length + 1 + c := by omega
    have hMk : Matched (litChildren (ch.length + 1 + c) ch)
        = WbProd ch * (cavSum ch / ((ch.length + 1 + c : ℕ) : ℝ)) := by
      rw [Matched_factor _ (hne_litCh (ch.length + 1 + c) ch), litCh_sum _ ch hdpos,
        Popen_litCh_eq]
    rw [litRealize_node, Ztot, Popen_append, Matched_append, Popen_replicate_cherry,
      Matched_replicate_cherry _ _ hdpos, Popen_litCh_eq, hMk, Wb, zc]
    push_cast
    have h1 : ((ch.length : ℝ) + 1 + (c : ℝ)) ≠ 0 := by positivity
    have h2 : (3 * ((ch.length : ℝ) + 1 + (c : ℝ)) + (c : ℝ)) ≠ 0 := by positivity
    field_simp [h1, h2]
    ring
theorem Popen_litCh_eq : ∀ (d : ℕ) (ch : List Branch), Popen (litChildren d ch) = WbProd ch
  | _, [] => by rw [litChildren_nil, Popen, WbProd]
  | d, K :: rest => by
    rw [litChildren_cons, Popen_cons, Ztot_lit_eq_Wb K, Popen_litCh_eq d rest, WbProd]
end

theorem Wb_pos (b : Branch) : 0 < Wb b := by
  rw [← Ztot_lit_eq_Wb b]; exact Ztot_lit_pos b

theorem WbProd_pos (ch : List Branch) : 0 < WbProd ch := by
  rw [← Popen_litCh_eq 1 ch]; exact Popen_litCh_pos 1 ch

/-- **The raw-cavity corollary in `Wb` form**: the literal open partition function. -/
theorem Zopen_lit_eq (b : Branch) :
    Zopen (litRealize b) = (dB b : ℝ) * cav b * Wb b := by
  have h := q_lit_eq_d_cav b
  rw [div_eq_iff (Ztot_lit_ne b)] at h
  rw [h, Ztot_lit_eq_Wb]

/-! ### The log-side link to the capstone -/

mutual
theorem logPhi_eq_log_Wb : ∀ b : Branch,
    logPhi b = Real.log (Wb b) - (Vb b : ℝ) * Lval
  | .node c ch => by
    have hA : (0 : ℝ) < (3 / 2) ^ c
        * (1 + (c : ℝ) / (3 * ((ch.length : ℝ) + 1 + (c : ℝ)))) := by positivity
    have hF : (0 : ℝ) < 1 + zc c ch.length * cavSum ch := by
      have := mul_nonneg (zc_pos c ch.length).le (cavSum_nonneg ch)
      linarith
    have hW := WbProd_pos ch
    have hlog_ac : Real.log (ac c ch.length)
        = Real.log ((3 / 2) ^ c * (1 + (c : ℝ) / (3 * ((ch.length : ℝ) + 1 + (c : ℝ)))))
          - ((1 + 2 * c : ℕ) : ℝ) * Lval := by
      rw [ac, Real.log_div (ne_of_gt hA) (ne_of_gt (pow_pos rhoB_pos _)), Real.log_pow,
        logRhoB]
    rw [logPhi, eroot, logPhiSum_eq_log_WbProd ch, Wb, hlog_ac,
      Real.log_mul (mul_pos hA hF).ne' (ne_of_gt hW),
      Real.log_mul (ne_of_gt hA) (ne_of_gt hF), Vb]
    push_cast
    ring
theorem logPhiSum_eq_log_WbProd : ∀ ch : List Branch,
    logPhiSum ch = Real.log (WbProd ch) - (VbSum ch : ℝ) * Lval
  | [] => by rw [logPhiSum, WbProd, VbSum]; simp
  | K :: rest => by
    rw [logPhiSum, WbProd, VbSum, logPhi_eq_log_Wb K, logPhiSum_eq_log_WbProd rest,
      Real.log_mul (Wb_pos K).ne' (WbProd_pos rest).ne']
    push_cast
    ring
end

/-- **THE LOCAL AMPLITUDE IDENTITY, exponential form**: the DEC amplitude of every branch IS its
    literal raw matching partition function -- `exp (logPhi b) * rhoB^{V(b)} = Ztot (litRealize b)`.
    Finite and local: no hub limit is involved. -/
theorem exp_logPhi_mul_rhoB_pow (b : Branch) :
    Real.exp (logPhi b) * rhoB ^ (Vb b) = Ztot (litRealize b) := by
  rw [logPhi_eq_log_Wb, Ztot_lit_eq_Wb, Real.exp_sub, Real.exp_log (Wb_pos b)]
  have h : Real.exp ((Vb b : ℝ) * Lval) = rhoB ^ (Vb b) := by
    rw [← logRhoB, Real.exp_nat_mul, Real.exp_log rhoB_pos]
  rw [h, div_mul_cancel₀ _ (pow_pos rhoB_pos (Vb b)).ne']

end R3Cert
