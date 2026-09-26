/-
  R3Cert.BGMaximizer -- the spider reduction for the Brualdi-Goldwasser maximizer, stated for
  actual trees (`UTree`, `Aobj` = per(L)/prod deg via `pi_utree`).

  `BGSpiderLowDegree.spider_dominates_of_maxDegreeRoot` proves, in the planted cavity model
  `R3Cert.BGSCL.Branch` with objective `piRoot`, that a root of maximum degree with >= 491 further
  vertices is strictly beaten by an arm_5/arm_4 spider unless it already is a spider.  This file
  supplies the two missing links:
    (1) the translation `fromU : UTree -> Branch` with `Aobj (node cs) = piRoot (cs.map fromU)`
        (`Aobj_eq_piRoot`): the BGSCL cavity pair `(U, total)` of `fromU K` is exactly
        `(Zopen, Ztot)` of the planted realization `dtSub K`;
    (2) every tree reroots, preserving `Aobj` and size (`RerootRel`, R47RootShift), onto a vertex of
        maximum degree (`exists_maxRooted`).
  Result (`bg_spider_reduction`): every tree on n >= 492 vertices is `Aobj`-dominated by a SPIDER on
  n vertices -- a centre whose children are cherries and arms (`armU j`: a vertex carrying j
  cherries; `armU 0` is a leaf).  Together with the exact spider optimization (BGSpiderOpt +
  proof/docs/BG_SPIDER_OPTIMIZATION_2026-09-24.md) and a certified computation for n <= 491 this
  identifies the maximizer; those two inputs are not in this file.
  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGSpiderLowDegree
import R3Cert.R47RootShift
import R3Cert.BGSCLFlpDeepLift
import R3Cert.BGSCLRealOblACaseAIdentity
import R3Cert.R47ArmPerm
import R3Cert.R47Tree

namespace BGMax

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSCL

/-! ### (1) The translation and the objective bridge -/

mutual
/-- A `UTree` read as a BGSCL planted branch (same shape). -/
def fromU : UTree → Branch
  | .node cs => Branch.node (fromUL cs)
/-- Child-list version. -/
def fromUL : List UTree → List Branch
  | [] => []
  | c :: t => fromU c :: fromUL t
end

theorem fromUL_eq : ∀ l : List UTree, fromUL l = l.map fromU
  | [] => by simp [fromUL]
  | c :: t => by simp [fromUL, fromUL_eq t]

mutual
/-- The BGSCL cavity pair of `fromU K` is `(Zopen, Ztot)` of the planted realization of `K`. -/
theorem fromU_spec : ∀ K : UTree,
    (cav (fromU K)).2 = Ztot (dtSub K) ∧ (cav (fromU K)).1 = Zopen (dtSub K) ∧
      bcc (fromU K) + 1 = udeg K ∧ bsize (fromU K) = usize K
  | .node cs => by
    obtain ⟨h1, h2, h3, h4⟩ := fromUL_spec cs
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [fromU, cav]
      rw [h1, h2, h4, Ztot_dtSub_node_eq]
      ring
    · simp only [fromU, cav]
      rw [h1, Zopen_dtSub_node_eq]
    · simp only [fromU, bcc, udeg_node, h4]
    · simp only [fromU, bsize, usize_node, h3]
/-- List version: product of totals, the dressed cavity sum, size and length. -/
theorem fromUL_spec : ∀ l : List UTree,
    (cavAgg (fromUL l)).1 = (l.map fun K => Ztot (dtSub K)).prod ∧
      (cavAgg (fromUL l)).2 = qSum l ∧ bsizeList (fromUL l) = usizeList l ∧
      (fromUL l).length = l.length
  | [] => by simp [fromUL, cavAgg, qSum, bsizeList, usizeList]
  | c :: t => by
    obtain ⟨a1, a2, a3, a4⟩ := fromU_spec c
    obtain ⟨b1, b2, b3, b4⟩ := fromUL_spec t
    have hdeg : ((bcc (fromU c) : ℝ) + 1) = (udeg c : ℝ) := by exact_mod_cast a3
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [fromUL, cavAgg, List.map_cons, List.prod_cons, a1, b1]
    · simp only [fromUL, cavAgg]
      rw [qSum_cons, a1, a2, b2, hdeg, div_div]
    · simp only [fromUL, bsizeList, usizeList_cons, a4, b3]
    · simp only [fromUL, List.length_cons, b4]
end

/-- **The objective bridge.**  `Aobj` of a tree rooted at a vertex with children `cs` is the BGSCL
    root objective `piRoot` of the translated children. -/
theorem Aobj_eq_piRoot (cs : List UTree) : Aobj (UTree.node cs) = piRoot (cs.map fromU) := by
  obtain ⟨h1, h2, _, h4⟩ := fromUL_spec cs
  rw [Aobj_factor, piRoot, ← fromUL_eq, ← cavAgg_fst, ← cavAgg_snd, h1, h2, h4]
  ring

theorem usize_eq_bsizeList (cs : List UTree) :
    usize (UTree.node cs) = 1 + bsizeList (cs.map fromU) := by
  rw [← fromUL_eq, (fromUL_spec cs).2.2.1, usize_node]

theorem fromU_cherryU : fromU cherryU = cherry := by
  simp [fromU, fromUL, cherryU, cherry]

theorem fromU_armU (j : ℕ) : fromU (armU j) = armB j := by
  rw [armU, fromU, fromUL_eq, List.map_replicate, fromU_cherryU, armB]

/-! ### The inverse translation (to read atoms back as trees) -/

mutual
def toU : Branch → UTree
  | .node cs => UTree.node (toUL cs)
def toUL : List Branch → List UTree
  | [] => []
  | c :: t => toU c :: toUL t
end

mutual
theorem toU_fromU : ∀ K : UTree, toU (fromU K) = K
  | .node cs => by rw [fromU, toU, toUL_fromUL cs]
theorem toUL_fromUL : ∀ l : List UTree, toUL (fromUL l) = l
  | [] => by simp [fromUL, toUL]
  | c :: t => by rw [fromUL, toUL, toU_fromU c, toUL_fromUL t]
end

theorem toUL_eq : ∀ l : List Branch, toUL l = l.map toU
  | [] => by simp [toUL]
  | c :: t => by simp [toUL, toUL_eq t]

theorem toU_cherry : toU cherry = cherryU := by
  simp [toU, toUL, cherry, cherryU]

theorem toU_armB (j : ℕ) : toU (armB j) = armU j := by
  rw [armB, toU, toUL_eq, List.map_replicate, toU_cherry, armU]

/-- A child whose translation is an atom is a cherry or an arm. -/
theorem atom_of_fromU {c : UTree} (h : IsAtom (fromU c)) : c = cherryU ∨ ∃ j, c = armU j := by
  rcases h with h | ⟨j, h⟩
  · left; rw [← toU_fromU c, h, toU_cherry]
  · right; exact ⟨j, by rw [← toU_fromU c, h, toU_armB]⟩

/-! ### (2) Rerooting onto a vertex of maximum degree -/

noncomputable local instance : DecidableEq UTree := Classical.decEq _

mutual
/-- Maximum vertex degree of a PLANTED tree (its root counts the edge to its parent). -/
def mdS : UTree → ℕ
  | .node cs => max (cs.length + 1) (mdL cs)
def mdL : List UTree → ℕ
  | [] => 0
  | c :: t => max (mdS c) (mdL t)
end

theorem le_mdL {x : UTree} : ∀ {l : List UTree}, x ∈ l → mdS x ≤ mdL l
  | [], h => by simp at h
  | c :: t, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp only [mdL]; exact le_max_left _ _
    · simp only [mdL]; exact le_trans (le_mdL h') (le_max_right _ _)

theorem mdL_le {m : ℕ} : ∀ {l : List UTree}, (∀ x ∈ l, mdS x ≤ m) → mdL l ≤ m
  | [], _ => by simp [mdL]
  | c :: t, h => by
    simp only [mdL]
    exact max_le (h c (by simp)) (mdL_le (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem one_le_mdS : ∀ x : UTree, 1 ≤ mdS x
  | .node cs => by simp only [mdS]; omega

mutual
theorem maxCh_fromU : ∀ x : UTree, maxCh (fromU x) + 1 = mdS x
  | .node cs => by
    have h := maxChList_fromUL cs
    have hl := (fromUL_spec cs).2.2.2
    simp only [fromU, maxCh, mdS, hl]
    omega
theorem maxChList_fromUL : ∀ l : List UTree, maxChList (fromUL l) + 1 = max 1 (mdL l)
  | [] => by simp [fromUL, maxChList, mdL]
  | c :: t => by
    have h1 := maxCh_fromU c
    have h2 := maxChList_fromUL t
    have h3 := one_le_mdS c
    simp only [fromUL, maxChList, mdL]
    omega
end

/-- The root has maximum degree: every child, as a planted tree, has max degree `≤` the root's. -/
def MaxRooted : UTree → Prop
  | .node cs => ∀ c ∈ cs, mdS c ≤ cs.length

theorem exists_max_mdS : ∀ (l : List UTree), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, mdS y ≤ mdS x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun y hy => by simp at hy; rw [hy]⟩
  | a :: b :: t, _ => by
    obtain ⟨x, hx, hmax⟩ := exists_max_mdS (b :: t) (by simp)
    rcases le_total (mdS a) (mdS x) with h | h
    · refine ⟨x, List.mem_cons_of_mem _ hx, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h
      · exact hmax y hy'
    · refine ⟨a, by simp, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact le_refl _
      · exact le_trans (hmax y hy') h

theorem usize_le_of_mem {x : UTree} : ∀ {l : List UTree}, x ∈ l → usize x ≤ usizeList l
  | [], h => by simp at h
  | c :: t, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · rw [usizeList_cons]; omega
    · rw [usizeList_cons]; have := usize_le_of_mem h'; omega

/-- One move: bring the maximal child `x = node es` to the front and shift the root into it. -/
theorem reroot_into {ds : List UTree} {es : List UTree} (tail : List UTree)
    (hx : UTree.node es ∈ ds) :
    RerootRel (UTree.node (ds ++ tail)) (UTree.node (es ++ [UTree.node (ds.erase (UTree.node es) ++ tail)])) := by
  have hperm : (ds ++ tail).Perm (UTree.node es :: (ds.erase (UTree.node es) ++ tail)) := by
    have := List.perm_cons_erase hx
    exact (this.append_right tail).trans (by simp)
  refine Relation.ReflTransGen.head (Or.inr ⟨_, _, hperm, rfl, rfl⟩) ?_
  exact Relation.ReflTransGen.single (Or.inl ⟨es, ds.erase (UTree.node es) ++ tail, rfl, rfl⟩)

theorem core : ∀ (N : ℕ) (ds : List UTree) (R : UTree), usizeList ds ≤ N →
    mdS R ≤ max (ds.length + 1) (mdL ds) →
    ∃ t', RerootRel (UTree.node (ds ++ [R])) t' ∧ MaxRooted t' := by
  intro N
  induction N with
  | zero =>
    intro ds R hN hR
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons c t =>
        rw [usizeList_cons] at hN
        cases c with | node _ => rw [usize_node] at hN; omega
    subst hds
    refine ⟨_, Relation.ReflTransGen.refl, ?_⟩
    intro c hc
    simp only [List.nil_append, List.mem_singleton] at hc
    subst hc; simpa [mdL] using hR
  | succ N ih =>
    intro ds R hN hR
    by_cases hA : ∀ x ∈ ds, mdS x ≤ ds.length + 1
    · refine ⟨_, Relation.ReflTransGen.refl, ?_⟩
      have hL : mdL ds ≤ ds.length + 1 := mdL_le hA
      intro c hc
      rw [List.length_append, List.length_singleton]
      rcases List.mem_append.mp hc with hc | hc
      · exact hA c hc
      · simp only [List.mem_singleton] at hc; subst hc; omega
    · push Not at hA
      obtain ⟨y, hy, hylt⟩ := hA
      have hne : ds ≠ [] := List.ne_nil_of_mem hy
      obtain ⟨x, hx, hmax⟩ := exists_max_mdS ds hne
      have hxbig : ds.length + 1 < mdS x := lt_of_lt_of_le hylt (hmax y hy)
      obtain ⟨es⟩ := x
      set rest := ds.erase (UTree.node es)
      have hrest_len : rest.length = ds.length - 1 := List.length_erase_of_mem hx
      have hdspos : 0 < ds.length := List.length_pos_of_ne_nil hne
      have hsz : usizeList es ≤ N := by
        have := usize_le_of_mem hx; rw [usize_node] at this; omega
      have hRx : mdS R ≤ mdS (UTree.node es) := by
        have : mdL ds ≤ mdS (UTree.node es) := mdL_le hmax
        omega
      have hR' : mdS (UTree.node (rest ++ [R])) ≤ max (es.length + 1) (mdL es) := by
        have hmx : mdS (UTree.node es) = max (es.length + 1) (mdL es) := by simp only [mdS]
        rw [← hmx]
        simp only [mdS, List.length_append, List.length_singleton]
        refine max_le (by omega) (mdL_le ?_)
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hmax z (List.mem_of_mem_erase hz)
        · simp only [List.mem_singleton] at hz; subst hz; exact hRx
      obtain ⟨t', ht', hmr⟩ := ih es (UTree.node (rest ++ [R])) hsz hR'
      exact ⟨t', (reroot_into [R] hx).trans ht', hmr⟩

/-- **Every tree reroots (preserving `Aobj` and size) onto a vertex of maximum degree.** -/
theorem exists_maxRooted (t : UTree) : ∃ t', RerootRel t t' ∧ MaxRooted t' := by
  obtain ⟨cs⟩ := t
  by_cases hA : ∀ c ∈ cs, mdS c ≤ cs.length
  · exact ⟨_, Relation.ReflTransGen.refl, hA⟩
  · push Not at hA
    obtain ⟨y, hy, hylt⟩ := hA
    have hne : cs ≠ [] := List.ne_nil_of_mem hy
    obtain ⟨x, hx, hmax⟩ := exists_max_mdS cs hne
    have hxbig : cs.length < mdS x := lt_of_lt_of_le hylt (hmax y hy)
    obtain ⟨es⟩ := x
    set rest := cs.erase (UTree.node es)
    have hrest_len : rest.length = cs.length - 1 := List.length_erase_of_mem hx
    have hcspos : 0 < cs.length := List.length_pos_of_ne_nil hne
    have hR : mdS (UTree.node rest) ≤ max (es.length + 1) (mdL es) := by
      have hmx : mdS (UTree.node es) = max (es.length + 1) (mdL es) := by simp only [mdS]
      rw [← hmx]
      simp only [mdS]
      exact max_le (by omega) (mdL_le (fun z hz => hmax z (List.mem_of_mem_erase hz)))
    obtain ⟨t', ht', hmr⟩ := core (usizeList es) es (UTree.node rest) le_rfl hR
    have hstep := reroot_into ([] : List UTree) hx
    simp only [List.append_nil] at hstep
    exact ⟨t', hstep.trans ht', hmr⟩

/-! ### (3) The reduction for actual trees -/

/-- A maximum-degree rooting of a tree with at least 3 vertices has at least 2 children. -/
theorem two_le_length_of_maxRooted {cs : List UTree} (h : MaxRooted (UTree.node cs))
    (hn : 3 ≤ usize (UTree.node cs)) : 2 ≤ cs.length := by
  by_contra hlt
  push Not at hlt
  rcases cs with _ | ⟨c, _ | ⟨d, t⟩⟩
  · rw [usize_node] at hn; simp [usizeList] at hn
  · have hc := h c (by simp)
    obtain ⟨es⟩ := c
    have : es = [] := by
      simp only [mdS, List.length_singleton] at hc
      have : es.length + 1 ≤ 1 := le_trans (le_max_left _ _) hc
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [usize_node, usizeList_cons, usize_node] at hn
    simp [usizeList] at hn
  · simp at hlt

/-- **The spider reduction.**  Every tree on `n ≥ 492` vertices is `Aobj`-dominated by a spider on
    `n` vertices: a centre whose children are all cherries or arms (`armU j`, `armU 0` = leaf). -/
theorem bg_spider_reduction (t : UTree) (hn : 492 ≤ usize t) :
    ∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧
      usize (UTree.node cs) = usize t ∧ Aobj t ≤ Aobj (UTree.node cs) := by
  obtain ⟨t', hrr, hmr⟩ := exists_maxRooted t
  have hA := hrr.aobj
  have hS := hrr.usize
  obtain ⟨cs'⟩ := t'
  have hk2 : 2 ≤ (cs'.map fromU).length := by
    rw [List.length_map]; exact two_le_length_of_maxRooted hmr (by omega)
  have hcap : ∀ c ∈ cs'.map fromU, maxCh c + 1 ≤ (cs'.map fromU).length := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    rw [maxCh_fromU, List.length_map]; exact hmr x hx
  have hN : 491 ≤ bsizeList (cs'.map fromU) := by
    have := usize_eq_bsizeList cs'; omega
  by_cases hsp : (cs'.map fromU).length ≤ 23 ∨ ∃ c ∈ cs'.map fromU, ¬ IsAtom c
  · obtain ⟨a, q, _, hsz, hlt⟩ := spider_dominates_of_maxDegreeRoot _ hk2 hcap hN hsp
    refine ⟨List.replicate a (armU 5) ++ List.replicate q (armU 4), ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inr ⟨5, (List.eq_of_mem_replicate hc)⟩
      · exact Or.inr ⟨4, (List.eq_of_mem_replicate hc)⟩
    · have hmap : (List.replicate a (armU 5) ++ List.replicate q (armU 4)).map fromU = spiderB a q := by
        simp [List.map_replicate, fromU_armU, spiderB]
      rw [usize_eq_bsizeList, hmap, hsz, hS, usize_eq_bsizeList]
    · have hmap : (List.replicate a (armU 5) ++ List.replicate q (armU 4)).map fromU = spiderB a q := by
        simp [List.map_replicate, fromU_armU, spiderB]
      rw [hA, Aobj_eq_piRoot, Aobj_eq_piRoot, hmap]
      exact le_of_lt hlt
  · push Not at hsp
    obtain ⟨_, hat⟩ := hsp
    refine ⟨cs', fun c hc => atom_of_fromU (hat _ (List.mem_map_of_mem hc)), hS.symm, le_of_eq hA⟩

/-- The same reduction for the literal Laplacian permanent ratio. -/
theorem bg_spider_reduction_perm (t : UTree) (hn : 492 ≤ usize t) :
    ∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧
      usize (UTree.node cs) = usize t ∧
      (R3Cert.lapl (aGraph (realize (dtRealize t)))).permanent
          / (∏ v, ((aGraph (realize (dtRealize t))).degree v : ℝ))
        ≤ (R3Cert.lapl (aGraph (realize (dtRealize (UTree.node cs))))).permanent
          / (∏ v, ((aGraph (realize (dtRealize (UTree.node cs)))).degree v : ℝ)) := by
  obtain ⟨cs, hat, hsz, hle⟩ := bg_spider_reduction t hn
  exact ⟨cs, hat, hsz, by rw [pi_utree, pi_utree]; exact hle⟩

end BGMax
