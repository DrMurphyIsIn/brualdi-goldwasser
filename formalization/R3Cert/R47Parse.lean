/-
  Rate port, file 2: THE CHERRY-FOLDING PARSE -- `Ztot (dtSub t) = Ztot (litRealize
  (parseB t))`.

  `dtSub` already expands cherries at litRealize's exact weights, but deeper child
  ORDER differs, so pairwise tree equality fails.  The right abstraction: `Popen`
  and `Matched` FACTOR THROUGH the list of value triples `(w, Zopen c, Ztot c)`,
  where per-child equality DOES hold (a cherry's dtSub IS the literal cherry tree;
  other children by the mutual value induction + `dB_parseB`).  Triple-level
  permutation invariance + `List.perm_middle` reorder cherries-first.

  Deliverables: `parseB`, `dB_parseB`, `Vb_parseB : Vb (parseB t) = usize t`, and
  `Ztot_dtSub_eq_lit` / `Zopen_dtSub_eq_lit`.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Perm

namespace R3Cert
namespace Step3

open RTree List

/-! ### The parse -/

/-- A cherry-shaped child: a 2-path. -/
def isCherryU : UTree → Bool
  | .node [.node []] => true
  | _ => false

def countCherry : List UTree → ℕ
  | [] => 0
  | K :: rest => (if isCherryU K then 1 else 0) + countCherry rest

mutual
/-- Fold cherry-shaped children into the load; parse the rest. -/
def parseB : UTree → Branch
  | .node cs => .node (countCherry cs) (parseChildren cs)
def parseChildren : List UTree → List Branch
  | [] => []
  | K :: rest =>
      if isCherryU K then parseChildren rest else parseB K :: parseChildren rest
end

theorem parseChildren_length : ∀ cs : List UTree,
    (parseChildren cs).length + countCherry cs = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons K rest ih =>
    rw [parseChildren, countCherry]
    by_cases h : isCherryU K
    · rw [if_pos h, if_pos h]
      simp only [List.length_cons]
      omega
    · rw [if_neg h, if_neg h]
      simp only [List.length_cons]
      omega

/-- The parse preserves the full degree. -/
theorem dB_parseB (t : UTree) : dB (parseB t) = udeg t := by
  cases t with
  | node cs =>
    rw [parseB, dB, udeg_node]
    have := parseChildren_length cs
    omega

/-- A cherry-shaped child realizes to the literal cherry tree, and has udeg 2. -/
theorem dtSub_cherry {K : UTree} (h : isCherryU K = true) :
    dtSub K = RTree.node [(1 / 2, RTree.node [])] ∧ udeg K = 2 := by
  cases K with
  | node l =>
    cases l with
    | nil => simp [isCherryU] at h
    | cons a t' =>
      cases t' with
      | nil =>
        cases a with
        | node al =>
          cases al with
          | nil =>
            constructor
            · rw [dtSub_node, dtChildren_cons, dtChildren_nil, dtSub_node,
                dtChildren_nil]
              norm_num [udeg_node]
            · rw [udeg_node]
              rfl
          | cons _ _ => simp [isCherryU] at h
      | cons _ _ => simp [isCherryU] at h

/-! ### Vertex counts -/

theorem usize_cherry {K : UTree} (h : isCherryU K = true) : usize K = 2 := by
  cases K with
  | node l =>
    cases l with
    | nil => simp [isCherryU] at h
    | cons a t' =>
      cases t' with
      | nil =>
        cases a with
        | node al =>
          cases al with
          | nil =>
            rw [usize_node, usizeList_cons, usizeList_nil, usize_node, usizeList_nil]
          | cons _ _ => simp [isCherryU] at h
      | cons _ _ => simp [isCherryU] at h

mutual
theorem Vb_parseB : ∀ t : UTree, Vb (parseB t) = usize t
  | .node cs => by
    rw [parseB, Vb, usize_node]
    have h := VbSum_parseChildren cs
    omega
theorem VbSum_parseChildren : ∀ cs : List UTree,
    VbSum (parseChildren cs) + 2 * countCherry cs = usizeList cs
  | [] => by rfl
  | K :: rest => by
    rw [parseChildren, countCherry, usizeList_cons]
    have hr := VbSum_parseChildren rest
    by_cases hK : isCherryU K
    · have hsz := usize_cherry hK
      rw [if_pos hK, if_pos hK]
      omega
    · have hV := Vb_parseB K
      rw [if_neg hK, if_neg hK, VbSum]
      omega
end

/-! ### The value-triple factoring -/

/-- The value triple of a weighted child. -/
noncomputable def vt (p : ℝ × RTree) : ℝ × ℝ × ℝ := (p.1, Zopen p.2, Ztot p.2)

noncomputable def Popen' : List (ℝ × ℝ × ℝ) → ℝ
  | [] => 1
  | (_, _, zt) :: rest => zt * Popen' rest

noncomputable def Matched' : List (ℝ × ℝ × ℝ) → ℝ
  | [] => 0
  | (w, zo, zt) :: rest => w * zo * Popen' rest + zt * Matched' rest

theorem Popen_factor : ∀ l : List (ℝ × RTree), Popen l = Popen' (l.map vt) := by
  intro l
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    simp only [Popen, List.map_cons, Popen', vt]
    rw [ih]

theorem Matched_factor' : ∀ l : List (ℝ × RTree), Matched l = Matched' (l.map vt) := by
  intro l
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    simp only [Matched, List.map_cons, Matched', vt]
    rw [ih, Popen_factor]

theorem Popen'_perm {l1 l2 : List (ℝ × ℝ × ℝ)} (h : l1.Perm l2) :
    Popen' l1 = Popen' l2 := by
  induction h with
  | nil => rfl
  | @cons x l1' l2' _ ih =>
    obtain ⟨w, zo, zt⟩ := x
    simp only [Popen']
    rw [ih]
  | @swap x y l =>
    obtain ⟨wx, zox, ztx⟩ := x
    obtain ⟨wy, zoy, zty⟩ := y
    simp only [Popen']
    ring
  | @trans _ _ _ _ _ ih1 ih2 => rw [ih1, ih2]

theorem Matched'_perm {l1 l2 : List (ℝ × ℝ × ℝ)} (h : l1.Perm l2) :
    Matched' l1 = Matched' l2 := by
  induction h with
  | nil => rfl
  | @cons x l1' l2' hp ih =>
    obtain ⟨w, zo, zt⟩ := x
    simp only [Matched']
    rw [ih, Popen'_perm hp]
  | @swap x y l =>
    obtain ⟨wx, zox, ztx⟩ := x
    obtain ⟨wy, zoy, zty⟩ := y
    simp only [Matched', Popen']
    ring
  | @trans _ _ _ _ _ ih1 ih2 => rw [ih1, ih2]

/-! ### The value equalities -/

mutual
/-- **The parse value equality**: raw and literal realizations share both partition
    functions. -/
theorem parse_vals : ∀ t : UTree,
    Ztot (dtSub t) = Ztot (litRealize (parseB t))
      ∧ Zopen (dtSub t) = Zopen (litRealize (parseB t))
  | .node cs => by
    have hlit : litRealize (parseB (.node cs))
        = RTree.node (List.replicate (countCherry cs) (litCherry (cs.length + 1))
            ++ litChildren (cs.length + 1) (parseChildren cs)) := by
      rw [parseB, litRealize]
      have harith : (parseChildren cs).length + 1 + countCherry cs = cs.length + 1 := by
        have := parseChildren_length cs
        omega
      rw [harith]
    have hperm := parse_children_perm (cs.length + 1) cs
    rw [dtSub_node, hlit]
    constructor
    · simp only [Ztot]
      rw [Popen_factor, Matched_factor', Popen_factor, Matched_factor',
        Popen'_perm hperm, Matched'_perm hperm]
    · simp only [Zopen]
      rw [Popen_factor, Popen_factor, Popen'_perm hperm]

/-- The triple lists of the raw children and the cherries-first literal children are
    permutations. -/
theorem parse_children_perm : ∀ (d : ℕ) (cs : List UTree),
    ((dtChildren d cs).map vt).Perm
      ((List.replicate (countCherry cs) (litCherry d)
        ++ litChildren d (parseChildren cs)).map vt)
  | d, [] => by
    rw [dtChildren_nil, countCherry, parseChildren]
    simp [litChildren]
  | d, K :: rest => by
    rw [dtChildren_cons, countCherry, parseChildren]
    have ihrest := parse_children_perm d rest
    by_cases hK : isCherryU K
    · obtain ⟨htree, hdeg⟩ := dtSub_cherry hK
      rw [if_pos hK, if_pos hK, Nat.add_comm 1 (countCherry rest),
        List.replicate_succ]
      have hhd : vt (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K) = vt (litCherry d) := by
        rw [htree, hdeg, litCherry]
        norm_num [vt, cherryMid]
      simp only [List.map_cons, List.cons_append, List.map_cons]
      rw [hhd]
      exact (ihrest.cons _)
    · rw [if_neg hK, if_neg hK, Nat.zero_add]
      simp only [litChildren]
      have hvals := parse_vals K
      have hhd : vt (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K)
          = vt (1 / ((d : ℝ) * (dB (parseB K) : ℝ)), litRealize (parseB K)) := by
        simp only [vt, dB_parseB, hvals.1, hvals.2]
      calc ((1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K) :: dtChildren d rest).map vt
          = vt (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K)
            :: (dtChildren d rest).map vt := by rw [List.map_cons]
        _ ~ vt (1 / ((d : ℝ) * (dB (parseB K) : ℝ)), litRealize (parseB K))
            :: ((List.replicate (countCherry rest) (litCherry d)
              ++ litChildren d (parseChildren rest)).map vt) := by
            rw [hhd]
            exact ihrest.cons _
        _ ~ ((List.replicate (countCherry rest) (litCherry d)).map vt)
            ++ vt (1 / ((d : ℝ) * (dB (parseB K) : ℝ)), litRealize (parseB K))
            :: ((litChildren d (parseChildren rest)).map vt) := by
            rw [List.map_append]
            exact (List.perm_middle).symm
        _ = ((List.replicate (countCherry rest) (litCherry d)
              ++ (1 / ((d : ℝ) * (dB (parseB K) : ℝ)), litRealize (parseB K))
              :: litChildren d (parseChildren rest)).map vt) := by
            rw [List.map_append, List.map_cons]
end

/-- The parse identity for the total partition function. -/
theorem Ztot_dtSub_eq_lit (t : UTree) :
    Ztot (dtSub t) = Ztot (litRealize (parseB t)) := (parse_vals t).1

/-- The parse identity for the open partition function. -/
theorem Zopen_dtSub_eq_lit (t : UTree) :
    Zopen (dtSub t) = Zopen (litRealize (parseB t)) := (parse_vals t).2

end Step3
end R3Cert
