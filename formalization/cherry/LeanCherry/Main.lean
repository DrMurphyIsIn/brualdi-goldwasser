/-
LeanCherry.Main -- the anchor at lam_c = 1 + sqrt 5 (the branch ceiling there), kernel-checked.

  ceiling_at_lam_c :  for every planted branch b,  T b <= phi ^ |b|   (T = the cavity-recursion matching sum at lam_c),
  equivalently  log T_b(lam_c) <= |b| log phi = |b| F*(lam_c).

Pooled hinge induction: leaves are exact (ell = -L, msg = 1); every non-leaf branch satisfies ell <= U(msg) and
msg <= 1/2; the step pools the non-leaf children by the supergradient of the concave hinge U (Jensen) and applies
step_k_pos (k >= 1 leaf children) or step_k_zero (k = 0).
-/
import LeanCherry.Tree

open Real

namespace LeanCherry

namespace Br

noncomputable section

/-- leaf test -/
def isLeaf : Br → Bool
  | .node [] => true
  | .node (_ :: _) => false

lemma eq_leaf_of_isLeaf {b : Br} (h : isLeaf b = true) : b = .node [] := by
  match b, h with
  | .node [], _ => rfl

/-- the induction hypothesis for one branch -/
def Good (b : Br) : Prop := isLeaf b = true ∨ (isLeaf b = false ∧ ell b ≤ U (msg b) ∧ msg b ≤ 1 / 2)

def nLeaf : List Br → ℕ
  | [] => 0
  | c :: cs => (if isLeaf c then 1 else 0) + nLeaf cs
def nNon : List Br → ℕ
  | [] => 0
  | c :: cs => (if isLeaf c then 0 else 1) + nNon cs
def sumYN : List Br → ℝ
  | [] => 0
  | c :: cs => (if isLeaf c then 0 else msg c) + sumYN cs

/-- supergradient of the concave hinge U at p -/
def gsup (p : ℝ) : ℝ := if p < ych then 0 else -kap

lemma U_super (p y : ℝ) : U y ≤ U p + gsup p * (y - p) := by
  unfold gsup
  split_ifs with h
  · rw [U_of_le h.le]; simpa using U_le_zero y
  · push_neg at h
    rw [U_of_ge h]
    unfold U
    have := kap_pos
    calc min 0 (kap * (ych - y)) ≤ kap * (ych - y) := min_le_right _ _
      _ = kap * (ych - p) + -kap * (y - p) := by ring

lemma length_eq : ∀ cs : List Br, cs.length = nLeaf cs + nNon cs
  | [] => rfl
  | c :: cs => by
      simp only [List.length_cons, nLeaf, nNon, length_eq cs]
      split_ifs <;> omega

/-- the list bookkeeping: sums, bounds, and the pooled (Jensen) bound for any pooling point p -/
lemma list_facts : ∀ cs : List Br, (∀ c ∈ cs, Good c) →
    sumY cs = (nLeaf cs : ℝ) + sumYN cs ∧ 0 ≤ sumYN cs ∧ sumYN cs ≤ (nNon cs : ℝ) / 2 ∧
    ∀ p : ℝ, sumEll cs ≤ -(nLeaf cs : ℝ) * L + (nNon cs : ℝ) * U p + gsup p * (sumYN cs - (nNon cs : ℝ) * p)
  | [] => by
      intro _; simp [sumY, sumYN, nLeaf, nNon, sumEll]
  | c :: cs => by
      intro h
      obtain ⟨h1, h2, h3, h4⟩ := list_facts cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hc := h c List.mem_cons_self
      rcases hc with hl | ⟨hl, hell, hmsg⟩
      · have hb := eq_leaf_of_isLeaf hl
        have hm1 : msg c = 1 := by rw [hb]; exact msg_leaf
        have he1 : ell c = -L := by rw [hb]; exact ell_leaf
        simp only [sumY, sumYN, nLeaf, nNon, sumEll, hl, if_true]
        push_cast
        refine ⟨by rw [hm1, h1]; ring, by linarith, by linarith, fun p => ?_⟩
        have := h4 p
        rw [he1]; linarith
      · simp only [sumY, sumYN, nLeaf, nNon, sumEll, hl]
        simp only [Bool.false_eq_true, if_false]
        push_cast
        have hm0 := msg_pos c
        refine ⟨by rw [h1]; ring, by linarith, by linarith, fun p => ?_⟩
        have hs := U_super p (msg c)
        have := h4 p
        nlinarith

lemma size_lt_of_mem : ∀ (cs : List Br) (c : Br), c ∈ cs → size c ≤ sizeL cs
  | [], c, h => by simp at h
  | d :: cs, c, h => by
      simp only [sizeL]
      rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have := size_lt_of_mem cs c h'; omega

/-- the step: children Good => node Good -/
lemma good_node (cs : List Br) (h : ∀ c ∈ cs, Good c) : Good (.node cs) := by
  cases cs with
  | nil => left; rfl
  | cons c0 cs0 =>
    right
    refine ⟨rfl, ?_, ?_⟩
    swap
    · -- msg <= 1/2 since d >= 2
      rw [msg_node]
      have := sumY_nonneg (c0 :: cs0); have hl := lam_pos
      have hlen : (1:ℝ) ≤ ((c0 :: cs0).length : ℝ) := by simp
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hl.le this]
    set cs := c0 :: cs0 with hcs
    obtain ⟨hY, hS0, hS1, hpool⟩ := list_facts cs h
    have hlen := length_eq cs
    rw [ell_node, msg_node]
    have hlenR : (cs.length : ℝ) = (nLeaf cs : ℝ) + (nNon cs : ℝ) := by rw [hlen]; push_cast; ring
    have hpos : 1 ≤ nLeaf cs + nNon cs := by rw [← hlen, hcs]; simp
    rcases Nat.eq_zero_or_pos (nNon cs) with hm0 | hmpos
    · -- all children are leaves: k = length >= 1, m = 0
      have hS : sumYN cs = 0 := by
        have : (nNon cs : ℝ) = 0 := by exact_mod_cast hm0
        linarith
      have hk1 : (1:ℝ) ≤ (nLeaf cs : ℝ) := by exact_mod_cast (by omega : 1 ≤ nLeaf cs)
      have hkcase : (nLeaf cs : ℝ) = 1 ∨ 2 ≤ (nLeaf cs : ℝ) := by
        rcases (by omega : nLeaf cs = 1 ∨ 2 ≤ nLeaf cs) with e | e
        · left; exact_mod_cast e
        · right; exact_mod_cast e
      have hstep := step_k_pos (nLeaf cs : ℝ) 0 0 hk1 le_rfl le_rfl (by norm_num) hkcase
      have hp := hpool 0
      have hm0R : (nNon cs : ℝ) = 0 := by exact_mod_cast hm0
      rw [hm0R, hS] at hp
      rw [hY, hS, hlenR, hm0R]
      simp only [mul_zero, add_zero, zero_mul] at hstep hp ⊢
      linarith
    · -- m >= 1: pool at the mean t = S/m
      have hmR : (1:ℝ) ≤ (nNon cs : ℝ) := by exact_mod_cast hmpos
      set t := sumYN cs / (nNon cs : ℝ) with ht
      have hmt : (nNon cs : ℝ) * t = sumYN cs := by rw [ht]; field_simp
      have ht0 : 0 ≤ t := div_nonneg hS0 (by linarith)
      have ht1 : t ≤ 1 / 2 := by
        rw [ht, div_le_iff₀ (by linarith)]; linarith
      have hp := hpool t
      rw [hmt, sub_self, mul_zero, add_zero] at hp
      have hY' : sumY cs = (nLeaf cs : ℝ) + (nNon cs : ℝ) * t := by rw [hY, hmt]
      rw [hY', hlenR]
      rcases Nat.eq_zero_or_pos (nLeaf cs) with hk0 | hkpos
      · -- k = 0
        have hk0R : (nLeaf cs : ℝ) = 0 := by exact_mod_cast hk0
        have hmcase : (nNon cs : ℝ) = 1 ∨ (nNon cs : ℝ) = 2 ∨ 3 ≤ (nNon cs : ℝ) := by
          rcases (by omega : nNon cs = 1 ∨ nNon cs = 2 ∨ 3 ≤ nNon cs) with e | e | e
          · left; exact_mod_cast e
          · right; left; exact_mod_cast e
          · right; right; exact_mod_cast e
        have hstep := step_k_zero (nNon cs : ℝ) t hmR hmcase ht0 ht1
        rw [hk0R] at hp ⊢
        simp only [zero_add, neg_zero, zero_mul] at hp ⊢
        linarith
      · -- k >= 1
        have hk1 : (1:ℝ) ≤ (nLeaf cs : ℝ) := by exact_mod_cast hkpos
        have hkcase : (nLeaf cs : ℝ) = 1 ∨ 2 ≤ (nLeaf cs : ℝ) := by
          rcases (by omega : nLeaf cs = 1 ∨ 2 ≤ nLeaf cs) with e | e
          · left; exact_mod_cast e
          · right; exact_mod_cast e
        have hstep := step_k_pos (nLeaf cs : ℝ) (nNon cs : ℝ) t hk1 (by linarith) ht0 ht1 hkcase
        linarith

/-- every branch is Good (strong induction on size) -/
theorem good_all : ∀ b : Br, Good b := by
  have H : ∀ n : ℕ, ∀ b : Br, size b ≤ n → Good b := by
    intro n
    induction n with
    | zero => intro b hb; cases b with | node cs => simp [size] at hb
    | succ n IH =>
      intro b hb
      cases b with
      | node cs =>
        apply good_node cs
        intro c hc
        apply IH
        have := size_lt_of_mem cs c hc
        simp only [size] at hb
        omega
  exact fun b => H (size b) b le_rfl

/-- ell b <= 0 for every branch -/
theorem ell_nonpos (b : Br) : ell b ≤ 0 := by
  rcases good_all b with hl | ⟨_, hell, _⟩
  · rw [eq_leaf_of_isLeaf hl, ell_leaf]; linarith [L_pos]
  · linarith [U_le_zero (msg b)]

/-- The anchor (kernel-checked): at lam_c = 1 + sqrt 5, every planted branch satisfies T_b <= phi^|b|,
i.e. log T_b(lam_c) <= |b| log phi. -/
theorem ceiling_at_lam_c (b : Br) : T b ≤ φ ^ size b := by
  have h := ell_nonpos b
  unfold ell at h
  have hT := T_pos b
  have hlog : Real.log (T b) ≤ Real.log (φ ^ size b) := by
    rw [Real.log_pow]; unfold L at h; linarith
  exact (Real.log_le_log_iff hT (pow_pos φ_pos _)).mp hlog

/-- the threshold is lam_c = 1 + sqrt 5 -/
example : lam = 1 + √5 := lam_eq

end

end Br

end LeanCherry
