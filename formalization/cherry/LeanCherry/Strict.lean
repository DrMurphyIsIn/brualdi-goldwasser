/-
LeanCherry.Strict -- equality in the cherry-regime ceiling holds only for the cherry.

At lam_c: refine the anchor induction to  SG b := b = leaf  or  b = cherry  or  ell b < U (msg b)   (strict for every other branch).
The anchor step is re-proved in SLACK form: ell(node cs) <= U(msg) - D, D = sum over children of (Ehat c - ell c) >= 0, Ehat c = -L for
leaves and U(msg c) otherwise.  If D > 0 we are done; if D = 0 every non-leaf child is tight, hence (IH) a cherry, and the
"leaves and cherries only" configurations are computed exactly (strict unless the node is the cherry).
For l > lam_c: g_b is antitone (LeanCherry.ThmE), so strictness at lam_c propagates.
-/
import LeanCherry.Lambda1

open Real

namespace LeanCherry

namespace Br

noncomputable section

/-! ### the anchor step with an arbitrary child-value function -/

def sumF (E : Br → ℝ) : List Br → ℝ
  | [] => 0
  | c :: cs => E c + sumF E cs

lemma pool_gen (E : Br → ℝ) : ∀ cs : List Br, (∀ c ∈ cs, Good c) →
    (∀ c ∈ cs, isLeaf c = true → E c = -L) → (∀ c ∈ cs, isLeaf c = false → E c ≤ U (msg c)) →
    ∀ p : ℝ, sumF E cs ≤ -(nLeaf cs : ℝ) * L + (nNon cs : ℝ) * U p + gsup p * (sumYN cs - (nNon cs : ℝ) * p)
  | [] => by intro _ _ _ p; simp [sumF, nLeaf, nNon, sumYN]
  | c :: cs => by
      intro h hL hN p
      have IH := pool_gen E cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
        (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (fun x hx => hN x (List.mem_cons_of_mem _ hx)) p
      cases hc : isLeaf c with
      | true =>
        have he := hL c List.mem_cons_self hc
        simp only [sumF, nLeaf, nNon, sumYN, hc, if_true]
        push_cast
        rw [he]; linarith
      | false =>
        have he := hN c List.mem_cons_self hc
        have hs := U_super p (msg c)
        simp only [sumF, nLeaf, nNon, sumYN, hc]
        simp only [Bool.false_eq_true, if_false]
        push_cast
        nlinarith [he, hs, IH]

/-- tight child value -/
def Ehat (c : Br) : ℝ := if isLeaf c then -L else U (msg c)

/-- the anchor step in pooled form (any nonempty children list of Good branches) -/
lemma pooled_node (cs : List Br) (hne : cs ≠ []) (h : ∀ c ∈ cs, Good c) :
    sumF Ehat cs + Real.log (1 + lam * sumY cs / ((cs.length : ℝ) + 1)) - L ≤ U (msg (.node cs)) := by
  obtain ⟨hY, hS0, hS1, _⟩ := list_facts cs h
  have hpool := pool_gen Ehat cs h (fun c _ hc => by simp [Ehat, hc]) (fun c _ hc => by simp [Ehat, hc])
  have hlen := length_eq cs
  rw [msg_node]
  have hlenR : (cs.length : ℝ) = (nLeaf cs : ℝ) + (nNon cs : ℝ) := by rw [hlen]; push_cast; ring
  have hpos : 1 ≤ nLeaf cs + nNon cs := by rw [← hlen]; exact List.length_pos_iff.mpr hne
  rcases Nat.eq_zero_or_pos (nNon cs) with hm0 | hmpos
  · have hS : sumYN cs = 0 := by
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
  · have hmR : (1:ℝ) ≤ (nNon cs : ℝ) := by exact_mod_cast hmpos
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
    · have hk0R : (nLeaf cs : ℝ) = 0 := by exact_mod_cast hk0
      have hmcase : (nNon cs : ℝ) = 1 ∨ (nNon cs : ℝ) = 2 ∨ 3 ≤ (nNon cs : ℝ) := by
        rcases (by omega : nNon cs = 1 ∨ nNon cs = 2 ∨ 3 ≤ nNon cs) with e | e | e
        · left; exact_mod_cast e
        · right; left; exact_mod_cast e
        · right; right; exact_mod_cast e
      have hstep := step_k_zero (nNon cs : ℝ) t hmR hmcase ht0 ht1
      rw [hk0R] at hp ⊢
      simp only [zero_add, neg_zero, zero_mul] at hp ⊢
      linarith
    · have hk1 : (1:ℝ) ≤ (nLeaf cs : ℝ) := by exact_mod_cast hkpos
      have hkcase : (nLeaf cs : ℝ) = 1 ∨ 2 ≤ (nLeaf cs : ℝ) := by
        rcases (by omega : nLeaf cs = 1 ∨ 2 ≤ nLeaf cs) with e | e
        · left; exact_mod_cast e
        · right; exact_mod_cast e
      have hstep := step_k_pos (nLeaf cs : ℝ) (nNon cs : ℝ) t hk1 (by linarith) ht0 ht1 hkcase
      linarith

/-! ### slack -/

def slack (c : Br) : ℝ := Ehat c - ell c

lemma sumEll_eq : ∀ cs : List Br, sumEll cs = sumF Ehat cs - sumF slack cs
  | [] => by simp [sumEll, sumF]
  | c :: cs => by simp only [sumEll, sumF, slack]; rw [sumEll_eq cs]; ring

lemma slack_nonneg {c : Br} (h : Good c) : 0 ≤ slack c := by
  unfold slack Ehat
  rcases h with hl | ⟨hl, hell, _⟩
  · rw [if_pos hl, eq_leaf_of_isLeaf hl, ell_leaf]; simp
  · rw [if_neg (by simp [hl])]; linarith

lemma sumF_nonneg {f : Br → ℝ} : ∀ cs : List Br, (∀ c ∈ cs, 0 ≤ f c) → 0 ≤ sumF f cs
  | [] => fun _ => by simp [sumF]
  | c :: cs => fun h => by
      simp only [sumF]
      linarith [h c List.mem_cons_self, sumF_nonneg cs (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma sumF_pos {f : Br → ℝ} : ∀ cs : List Br, (∀ c ∈ cs, 0 ≤ f c) → (∃ c ∈ cs, 0 < f c) → 0 < sumF f cs
  | [] => fun _ h => by obtain ⟨c, hc, _⟩ := h; simp at hc
  | c :: cs => fun h0 ⟨d, hd, hpos⟩ => by
      simp only [sumF]
      have h1 := h0 c List.mem_cons_self
      have h2 := sumF_nonneg cs (fun x hx => h0 x (List.mem_cons_of_mem _ hx))
      rcases List.mem_cons.mp hd with rfl | hd'
      · linarith
      · have := sumF_pos cs (fun x hx => h0 x (List.mem_cons_of_mem _ hx)) ⟨d, hd', hpos⟩
        linarith

/-! ### the leaf and the cherry -/

def cherry : Br := .node [.node []]

lemma msg_cherry : msg cherry = ych := by
  rw [cherry, msg_node, ych_eq]; simp [sumY, msg_leaf]; ring_nf

lemma ell_cherry : ell cherry = 0 := by
  rw [cherry, ell_node]; simp only [sumEll, sumY, ell_leaf, msg_leaf, List.length_cons, List.length_nil]
  have e : (1:ℝ) + lam * (1 + 0) / (((0 + 1 : ℕ) : ℝ) + 1) = φ ^ 2 := by
    rw [← one_add_half_lam]; push_cast; ring
  rw [e, log_φ_sq]; ring

lemma isLeaf_cherry : isLeaf cherry = false := rfl

/-! ### nodes all of whose children are leaves or cherries -/

def LC (c : Br) : Prop := c = .node [] ∨ c = cherry

lemma lc_sums : ∀ cs : List Br, (∀ c ∈ cs, LC c) →
    sumY cs = (nLeaf cs : ℝ) + (nNon cs : ℝ) * ych ∧ sumEll cs = -(nLeaf cs : ℝ) * L
  | [] => fun _ => by simp [sumY, sumEll, nLeaf, nNon]
  | c :: cs => fun h => by
      obtain ⟨h1, h2⟩ := lc_sums cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rcases h c List.mem_cons_self with rfl | rfl
      · simp only [sumY, sumEll, nLeaf, nNon, isLeaf, if_true, msg_leaf, ell_leaf, h1, h2]; push_cast; constructor <;> ring
      · simp only [sumY, sumEll, nLeaf, nNon, isLeaf_cherry, msg_cherry, ell_cherry, h1, h2]
        simp only [Bool.false_eq_true, if_false]; push_cast; constructor <;> ring

lemma lt_U_iff {x y : ℝ} : x < U y ↔ x < 0 ∧ x < kap * (ych - y) := lt_min_iff

/-- strict kink constants -/
lemma Cm_neg (m : ℝ) (hm : 1 ≤ m) (hcase : m = 1 ∨ m = 2 ∨ 3 ≤ m) :
    (m * φ + 1) / ((m + 1) * φ) - 1 + kap * (1 / (m * φ + 1) - ych) < 0 := by
  have hp := φ_pos; have hk := kap_pos; have hp1 := φ_gt_one
  rw [ych_eq']
  have hq : (1 - φ) / φ = -1 / (φ + 1) := by
    rw [div_eq_div_iff hp.ne' (by positivity)]; linear_combination (-1 : ℝ) * φ_sq
  rcases hcase with h | h | h
  · subst h
    have e : (1 * φ + 1) / ((1 + 1) * φ) - 1 + kap * (1 / (1 * φ + 1) - 1 / (2 * (φ + 1)))
        = (1 / 2) * ((1 - φ) / φ) + kap / (2 * (φ + 1)) := by field_simp; ring
    rw [e, hq]
    have : (1 / 2) * (-1 / (φ + 1)) + kap / (2 * (φ + 1)) = (kap - 1) / (2 * (φ + 1)) := by field_simp; ring
    rw [this]
    exact div_neg_of_neg_of_pos (by linarith [kap_lt_one]) (by positivity)
  · subst h
    have e : (2 * φ + 1) / ((2 + 1) * φ) - 1 + kap * (1 / (2 * φ + 1) - 1 / (2 * (φ + 1)))
        = (1 / 3) * ((1 - φ) / φ) + kap / (2 * (φ + 1) * (2 * φ + 1)) := by field_simp; ring
    rw [e, hq]
    have : (1 / 3) * (-1 / (φ + 1)) + kap / (2 * (φ + 1) * (2 * φ + 1))
        = (3 * kap - 2 * (2 * φ + 1)) / (6 * (φ + 1) * (2 * φ + 1)) := by field_simp; ring
    rw [this]
    exact div_neg_of_neg_of_pos (by linarith [kap_lt_one]) (by positivity)
  · have hA : (m * φ + 1) / ((m + 1) * φ) - 1 < 0 := by
      rw [sub_neg, div_lt_one (by positivity)]; nlinarith
    have hB : 1 / (m * φ + 1) - 1 / (2 * (φ + 1)) ≤ 0 := by
      rw [sub_nonpos, one_div_le_one_div (by positivity) (by positivity)]; nlinarith
    nlinarith [kap_pos]

lemma ych_lt_half : ych < 1 / 2 := by
  rw [ych_eq, div_lt_div_iff₀ (by linarith [lam_pos]) (by norm_num)]; linarith [lam_pos]

/-- configurations of leaves and cherries other than the cherry itself are strict -/
lemma lc_strict (cs : List Br) (hne : cs ≠ []) (hnc : cs ≠ [.node []]) (h : ∀ c ∈ cs, LC c) :
    ell (.node cs) < U (msg (.node cs)) := by
  obtain ⟨hY, hE⟩ := lc_sums cs h
  have hlen := length_eq cs
  have hlenR : (cs.length : ℝ) = (nLeaf cs : ℝ) + (nNon cs : ℝ) := by rw [hlen]; push_cast; ring
  have hpos : 1 ≤ nLeaf cs + nNon cs := by rw [← hlen]; exact List.length_pos_iff.mpr hne
  have hl := lam_pos; have hL := L_pos; have hy := ych_pos; have hyh := ych_lt_half
  rw [ell_node, msg_node, hY, hE, hlenR]
  set k := (nLeaf cs : ℝ) with hk
  set m := (nNon cs : ℝ) with hm
  have hk0 : 0 ≤ k := by positivity
  have hm0 : 0 ≤ m := by positivity
  have hd : 0 < k + m + 1 := by linarith
  rcases Nat.eq_zero_or_pos (nLeaf cs) with hkz | hkp
  · -- k = 0: all cherries, m >= 1
    have hkz' : k = 0 := by rw [hk]; exact_mod_cast hkz
    have hm1 : (1:ℝ) ≤ m := by rw [hm]; exact_mod_cast (by omega : 1 ≤ nNon cs)
    have hmcase : m = 1 ∨ m = 2 ∨ 3 ≤ m := by
      rcases (by omega : nNon cs = 1 ∨ nNon cs = 2 ∨ 3 ≤ nNon cs) with e | e | e
      · left; rw [hm]; exact_mod_cast e
      · right; left; rw [hm]; exact_mod_cast e
      · right; right; rw [hm]; exact_mod_cast e
    rw [hkz']
    have hly := lam_ych'
    have hφ := φ_pos
    have hlm : lam * (0 + m * ych) = m * (φ - 1) := by rw [← hly]; ring
    have e1 : 1 + lam * (0 + m * ych) / (0 + m + 1) = (m * φ + 1) / (m + 1) := by
      rw [hlm]; field_simp; ring
    have e2 : 1 / (0 + m + 1 + lam * (0 + m * ych)) = 1 / (m * φ + 1) := by
      rw [hlm]; congr 1; ring
    rw [e1, e2]
    have hb : 0 < (m * φ + 1) / (m + 1) := by positivity
    have hlog : Real.log ((m * φ + 1) / (m + 1)) - L ≤ (m * φ + 1) / ((m + 1) * φ) - 1 := by
      unfold L
      rw [← Real.log_div hb.ne' hφ.ne', show (m * φ + 1) / (m + 1) / φ = (m * φ + 1) / ((m + 1) * φ) by field_simp]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hA : (m * φ + 1) / ((m + 1) * φ) - 1 < 0 := by
      rw [sub_neg, div_lt_one (by positivity)]; nlinarith [φ_gt_one]
    have hC := Cm_neg m hm1 hmcase
    rw [lt_U_iff]
    constructor
    · simp only [neg_zero, zero_mul, zero_add]; linarith
    · simp only [neg_zero, zero_mul, zero_add]; linarith
  · have hk1 : (1:ℝ) ≤ k := by rw [hk]; exact_mod_cast hkp
    -- U(msg) = 0
    have hyv : 1 / (k + m + 1 + lam * (k + m * ych)) ≤ ych := by
      calc 1 / (k + m + 1 + lam * (k + m * ych)) ≤ 1 / (2 + lam) :=
            one_div_le_one_div_of_le (by linarith)
              (by nlinarith [mul_le_mul_of_nonneg_left hk1 hl.le, mul_nonneg hl.le (mul_nonneg hm0 hy.le)])
        _ = ych := ych_eq.symm
    rw [U_of_le hyv]
    have hpos' : 0 < 1 + lam * (k + m * ych) / (k + m + 1) := by positivity
    rcases (by omega : nLeaf cs = 1 ∨ 2 ≤ nLeaf cs) with e | e
    · -- k = 1, m >= 1 (k = 1, m = 0 is the cherry)
      have hk1' : k = 1 := by rw [hk]; exact_mod_cast e
      have hm1 : 1 ≤ nNon cs := by
        by_contra hcon
        have hm00 : nNon cs = 0 := by omega
        apply hnc
        have hlen1 : cs.length = 1 := by omega
        obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen1
        rcases h c List.mem_cons_self with rfl | rfl
        · rfl
        · simp [nNon, isLeaf_cherry] at hm00
      have hm1R : (1:ℝ) ≤ m := by rw [hm]; exact_mod_cast hm1
      rw [hk1']
      have hR : lam * (1 + m * ych) / (1 + m + 1) < lam / 2 := by
        rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        nlinarith [mul_pos hl (mul_pos (by linarith : (0:ℝ) < m) (by linarith : (0:ℝ) < 1 - 2 * ych))]
      have : Real.log (1 + lam * (1 + m * ych) / (1 + m + 1)) < 2 * L := by
        rw [← log_φ_sq, ← one_add_half_lam]
        exact Real.log_lt_log (by positivity) (by linarith)
      linarith
    · have hk2 : (2:ℝ) ≤ k := by rw [hk]; exact_mod_cast e
      have hR : lam * (k + m * ych) / (k + m + 1) < lam := by
        rw [div_lt_iff₀ hd]
        nlinarith [mul_pos hl (by nlinarith : (0:ℝ) < m * (1 - ych) + 1)]
      have hlog : Real.log (1 + lam * (k + m * ych) / (k + m + 1)) < 3 * L := by
        rw [← log_φ_cube, ← one_add_lam]
        exact Real.log_lt_log hpos' (by linarith)
      nlinarith

/-! ### the strict induction -/

def SG (b : Br) : Prop := b = .node [] ∨ b = cherry ∨ ell b < U (msg b)

lemma sg_node (cs : List Br) (h : ∀ c ∈ cs, SG c) : SG (.node cs) := by
  by_cases hne : cs = []
  · left; rw [hne]
  by_cases hnc : cs = [.node []]
  · right; left; rw [hnc]; rfl
  right; right
  have hG : ∀ c ∈ cs, Good c := fun c _ => good_all c
  have hP := pooled_node cs hne hG
  have hellnode : ell (.node cs) = sumEll cs + Real.log (1 + lam * sumY cs / ((cs.length : ℝ) + 1)) - L := ell_node cs
  rw [sumEll_eq] at hellnode
  have h0 : ∀ c ∈ cs, 0 ≤ slack c := fun c hc => slack_nonneg (hG c hc)
  by_cases hex : ∃ c ∈ cs, 0 < slack c
  · have := sumF_pos cs h0 hex
    linarith
  · push Not at hex
    -- every child is a leaf or a cherry
    have hlc : ∀ c ∈ cs, LC c := by
      intro c hc
      rcases h c hc with h1 | h1 | h1
      · left; exact h1
      · right; exact h1
      · exfalso
        have hs := hex c hc
        unfold slack Ehat at hs
        by_cases hl : isLeaf c = true
        · rw [eq_leaf_of_isLeaf hl, ell_leaf] at h1
          have : msg (.node []) = 1 := msg_leaf
          rw [this] at h1
          have hU : U 1 = kap * (ych - 1) := U_of_ge (by linarith [ych_lt_half])
          rw [hU] at h1
          have hy2 : ych < 0.2 := by
            rw [ych_eq', div_lt_iff₀ (by linarith [φ_pos])]; linarith [φ_bounds.1]
          have hφy : φ * (ych - 1) < -1 := by nlinarith [φ_bounds.1, φ_bounds.2, ych_pos]
          have hk : kap * (ych - 1) = L * (φ * (ych - 1)) := by unfold kap; ring
          rw [hk] at h1
          nlinarith [mul_lt_mul_of_pos_left hφy L_pos]
        · rw [if_neg hl] at hs; linarith
    exact lc_strict cs hne hnc hlc

theorem sg_all : ∀ b : Br, SG b := by
  have H : ∀ n : ℕ, ∀ b : Br, size b ≤ n → SG b := by
    intro n
    induction n with
    | zero => intro b hb; cases b with | node cs => simp [size] at hb
    | succ n IH =>
      intro b hb
      cases b with
      | node cs =>
        apply sg_node cs
        intro c hc
        apply IH
        have := size_lt_of_mem cs c hc
        simp only [size] at hb
        omega
  exact fun b => H (size b) b le_rfl

/-- strict anchor: every branch other than the cherry has ell < 0 at lam_c -/
theorem ell_neg (b : Br) (hb : b ≠ cherry) : ell b < 0 := by
  rcases sg_all b with h | h | h
  · rw [h, ell_leaf]; linarith [L_pos]
  · exact absurd h hb
  · linarith [U_le_zero (msg b)]

lemma Tl_cherry (l : ℝ) : Tl l cherry = 1 + l / 2 := by
  rw [cherry, Tl_node]
  simp [prodTl, sumYl, msgl_node, Tl_node]
  ring

/-- strict part: for every l >= 1 + sqrt 5 and every branch other than the cherry, Tl l b < (1 + l/2)^(|b|/2) -/
theorem ceiling_strict (l : ℝ) (hl : 1 + √5 ≤ l) (b : Br) (hb : b ≠ cherry) :
    Tl l b < (1 + l / 2) ^ ((size b : ℝ) / 2) := by
  have hl' : lam ≤ l := by rw [lam_eq]; exact hl
  have hl0 : 0 < l := by linarith [lam_ge_two]
  have hmono := gE_antitone b (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hl') hl'
  have hA := ell_neg b hb
  unfold ell at hA
  rw [← Tl_lam] at hA
  have h2c : Real.log (2 + lam) = Real.log 2 + 2 * Real.log φ := by
    rw [two_add_lam, Real.log_mul (by norm_num) (pow_pos φ_pos 2).ne', Real.log_pow]; push_cast; ring
  unfold gE at hmono
  rw [h2c] at hmono
  have hlogl : Real.log (Tl l b) < (size b : ℝ) / 2 * Real.log (1 + l / 2) := by
    have e : Real.log (1 + l / 2) = Real.log (2 + l) - Real.log 2 := by
      rw [← Real.log_div (by linarith) (by norm_num)]; congr 1; ring
    rw [e]; unfold L at hA; nlinarith
  have hpos : 0 < 1 + l / 2 := by linarith
  rw [Real.rpow_def_of_pos hpos]
  calc Tl l b = Real.exp (Real.log (Tl l b)) := (Real.exp_log (Tl_pos hl0.le b)).symm
    _ < Real.exp (Real.log (1 + l / 2) * ((size b : ℝ) / 2)) := by
        apply Real.exp_lt_exp.mpr; linarith

/-- the branch ceiling for l >= 1 + sqrt 5 with its equality clause -/
theorem Tl_eq_cherry_iff (l : ℝ) (hl : 1 + √5 ≤ l) (b : Br) :
    Tl l b = (1 + l / 2) ^ ((size b : ℝ) / 2) ↔ b = .node [.node []] := by
  constructor
  · intro h
    by_contra hb
    exact (ceiling_strict l hl b hb).ne h
  · intro h
    have hc : b = cherry := h
    subst hc
    rw [Tl_cherry]
    have : (size cherry : ℝ) = 2 := by simp [cherry, size, sizeL]
    rw [this, div_self (by norm_num : (2:ℝ) ≠ 0), Real.rpow_one]

end

end Br

end LeanCherry
