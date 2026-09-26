/-
  R3Cert.BGEnvCert.Envelope -- the Bellman envelope theorem over real tables (2026-09-25).

  With a rational rate `f` in place of `F*` (it cancels exactly between a tree and a spider of the
  same size), `ell_f(b) = log T(b) - |b| f` and `V_μ(b) = ell_f(b) + μ y_b`.  At a vertex with
  `c` children the tangent step (`TanB`) bounds `V_μ(node cs)` by a constant plus `Σ V_ν(child)`,
  and a max-plus knapsack over child sizes bounds the sum.  `envelope` turns per-entry
  inequalities between real tables into the statement

      every branch `b` with at most `C` children per vertex and `|b| ≤ Sm` has
      `V_{μ_g}(b) ≤ wa(|b|, g)`, and `V_{μ_g}(b) ≤ wn(|b|, g)` if `b` is not an atom;

  `knap_root` gives the root sum with at least one non-atom child.  No `sorry`; standard axioms.
-/
import Mathlib
import R3Cert.BGSpiderReduction
import R3Cert.BGSCLStep
import R3Cert.BGEnvCert.Tangent

namespace R3Cert
namespace EnvCert

open R3Cert.BGSCL

/-- `ell_f(b) = log T(b) - |b| f`. -/
noncomputable def bellF (f : ℝ) (b : Branch) : ℝ := Real.log (cav b).2 - (bsize b : ℝ) * f

/-- `V_μ(b) = ell_f(b) + μ y_b`. -/
noncomputable def bVF (f μ : ℝ) (b : Branch) : ℝ := bellF f b + μ * bY b

theorem bellF_eq (f : ℝ) (b : Branch) : bellF f b = bell b + (bsize b : ℝ) * (FSTAR - f) := by
  unfold bellF bell; ring

theorem sum_bellF (f : ℝ) : ∀ cs : List Branch,
    (cs.map (bellF f)).sum = (cs.map bell).sum + (bsizeList cs : ℝ) * (FSTAR - f)
  | [] => by simp [bsizeList]
  | c :: t => by
    simp only [List.map_cons, List.sum_cons, sum_bellF f t, bsizeList, Nat.cast_add, bellF_eq]; ring

theorem bsize_node (cs : List Branch) : bsize (Branch.node cs) = 1 + bsizeList cs := by simp [bsize]

theorem bellF_node (f : ℝ) (cs : List Branch) :
    bellF f (Branch.node cs) = (cs.map (bellF f)).sum
      + (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - f) := by
  rw [bellF_eq, bell_node, sum_bellF, bsize_node]; push_cast; ring

theorem sum_bVF (f μ : ℝ) : ∀ cs : List Branch,
    (cs.map (bVF f μ)).sum = (cs.map (bellF f)).sum + μ * (cs.map bY).sum
  | [] => by simp
  | c :: t => by simp only [List.map_cons, List.sum_cons, sum_bVF f μ t, bVF]; ring

/-- One Bellman step: the tangent bound at a vertex. -/
theorem bVF_le_of_tanB {f μ ν T : ℝ} {c : ℕ} (h : TanB f μ ν c T) (cs : List Branch) (hc : cs.length = c) :
    bVF f μ (Branch.node cs) ≤ T + (cs.map (bVF f ν)).sum := by
  have hS := sumY_nonneg cs
  have ht := h _ hS
  rw [bVF, bellF_node, bY_node, sum_bVF, hc]
  rw [div_eq_mul_one_div μ] at ht
  rw [← hc] at ht ⊢
  have : μ * (1 / (((cs.length : ℝ) + 1) + (cs.map bY).sum)) = μ / (((cs.length : ℝ) + 1) + (cs.map bY).sum) := by
    ring
  linarith

/-! ### Atoms. -/

theorem one_le_bsize (b : Branch) : 1 ≤ bsize b := by cases b; simp [bsize]

theorem bsizeList_pos {x : Branch} {t : List Branch} : 1 ≤ bsizeList (x :: t) := by
  simp only [bsizeList]; have := one_le_bsize x; omega

theorem bsize_eq_one {x : Branch} (h : bsize x = 1) : x = Branch.node [] := by
  obtain ⟨cs⟩ := x
  rcases cs with _ | ⟨y, t⟩
  · rfl
  · simp only [bsize] at h; have := @bsizeList_pos y t; omega

theorem bsize_eq_two {x : Branch} (h : bsize x = 2) : x = cherry := by
  obtain ⟨cs⟩ := x
  rcases cs with _ | ⟨y, t⟩
  · simp [bsize, bsizeList] at h
  · simp only [bsize, bsizeList] at h
    have hy := one_le_bsize y
    have ht : bsizeList t = 0 := by omega
    have hy1 : bsize y = 1 := by omega
    rcases t with _ | ⟨z, u⟩
    · rw [bsize_eq_one hy1]; rfl
    · have := @bsizeList_pos z u; omega

theorem isAtom_leaf : IsAtom (Branch.node []) := Or.inr ⟨0, rfl⟩

theorem nonatom_size {b : Branch} (h : ¬ IsAtom b) : 3 ≤ bsize b := by
  by_contra hlt
  push Not at hlt
  have h1 := one_le_bsize b
  rcases (by omega : bsize b = 1 ∨ bsize b = 2) with h2 | h2
  · exact h (by rw [bsize_eq_one h2]; exact isAtom_leaf)
  · exact h (by rw [bsize_eq_two h2]; exact Or.inl rfl)

theorem nonatom_one {x : Branch} (h : ¬ IsAtom (Branch.node [x])) : 3 ≤ bsize x := by
  by_contra hlt
  push Not at hlt
  have h1 := one_le_bsize x
  rcases (by omega : bsize x = 1 ∨ bsize x = 2) with h2 | h2
  · exact h (by rw [bsize_eq_one h2]; exact Or.inl rfl)
  · exact h (by rw [bsize_eq_two h2]; exact Or.inr ⟨1, rfl⟩)

theorem nonatom_many {cs : List Branch} (h : ¬ IsAtom (Branch.node cs)) : ∃ x ∈ cs, bsize x ≠ 2 := by
  by_contra hall
  push Not at hall
  apply h
  refine Or.inr ⟨cs.length, ?_⟩
  unfold armB
  congr 1
  exact List.eq_replicate_iff.mpr ⟨rfl, fun x hx => bsize_eq_two (hall x hx)⟩

/-! ### The abstract envelope. -/

/-- The per-entry inequalities between the real tables (cap `C`, sizes `≤ Sm`, grid `μ 0..Hg-1`). -/
structure EnvHyp (f : ℝ) (μ : ℕ → ℝ) (Hg C Sm : ℕ) (wa wn : ℕ → ℕ → ℝ) (kk kx : ℕ → ℕ → ℕ → ℝ)
    (k1 : ℕ → ℕ → ℝ) : Prop where
  leaf : ∀ g < Hg, μ g - f ≤ wa 1 g
  k1a : ∀ N h, 1 ≤ N → N ≤ Sm → h < Hg → wa N h ≤ kk 1 N h
  ka : ∀ c N m h, 2 ≤ c → c ≤ C → N ≤ Sm → 1 ≤ m → m ≤ N → h < Hg →
    kk (c - 1) (N - m) h + wa m h ≤ kk c N h
  k1x : ∀ N h, 1 ≤ N → N ≤ Sm → N ≠ 2 → h < Hg → wa N h ≤ kx 1 N h
  kxa : ∀ c N m h, 2 ≤ c → c ≤ C → N ≤ Sm → 1 ≤ m → m ≤ N → h < Hg →
    kx (c - 1) (N - m) h + wa m h ≤ kx c N h
  kxb : ∀ c N m h, 2 ≤ c → c ≤ C → N ≤ Sm → 1 ≤ m → m ≤ N → m ≠ 2 → h < Hg →
    kk (c - 1) (N - m) h + wa m h ≤ kx c N h
  k1p : ∀ N h, 3 ≤ N → N ≤ Sm → h < Hg → wa N h ≤ k1 N h
  ba : ∀ s g c, 2 ≤ s → s ≤ Sm → g < Hg → 1 ≤ c → c ≤ C →
    ∃ h < Hg, ∃ T, TanB f (μ g) (μ h) c T ∧ T + kk c (s - 1) h ≤ wa s g
  bn : ∀ s g c, 3 ≤ s → s ≤ Sm → g < Hg → 1 ≤ c → c ≤ C →
    ∃ h < Hg, ∃ T, TanB f (μ g) (μ h) c T ∧ T + (if c = 1 then k1 (s - 1) h else kx c (s - 1) h) ≤ wn s g

variable {f : ℝ} {μ : ℕ → ℝ} {Hg C Sm : ℕ} {wa wn : ℕ → ℕ → ℝ} {kk kx : ℕ → ℕ → ℕ → ℝ} {k1 : ℕ → ℕ → ℝ}

/-- The all-branch envelope of the children. -/
def EnvA (f : ℝ) (μ : ℕ → ℝ) (Hg : ℕ) (wa : ℕ → ℕ → ℝ) (x : Branch) : Prop :=
  ∀ g < Hg, bVF f (μ g) x ≤ wa (bsize x) g

theorem knap_a (hE : EnvHyp f μ Hg C Sm wa wn kk kx k1) : ∀ cs : List Branch, 1 ≤ cs.length →
    cs.length ≤ C → bsizeList cs ≤ Sm → (∀ x ∈ cs, EnvA f μ Hg wa x) →
    ∀ h < Hg, (cs.map (bVF f (μ h))).sum ≤ kk cs.length (bsizeList cs) h
  | [], h1, _, _, _, _, _ => by simp at h1
  | [x], _, _, hS, hx, h, hh => by
    have hsz : bsizeList [x] = bsize x := by simp [bsizeList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_singleton]
    rw [hsz] at hS ⊢
    exact le_trans (hx x (by simp) h hh) (hE.k1a _ h (one_le_bsize x) hS hh)
  | x :: y :: t, _, hC, hS, hx, h, hh => by
    have hsz : bsizeList (x :: y :: t) = bsize x + bsizeList (y :: t) := by simp [bsizeList]
    have ih := knap_a hE (y :: t) (by simp) (by simp at hC ⊢; omega) (by rw [hsz] at hS; omega)
      (fun z hz => hx z (by simp at hz ⊢; tauto)) h hh
    have hstep := hE.ka (x :: y :: t).length (bsizeList (x :: y :: t)) (bsize x) h (by simp) hC hS
      (one_le_bsize x) (by rw [hsz]; omega) hh
    simp only [List.length_cons] at hstep ih ⊢
    rw [show bsizeList (x :: y :: t) - bsize x = bsizeList (y :: t) by rw [hsz]; omega,
      show t.length + 1 + 1 - 1 = t.length + 1 by omega] at hstep
    have hxv := hx x (by simp) h hh
    rw [List.map_cons, List.sum_cons]
    linarith

theorem knap_x (hE : EnvHyp f μ Hg C Sm wa wn kk kx k1) : ∀ cs : List Branch, 1 ≤ cs.length →
    cs.length ≤ C → bsizeList cs ≤ Sm → (∀ x ∈ cs, EnvA f μ Hg wa x) → (∃ x ∈ cs, bsize x ≠ 2) →
    ∀ h < Hg, (cs.map (bVF f (μ h))).sum ≤ kx cs.length (bsizeList cs) h
  | [], h1, _, _, _, _, _, _ => by simp at h1
  | [x], _, _, hS, hx, hne, h, hh => by
    have hsz : bsizeList [x] = bsize x := by simp [bsizeList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_singleton]
    rw [hsz] at hS ⊢
    obtain ⟨z, hz, hz2⟩ := hne
    simp at hz; subst hz
    exact le_trans (hx z (by simp) h hh) (hE.k1x _ h (one_le_bsize z) hS hz2 hh)
  | x :: y :: t, _, hC, hS, hx, hne, h, hh => by
    have hsz : bsizeList (x :: y :: t) = bsize x + bsizeList (y :: t) := by simp [bsizeList]
    have hxv := hx x (by simp) h hh
    have hidx : bsizeList (x :: y :: t) - bsize x = bsizeList (y :: t) := by rw [hsz]; omega
    rw [List.map_cons, List.sum_cons]
    simp only [List.length_cons]
    by_cases h2 : bsize x = 2
    · obtain ⟨z, hz, hz2⟩ := hne
      have hz' : z ∈ y :: t := by
        rcases List.mem_cons.mp hz with rfl | h'
        · exact absurd h2 hz2
        · exact h'
      have ih := knap_x hE (y :: t) (by simp) (by simp at hC ⊢; omega) (by rw [hsz] at hS; omega)
        (fun z hz => hx z (by simp at hz ⊢; tauto)) ⟨z, hz', hz2⟩ h hh
      have hstep := hE.kxa (t.length + 1 + 1) (bsizeList (x :: y :: t)) (bsize x) h (by omega)
        (by simpa using hC) hS (one_le_bsize x) (by rw [hsz]; omega) hh
      rw [hidx, show t.length + 1 + 1 - 1 = t.length + 1 by omega] at hstep
      simp only [List.length_cons] at ih
      linarith
    · have ih := knap_a hE (y :: t) (by simp) (by simp at hC ⊢; omega) (by rw [hsz] at hS; omega)
        (fun z hz => hx z (by simp at hz ⊢; tauto)) h hh
      have hstep := hE.kxb (t.length + 1 + 1) (bsizeList (x :: y :: t)) (bsize x) h (by omega)
        (by simpa using hC) hS (one_le_bsize x) (by rw [hsz]; omega) h2 hh
      rw [hidx, show t.length + 1 + 1 - 1 = t.length + 1 by omega] at hstep
      simp only [List.length_cons] at ih
      linarith

theorem maxCh_node_ge (cs : List Branch) : cs.length ≤ maxCh (Branch.node cs) := by
  rw [maxCh_node]; exact le_max_left _ _

theorem maxCh_child_le {cs : List Branch} {x : Branch} (hx : x ∈ cs) : maxCh x ≤ maxCh (Branch.node cs) := by
  rw [maxCh_node]; exact le_trans (maxCh_le_of_mem hx) (le_max_right _ _)

theorem bsize_child_lt {cs : List Branch} {x : Branch} (hx : x ∈ cs) :
    bsize x ≤ bsizeList cs := bsize_le_bsizeList hx

/-- **The envelope theorem.** -/
theorem envelope (hE : EnvHyp f μ Hg C Sm wa wn kk kx k1) :
    ∀ b : Branch, maxCh b ≤ C → bsize b ≤ Sm → ∀ g < Hg,
      bVF f (μ g) b ≤ wa (bsize b) g ∧ (¬ IsAtom b → bVF f (μ g) b ≤ wn (bsize b) g) := by
  refine scl_of_child_step bsize bchildren
    (fun b => maxCh b ≤ C → bsize b ≤ Sm → ∀ g < Hg,
      bVF f (μ g) b ≤ wa (bsize b) g ∧ (¬ IsAtom b → bVF f (μ g) b ≤ wn (bsize b) g))
    bchildren_bsize_lt (fun a hIH => ?_)
  obtain ⟨cs⟩ := a
  intro hC hS g hg
  have hsz := bsize_node cs
  -- children
  have hch : ∀ x ∈ cs, EnvA f μ Hg wa x ∧ (¬ IsAtom x → ∀ g < Hg, bVF f (μ g) x ≤ wn (bsize x) g) := by
    intro x hx
    have := hIH x (by simpa [bchildren] using hx) (le_trans (maxCh_child_le hx) hC)
      (by have := bsize_child_lt hx; omega)
    exact ⟨fun g hg => (this g hg).1, fun hna g hg => (this g hg).2 hna⟩
  by_cases hcs : cs = []
  · -- the leaf
    subst hcs
    have hv : bVF f (μ g) (Branch.node []) = μ g - f := by
      rw [bVF, bellF_node, bY_leaf]; simp; ring
    refine ⟨?_, fun hna => absurd isAtom_leaf hna⟩
    rw [hv, show bsize (Branch.node []) = 1 by simp [bsize, bsizeList]]
    exact hE.leaf g hg
  · have hc1 : 1 ≤ cs.length := List.length_pos_of_ne_nil hcs
    have hcC : cs.length ≤ C := le_trans (maxCh_node_ge cs) hC
    have hpos : 1 ≤ bsizeList cs := by
      obtain ⟨x0, t0, rfl⟩ := List.exists_cons_of_ne_nil hcs
      exact bsizeList_pos
    have hs2 : 2 ≤ bsize (Branch.node cs) := by omega
    have hN : bsizeList cs ≤ Sm := by omega
    have hsm1 : bsize (Branch.node cs) - 1 = bsizeList cs := by omega
    constructor
    · obtain ⟨h, hh, T, hT, hle⟩ := hE.ba _ g cs.length hs2 hS hg hc1 hcC
      have h1 := bVF_le_of_tanB hT cs rfl
      have h2 := knap_a hE cs hc1 hcC hN (fun x hx => (hch x hx).1) h hh
      rw [hsm1] at hle
      linarith
    · intro hna
      have hs3 := nonatom_size hna
      obtain ⟨h, hh, T, hT, hle⟩ := hE.bn _ g cs.length hs3 hS hg hc1 hcC
      have h1 := bVF_le_of_tanB hT cs rfl
      rw [hsm1] at hle
      by_cases hc : cs.length = 1
      · rw [if_pos hc] at hle
        obtain ⟨x, rfl⟩ : ∃ x, cs = [x] := List.length_eq_one_iff.mp hc
        have hx3 := nonatom_one hna
        have hsx : bsizeList [x] = bsize x := by simp [bsizeList]
        have hxv := (hch x (by simp)).1 h hh
        have := hE.k1p (bsize x) h hx3 (by rw [← hsx]; exact hN) hh
        rw [hsx] at hle
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
        linarith
      · rw [if_neg hc] at hle
        have h2 := knap_x hE cs hc1 hcC hN (fun x hx => (hch x hx).1) (nonatom_many hna) h hh
        linarith

/-! ### The root. -/

/-- Root knapsack inequalities (`k ≤ kmax` parts, at least one non-atom). -/
structure RootHyp (Hg Sm kmax : ℕ) (wa wn : ℕ → ℕ → ℝ) (kk rr : ℕ → ℕ → ℕ → ℝ) : Prop where
  r1 : ∀ N h, 3 ≤ N → N ≤ Sm → h < Hg → wn N h ≤ rr 1 N h
  ra : ∀ c N m h, 2 ≤ c → c ≤ kmax → N ≤ Sm → 1 ≤ m → m ≤ N → h < Hg →
    rr (c - 1) (N - m) h + wa m h ≤ rr c N h
  rb : ∀ c N m h, 2 ≤ c → c ≤ kmax → N ≤ Sm → 3 ≤ m → m ≤ N → h < Hg →
    kk (c - 1) (N - m) h + wn m h ≤ rr c N h

theorem knap_root (hE : EnvHyp f μ Hg C Sm wa wn kk kx k1) {kmax : ℕ} {rr : ℕ → ℕ → ℕ → ℝ}
    (hR : RootHyp Hg Sm kmax wa wn kk rr) (hk : kmax ≤ C + 1) :
    ∀ cs : List Branch, 1 ≤ cs.length → cs.length ≤ kmax → bsizeList cs ≤ Sm →
      (∀ x ∈ cs, maxCh x ≤ C) → (∃ x ∈ cs, ¬ IsAtom x) →
      ∀ h < Hg, (cs.map (bVF f (μ h))).sum ≤ rr cs.length (bsizeList cs) h := by
  have env := envelope hE
  intro cs
  induction cs with
  | nil => intro h1; simp at h1
  | cons x t ih =>
    intro _ hk' hS hcap hna h hh
    have hsz : bsizeList (x :: t) = bsize x + bsizeList t := by simp [bsizeList]
    have hxS : bsize x ≤ Sm := by omega
    have hx := env x (hcap x (by simp)) hxS h hh
    rw [List.map_cons, List.sum_cons]
    rcases t with _ | ⟨y, t'⟩
    · -- a single child: it is the non-atom
      obtain ⟨z, hz, hzna⟩ := hna
      simp at hz; subst hz
      simp only [List.map_nil, List.sum_nil, add_zero, List.length_singleton]
      rw [show bsizeList [z] = bsize z by simp [bsizeList]]
      exact le_trans (hx.2 hzna) (hR.r1 _ h (nonatom_size hzna) hxS hh)
    · have hidx : bsizeList (x :: y :: t') - bsize x = bsizeList (y :: t') := by rw [hsz]; omega
      simp only [List.length_cons] at hk' ⊢
      by_cases hxa : IsAtom x
      · obtain ⟨z, hz, hzna⟩ := hna
        have hz' : z ∈ y :: t' := by
          rcases List.mem_cons.mp hz with rfl | h'
          · exact absurd hxa hzna
          · exact h'
        have ih' := ih (by simp) (by simp; omega) (by rw [hsz] at hS; omega)
          (fun w hw => hcap w (by simp at hw ⊢; tauto)) ⟨z, hz', hzna⟩ h hh
        have hstep := hR.ra (t'.length + 1 + 1) (bsizeList (x :: y :: t')) (bsize x) h (by omega) hk' hS
          (one_le_bsize x) (by rw [hsz]; omega) hh
        rw [hidx, show t'.length + 1 + 1 - 1 = t'.length + 1 by omega] at hstep
        simp only [List.length_cons] at ih'
        linarith [hx.1]
      · have hka := knap_a hE (y :: t') (by simp) (by simp; omega) (by rw [hsz] at hS; omega)
          (fun w hw => fun g hg => (env w (hcap w (by simp at hw ⊢; tauto))
            (by have := bsize_le_bsizeList hw; rw [hsz] at hS; omega) g hg).1) h hh
        have hstep := hR.rb (t'.length + 1 + 1) (bsizeList (x :: y :: t')) (bsize x) h (by omega) hk' hS
          (nonatom_size hxa) (by rw [hsz]; omega) hh
        rw [hidx, show t'.length + 1 + 1 - 1 = t'.length + 1 by omega] at hstep
        simp only [List.length_cons] at hka
        linarith [hx.2 hxa]

/-! ### The root objective with a rational rate. -/

/-- `log π(cs) - (n-1) f`. -/
noncomputable def phiF (f : ℝ) (cs : List Branch) : ℝ := Real.log (piRoot cs) - (bsizeList cs : ℝ) * f

theorem phiF_eq (f : ℝ) (cs : List Branch) : phiF f cs = phiRoot cs + (bsizeList cs : ℝ) * (FSTAR - f) := by
  unfold phiF phiRoot; ring

theorem sum_bVF_eq (f μ : ℝ) (cs : List Branch) :
    (cs.map (bVF f μ)).sum = (cs.map (bV μ)).sum + (bsizeList cs : ℝ) * (FSTAR - f) := by
  rw [sum_bVF, sum_bellF, sum_map_bV]; ring

/-- The root tangent bound with the rational rate. -/
theorem phiF_le_tangent (f : ℝ) (cs : List Branch) (hcs : cs ≠ []) {t : ℝ} (ht : 0 < t) :
    phiF f cs ≤ Real.log t + 1 / t - 1 + (cs.map (bVF f (1 / ((cs.length : ℝ) * t)))).sum := by
  have := phiRoot_le_tangent cs hcs ht
  rw [phiF_eq, sum_bVF_eq]; linarith

theorem piRoot_lt_of_phiF (f : ℝ) {cs ds : List Branch} (hsz : bsizeList cs = bsizeList ds)
    (h : phiF f cs < phiF f ds) : piRoot cs < piRoot ds := by
  unfold phiF at h
  rw [hsz] at h
  exact (Real.log_lt_log_iff (piRoot_pos _) (piRoot_pos _)).mp (by linarith)

end EnvCert
end R3Cert
