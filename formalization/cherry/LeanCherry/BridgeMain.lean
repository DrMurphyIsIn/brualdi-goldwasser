/-
LeanCherry.BridgeMain -- proof of Tl_eq_matching_sum (the cavity recursion for planted branches).
-/
import LeanCherry.Bridge

open Finset LeanCherry.MatchSum

namespace LeanCherry

namespace Br

noncomputable section

/-- weight bookkeeping for a list of children numbered from i, inside a root of planted degree D -/
def Fits (l D : ℝ) (W : List ℕ × List ℕ → ℝ) : ℕ → List Br → Prop
  | _, [] => True
  | i, c :: L => (∀ e, W (sh i e) = wt l c e) ∧ W ([], [i]) = l / (D * ((nch c : ℝ) + 1)) ∧ Fits l D W (i + 1) L

lemma edges_node (gs : List Br) : edges (.node gs) = fanE 0 gs := by rw [edges]

lemma Z_sh {l : ℝ} {c : Br} {W : List ℕ × List ℕ → ℝ} {i : ℕ} (hW : ∀ e, W (sh i e) = wt l c e)
    (E : Finset (List ℕ × List ℕ)) : Z W (E.map (sh i)) = Z (wt l c) E :=
  Z_map (consE i) (wt l c) W E (fun e _ => hW e)

/-- the forest: Z of the shifted children = product of their T's -/
lemma rest_Z {l D : ℝ} {W : List ℕ × List ℕ → ℝ} : ∀ (i : ℕ) (L : List Br), Fits l D W i L →
    (∀ c ∈ L, Z (wt l c) (edges c) = Tl l c) → Z W (restE i L) = prodTl l L
  | _, [], _, _ => by simp [restE, prodTl, Z_empty]
  | i, c :: L, ⟨h1, _, h3⟩, hIH => by
      rw [restE, Z_union W _ _ (disj_sh_rest i (edges c) L), Z_sh h1, hIH c (List.mem_cons_self ..),
        rest_Z (i + 1) L h3 (fun c' hc' => hIH c' (List.mem_cons_of_mem _ hc')), prodTl]

lemma msgl_mul_Tl {l : ℝ} (hl : 0 ≤ l) (gs : List Br) :
    msgl l (.node gs) * Tl l (.node gs) = prodTl l gs / ((gs.length : ℝ) + 1) := by
  rw [msgl_node, Tl_node]
  have h0 := sumYl_nonneg hl gs
  have hpos : 0 < (gs.length : ℝ) + 1 + l * sumYl l gs := by positivity
  have hd : (0:ℝ) < (gs.length : ℝ) + 1 := by positivity
  field_simp

/-- the fan at a root of planted degree D -/
lemma fan_Z {l D : ℝ} (hl : 0 ≤ l) {W : List ℕ × List ℕ → ℝ} : ∀ (i : ℕ) (L : List Br), Fits l D W i L →
    (∀ c ∈ L, Z (wt l c) (edges c) = Tl l c ∧ Z (wt l c) (restE 0 (kids c)) = prodTl l (kids c)) →
    Z W (fanE i L) = prodTl l L * (1 + l * sumYl l L / D)
  | _, [], _, _ => by simp [fanE, prodTl, sumYl, Z_empty]
  | i, c :: L, ⟨h1, h2, h3⟩, hIH => by
      obtain ⟨hc1, hc2⟩ := hIH c (List.mem_cons_self ..)
      have hIH' : ∀ c' ∈ L, Z (wt l c') (edges c') = Tl l c' ∧ Z (wt l c') (restE 0 (kids c')) = prodTl l (kids c') :=
        fun c' hc' => hIH c' (List.mem_cons_of_mem _ hc')
      set r : List ℕ × List ℕ := ([], [i]) with hr
      have hrA : r ∉ (edges c).map (sh i) := by
        intro h; obtain ⟨e, _, he⟩ := mem_map.mp h
        rw [sh_apply] at he; exact List.cons_ne_nil _ _ (congrArg Prod.fst he)
      have hrB : r ∉ fanE (i + 1) L := by
        intro h
        rcases fanE_verts (i + 1) L r h [i] (by simp [r, ev]) with h' | ⟨k, u, hk, h'⟩
        · exact List.cons_ne_nil _ _ h'
        · have := (List.cons.inj h').1; omega
      -- predicates
      have hpredA : ∀ f ∈ (edges c).map (sh i), (Disjoint (ev r) (ev f) ↔ ∃ g ∈ (edges c).filter (fun g => ([] : List ℕ) ∉ ev g), sh i g = f) := by
        intro f hf
        obtain ⟨g, hg, rfl⟩ := mem_map.mp hf
        constructor
        · intro hd
          refine ⟨g, mem_filter.mpr ⟨hg, fun h0 => ?_⟩, rfl⟩
          have : (i :: ([] : List ℕ)) ∈ ev (sh i g) := by
            simp only [ev, sh_apply, mem_insert, mem_singleton] at h0 ⊢
            rcases h0 with h0 | h0 <;> [left; right] <;> rw [h0]
          exact Finset.disjoint_left.mp hd (by simp [r, ev]) this
        · rintro ⟨g', hg', hgg⟩
          have hgg' : g' = g := (sh i).injective hgg
          subst hgg'
          have h0 := (mem_filter.mp hg').2
          rw [Finset.disjoint_left]
          intro v hvr hvf
          simp only [ev, r, mem_insert, mem_singleton] at hvr
          simp only [ev, sh_apply, mem_insert, mem_singleton] at hvf
          rcases hvr with rfl | rfl
          · rcases hvf with h | h <;> exact List.cons_ne_nil _ _ h.symm
          · apply h0
            simp only [ev, mem_insert, mem_singleton]
            rcases hvf with h | h
            · left; exact (List.cons.inj h).2
            · right; exact (List.cons.inj h).2
      have hfilA : ((edges c).map (sh i)).filter (fun f => Disjoint (ev r) (ev f))
          = (restE 0 (kids c)).map (sh i) := by
        cases c with
        | node gs =>
          rw [show kids (.node gs) = gs from rfl, ← fanE_filter_root 0 gs, ← edges_node]
          ext f
          simp only [mem_filter, mem_map]
          constructor
          · rintro ⟨⟨g, hg, rfl⟩, hd⟩
            obtain ⟨g', hg', he⟩ := (hpredA _ (mem_map_of_mem _ hg)).mp hd
            exact ⟨g', mem_filter.mp hg', he⟩
          · rintro ⟨g, ⟨hg, h0⟩, rfl⟩
            exact ⟨⟨g, hg, rfl⟩, (hpredA _ (mem_map_of_mem _ hg)).mpr ⟨g, mem_filter.mpr ⟨hg, h0⟩, rfl⟩⟩
      have hfilB : (fanE (i + 1) L).filter (fun f => Disjoint (ev r) (ev f)) = restE (i + 1) L := by
        rw [← fanE_filter_root (i + 1) L]
        apply filter_congr
        intro f hf
        constructor
        · intro hd h0; exact Finset.disjoint_left.mp hd (by simp [r, ev]) h0
        · intro h0
          rw [Finset.disjoint_left]
          intro v hvr hvf
          simp only [ev, r, mem_insert, mem_singleton] at hvr
          rcases hvr with rfl | rfl
          · exact h0 hvf
          · rcases fanE_verts (i + 1) L f hf _ hvf with h' | ⟨k, u, hk, h'⟩
            · exact List.cons_ne_nil _ _ h'
            · have := (List.cons.inj h').1; omega
      rw [fanE, Z_insert W (by rw [mem_union]; rintro (h | h); exacts [hrA h, hrB h]),
        Z_union W _ _ (disj_sh_fan i (edges c) L), filter_union, hfilA, hfilB,
        Z_union W _ _ (disj_sh_rest i _ L), Z_sh h1, Z_sh h1, hc1, hc2,
        fan_Z hl (i + 1) L h3 hIH', rest_Z (i + 1) L h3 (fun c' hc' => (hIH' c' hc').1), h2]
      simp only [prodTl, sumYl]
      cases c with
      | node gs =>
        have key := msgl_mul_Tl hl gs
        simp only [nch, kids] at key ⊢
        have hd : (0:ℝ) < (gs.length : ℝ) + 1 := by positivity
        rcases eq_or_ne D 0 with hD | hD
        · subst hD; simp
        · have hP : prodTl l gs = msgl l (.node gs) * Tl l (.node gs) * ((gs.length : ℝ) + 1) := by
            rw [key]; field_simp
          field_simp
          rw [hP]
          ring

lemma drop_getElem? {cs L : List Br} {i : ℕ} {c : Br} (h : cs.drop i = c :: L) : cs[i]? = some c := by
  have := congrArg (fun x : List Br => x[0]?) h
  simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
  exact this

lemma drop_succ_of {cs L : List Br} {i : ℕ} {c : Br} (h : cs.drop i = c :: L) : cs.drop (i + 1) = L := by
  rw [← List.drop_drop, h]; rfl

lemma fits_self (l : ℝ) (cs : List Br) : ∀ (L : List Br) (i : ℕ), cs.drop i = L →
    Fits l ((cs.length : ℝ) + 1) (wt l (.node cs)) i L
  | [], _, _ => trivial
  | c :: L, i, h => by
      have hc := drop_getElem? h
      exact ⟨fun e => wt_sh hc e, wt_root hc, fits_self l cs L (i + 1) (drop_succ_of h)⟩

lemma size_le_of_mem : ∀ (cs : List Br) (c : Br), c ∈ cs → size c ≤ sizeL cs
  | [], c, h => by simp at h
  | d :: cs, c, h => by
      simp only [sizeL]
      rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have := size_le_of_mem cs c h'; omega

/-- planted branches: the cavity recursion equals the lambda-weighted matching sum -/
theorem Tl_eq_matching_sum {l : ℝ} (hl : 0 ≤ l) (b : Br) : Tl l b = Zl l b := by
  have H : ∀ n : ℕ, ∀ b : Br, size b ≤ n →
      Z (wt l b) (edges b) = Tl l b ∧ Z (wt l b) (restE 0 (kids b)) = prodTl l (kids b) := by
    intro n
    induction n with
    | zero => intro b hb; cases b with | node cs => simp [size] at hb
    | succ n IH =>
      intro b hb
      cases b with
      | node cs =>
        have hIH : ∀ c ∈ cs, Z (wt l c) (edges c) = Tl l c ∧ Z (wt l c) (restE 0 (kids c)) = prodTl l (kids c) := by
          intro c hc; apply IH; have := size_le_of_mem cs c hc; simp only [size] at hb; omega
        have hfit := fits_self l cs cs 0 (List.drop_zero)
        refine ⟨?_, ?_⟩
        · rw [edges_node, fan_Z hl 0 cs hfit hIH, Tl_node]
        · exact rest_Z 0 cs hfit (fun c hc => (hIH c hc).1)
  exact ((H (size b) b le_rfl).1).symm

end

end Br

end LeanCherry
