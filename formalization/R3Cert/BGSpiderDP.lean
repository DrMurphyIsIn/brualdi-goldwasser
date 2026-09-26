/-
  A small verified max-plus knapsack over integer-weighted "types" (size, weight), evaluated by the kernel.

  `dpRows tys BM K` builds rows `r_0 .. r_K`, each of length `BM + 1`, with `r_0 = 0` and
  `r_{c+1} = max over (s, w) ∈ tys of (r_c shifted right by s) + w` (entries off the table are `NEGI`).
  `dp_sound`: for any list of types `L ⊆ tys` with total size `≤ B ≤ BM`,
  `Σ w ≤ (dpRows tys BM L.length).getD B NEGI`.  No `sorry`; standard axioms.
-/
import Mathlib

namespace R3Cert
namespace BGSCL

def NEGI : ℤ := -(10 ^ 40)

/-- Row shifted right by `s` (filled with `NEGI`), plus `w`, truncated to length `L`. -/
def shiftRow (L s : ℕ) (w : ℤ) (r : List ℤ) : List ℤ :=
  (List.replicate s NEGI ++ r.map (· + w)).take L

def zmax (a b : List ℤ) : List ℤ := List.zipWith max a b

def stepRow (tys : List (ℕ × ℤ)) (L : ℕ) (r : List ℤ) : List ℤ :=
  tys.foldl (fun acc p => zmax acc (shiftRow L p.1 p.2 r)) (List.replicate L NEGI)

/-- Row `c` of the table. -/
def dpRow (tys : List (ℕ × ℤ)) (L : ℕ) : ℕ → List ℤ
  | 0 => List.replicate L 0
  | c + 1 => stepRow tys L (dpRow tys L c)

theorem length_shiftRow (L s : ℕ) (w : ℤ) (r : List ℤ) (h : L ≤ s + r.length) :
    (shiftRow L s w r).length = L := by
  simp [shiftRow, List.length_take, List.length_append, List.length_replicate, List.length_map]; omega

theorem length_zmax (a b : List ℤ) : (zmax a b).length = min a.length b.length := by
  simp [zmax, List.length_zipWith]

theorem length_stepRow_aux (tys : List (ℕ × ℤ)) (L : ℕ) (r : List ℤ) (hr : r.length = L) :
    ∀ acc : List ℤ, acc.length = L →
      (tys.foldl (fun acc p => zmax acc (shiftRow L p.1 p.2 r)) acc).length = L := by
  induction tys with
  | nil => intro acc h; simpa using h
  | cons p t ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      rw [length_zmax, h, length_shiftRow _ _ _ _ (by omega)]; simp

theorem length_dpRow (tys : List (ℕ × ℤ)) (L : ℕ) : ∀ c, (dpRow tys L c).length = L
  | 0 => by simp [dpRow]
  | c + 1 => by
      simp only [dpRow, stepRow]
      exact length_stepRow_aux tys L _ (length_dpRow tys L c) _ (by simp)

theorem getD_zmax (a b : List ℤ) (i : ℕ) (ha : i < a.length) (hb : i < b.length) :
    (zmax a b).getD i NEGI = max (a.getD i NEGI) (b.getD i NEGI) := by
  simp only [zmax, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
  simp

theorem getD_shiftRow (L s : ℕ) (w : ℤ) (r : List ℤ) (i : ℕ) (hs : s ≤ i) (hi : i < L)
    (hr : i - s < r.length) :
    (shiftRow L s w r).getD i NEGI = r.getD (i - s) NEGI + w := by
  simp only [shiftRow, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt hi, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, List.getElem?_map]
  rw [List.getElem?_eq_getElem hr]
  simp

/-- The fold dominates each shifted row entrywise. -/
theorem foldl_ge (tys : List (ℕ × ℤ)) (L : ℕ) (r : List ℤ) (hr : r.length = L) (i : ℕ) (hi : i < L) :
    ∀ acc : List ℤ, acc.length = L →
      (∀ p ∈ tys, p.1 ≤ i → (shiftRow L p.1 p.2 r).getD i NEGI
          ≤ (tys.foldl (fun acc p => zmax acc (shiftRow L p.1 p.2 r)) acc).getD i NEGI) ∧
      acc.getD i NEGI ≤ (tys.foldl (fun acc p => zmax acc (shiftRow L p.1 p.2 r)) acc).getD i NEGI := by
  induction tys with
  | nil => intro acc _; simp
  | cons p t ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      have hlen : (zmax acc (shiftRow L p.1 p.2 r)).length = L := by
        rw [length_zmax, hacc, length_shiftRow _ _ _ _ (by omega)]; simp
      obtain ⟨ih1, ih2⟩ := ih _ hlen
      have hsh : (shiftRow L p.1 p.2 r).length = L := length_shiftRow _ _ _ _ (by omega)
      have hz := getD_zmax acc (shiftRow L p.1 p.2 r) i (by omega) (by omega)
      refine ⟨fun q hq hqi => ?_, ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rw [hz] at ih2; exact le_trans (le_max_right _ _) ih2
        · exact ih1 q hq' hqi
      · rw [hz] at ih2; exact le_trans (le_max_left _ _) ih2

theorem stepRow_ge (tys : List (ℕ × ℤ)) (L : ℕ) (r : List ℤ) (hr : r.length = L) {s : ℕ} {w : ℤ}
    (hp : (s, w) ∈ tys) (i : ℕ) (hs : s ≤ i) (hi : i < L) :
    r.getD (i - s) NEGI + w ≤ (stepRow tys L r).getD i NEGI := by
  have := (foldl_ge tys L r hr i hi (List.replicate L NEGI) (by simp)).1 (s, w) hp hs
  rw [getD_shiftRow L s w r i hs hi (by omega)] at this
  exact this

/-- **Soundness of the DP.** -/
theorem dp_sound (tys : List (ℕ × ℤ)) (L : ℕ) :
    ∀ (ps : List (ℕ × ℤ)), (∀ p ∈ ps, p ∈ tys) → ∀ B, (ps.map Prod.fst).sum ≤ B → B < L →
      (ps.map Prod.snd).sum ≤ (dpRow tys L ps.length).getD B NEGI
  | [], _, B, _, hB => by
      simp only [List.map_nil, List.sum_nil, List.length_nil, dpRow]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp [hB]
  | p :: ps, hsub, B, hsz, hB => by
      simp only [List.map_cons, List.sum_cons] at hsz ⊢
      have hp := hsub p (by simp)
      have ih := dp_sound tys L ps (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) (B - p.1)
        (by omega) (by omega)
      have hst := stepRow_ge tys L (dpRow tys L ps.length) (length_dpRow tys L _)
        (s := p.1) (w := p.2) (by simpa using hp) B (by omega) hB
      simp only [List.length_cons, dpRow]
      linarith

end BGSCL
end R3Cert
