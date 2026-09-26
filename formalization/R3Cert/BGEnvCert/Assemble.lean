/-
  R3Cert.BGEnvCert.Assemble -- combining cap certificates into the finite-range theorem (2026-09-25).

  `envcert_generic`: given passing checks for a list of caps, the shared tangent / `log d` tables,
  a coverage check (every `(n, k)` with `nmin ≤ n ≤ nmax`, `2 ≤ k ≤ n - 1` has a root entry in a cap
  with `C ≥ k - 1`) and the spider certificates, every root list `cs` of a maximum-degree rooting on
  `n` vertices with a non-atom child is strictly beaten by the certified spider on `n` vertices.
  `envcert_utree` states it for actual trees (`UTree`, `Aobj = per(L)/Π deg`).
  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Sound
import R3Cert.BGEnvCert.Spider
import R3Cert.BGMaximizer

namespace R3Cert
namespace EnvCert

open R3Cert.BGSCL

/-- Every `(n, k)` in range is covered by a root entry of a cap with `C ≥ k - 1`. -/
def coverOK (caps : List CapData) (nmin nmax : ℕ) : Bool :=
  (List.range' nmin (nmax + 1 - nmin)).all fun n =>
    (List.range' 2 (n - 2)).all fun k =>
      caps.any fun d => decide (k ≤ d.C + 1) && d.roots.any fun e => e.1 == n && e.2.1 == k

/-- The spider certificates for `nmin ≤ n ≤ nmax`. -/
def spidersOK (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ) (nmin nmax : ℕ) : Bool :=
  (List.range' nmin (nmax + 1 - nmin)).all (spiderOK ph sp sm)

theorem length_le_bsizeList : ∀ cs : List BGSCL.Branch, cs.length ≤ bsizeList cs
  | [] => le_rfl
  | c :: t => by
    simp only [List.length_cons, bsizeList]
    have := one_le_bsize c; have := length_le_bsizeList t; omega

theorem envcert_generic (tt : TanTab) (ld : LdTab) (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ)
    (D : ℕ) (caps : List CapData) (nmin nmax : ℕ)
    (hT : tanOK tt 0 HG = true) (hL : ldOK ld D = true)
    (hcaps : ∀ d ∈ caps, capCheck tt ld ph d = true ∧ d.C + 1 ≤ D)
    (hcov : coverOK caps nmin nmax = true) (hsp : spidersOK ph sp sm nmin nmax = true)
    (cs : List BGSCL.Branch) (hk2 : 2 ≤ cs.length) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length)
    (hn1 : nmin ≤ bsizeList cs + 1) (hn2 : bsizeList cs + 1 ≤ nmax) (hna : ∃ c ∈ cs, ¬ IsAtom c) :
    (∀ c ∈ (sp.getD (bsizeList cs + 1) []).map atomB, IsAtom c) ∧
      bsizeList ((sp.getD (bsizeList cs + 1) []).map atomB) = bsizeList cs ∧
      piRoot cs < piRoot ((sp.getD (bsizeList cs + 1) []).map atomB) := by
  set n := bsizeList cs + 1 with hn
  have hkn := length_le_bsizeList cs
  -- coverage
  unfold coverOK at hcov
  have hn' := (List.all_eq_true.mp hcov) n (by simp only [List.mem_range'_1]; omega)
  have hk' := (List.all_eq_true.mp hn') cs.length (by simp only [List.mem_range'_1]; omega)
  obtain ⟨d, hd, hdk⟩ := List.any_eq_true.mp hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdk
  obtain ⟨hkC, hroot⟩ := hdk
  obtain ⟨e, he, hen⟩ := List.any_eq_true.mp hroot
  simp only [Bool.and_eq_true, beq_iff_eq] at hen
  obtain ⟨hchk, hDle⟩ := hcaps d hd
  have hup := capSound tt ld ph D d hT hL hDle hchk e he cs hen.2.symm (by rw [hen.1]; omega)
    (fun x hx => by have := hcap x hx; omega) hna
  -- the spider
  have hs := (List.all_eq_true.mp hsp) n (by simp only [List.mem_range'_1]; omega)
  obtain ⟨hssz, hlo⟩ := spider_sound ph sp sm n hs
  rw [hen.1] at hup
  refine ⟨fun c hc => ?_, by omega, piRoot_lt_of_phiF (fq : ℝ) (by omega) (by linarith)⟩
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  exact atom_isAtom a

/-! ### Actual trees. -/

open R3Cert.RTree R3Cert.Step3 BGMax

/-- The certified spider on `n` vertices, as a tree. -/
def spiderT (sp : List (List ℕ)) (n : ℕ) : UTree := UTree.node (((sp.getD n []).map atomB).map toU)

theorem fromU_toU_atom (c : ℕ) : fromU (toU (atomB c)) = atomB c := by
  cases c with
  | zero => simp only [atomB]; rw [toU_cherry, fromU_cherryU]
  | succ j => simp only [atomB]; rw [toU_armB, fromU_armU]

theorem map_fromU_spider (L : List ℕ) : ((L.map atomB).map toU).map fromU = L.map atomB := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left; intro c _; exact fromU_toU_atom c

/-- **The finite-range theorem for trees.**  Every tree `t` with `nmin ≤ |t| ≤ nmax` either reroots
    to a spider (a centre whose children are cherries and arms), or has `Aobj t` strictly below the
    certified spider `spiderT sp |t|`, which has the same number of vertices. -/
theorem envcert_utree (tt : TanTab) (ld : LdTab) (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ)
    (D : ℕ) (caps : List CapData) (nmin nmax : ℕ) (h3 : 3 ≤ nmin)
    (hT : tanOK tt 0 HG = true) (hL : ldOK ld D = true)
    (hcaps : ∀ d ∈ caps, capCheck tt ld ph d = true ∧ d.C + 1 ≤ D)
    (hcov : coverOK caps nmin nmax = true) (hsp : spidersOK ph sp sm nmin nmax = true)
    (t : UTree) (h1 : nmin ≤ usize t) (h2 : usize t ≤ nmax) :
    usize (spiderT sp (usize t)) = usize t ∧
      ((∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧ RerootRel t (UTree.node cs)) ∨
        Aobj t < Aobj (spiderT sp (usize t))) := by
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
  have hN := usize_eq_bsizeList cs'
  have hspsz : usize (spiderT sp (usize t)) = usize t := by
    by_cases hna : ∃ c ∈ cs'.map fromU, ¬ IsAtom c
    · obtain ⟨_, hsz, _⟩ := envcert_generic tt ld ph sp sm D caps nmin nmax hT hL hcaps hcov hsp _ hk2
        hcap (by omega) (by omega) hna
      unfold spiderT
      rw [usize_eq_bsizeList, map_fromU_spider, show bsizeList (cs'.map fromU) + 1 = usize t by omega] at *
      omega
    · -- the spider certificate alone gives the size
      have hs := (List.all_eq_true.mp hsp) (usize t) (by simp only [List.mem_range'_1]; omega)
      obtain ⟨hssz, _⟩ := spider_sound ph sp sm _ hs
      unfold spiderT
      rw [usize_eq_bsizeList, map_fromU_spider]; omega
  refine ⟨hspsz, ?_⟩
  by_cases hna : ∃ c ∈ cs'.map fromU, ¬ IsAtom c
  · right
    obtain ⟨_, _, hlt⟩ := envcert_generic tt ld ph sp sm D caps nmin nmax hT hL hcaps hcov hsp _ hk2
      hcap (by omega) (by omega) hna
    rw [hA, Aobj_eq_piRoot]
    unfold spiderT
    rw [Aobj_eq_piRoot, map_fromU_spider]
    rw [show bsizeList (cs'.map fromU) + 1 = usize t by omega] at hlt
    exact hlt
  · left
    push Not at hna
    exact ⟨cs', fun c hc => atom_of_fromU (hna _ (List.mem_map_of_mem hc)), hrr⟩

end EnvCert
end R3Cert
