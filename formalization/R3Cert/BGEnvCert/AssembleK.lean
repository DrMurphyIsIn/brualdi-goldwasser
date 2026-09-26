/-
  R3Cert.BGEnvCert.AssembleK -- the envelope certificate with coverage up to a root degree `K`.

  Same argument as `envcert_generic`, but the coverage check `coverOKK` only asks for root degrees
  `k ≤ K` (roots of larger degree are handled by the high-degree theorems), and the capped checks may be
  given through `capCheckF` (the evaluation-forcing loop, `capCheckF_eq`).
  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Force

namespace R3Cert
namespace EnvCert

open R3Cert.BGSCL

/-- Every `(n, k)` with `nmin ≤ n ≤ nmax`, `2 ≤ k ≤ min (n - 1) K` has a root entry in a cap with `C ≥ k - 1`. -/
def coverOKK (caps : List CapData) (nmin nmax K : ℕ) : Bool :=
  (List.range' nmin (nmax + 1 - nmin)).all fun n =>
    (List.range' 2 (min (n - 1) K - 1)).all fun k =>
      caps.any fun d => decide (k ≤ d.C + 1) && d.roots.any fun e => e.1 == n && e.2.1 == k

theorem envcert_generic_K (tt : TanTab) (ld : LdTab) (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ)
    (D : ℕ) (caps : List CapData) (nmin nmax K : ℕ)
    (hT : tanOK tt 0 HG = true) (hL : ldOK ld D = true)
    (hcaps : ∀ d ∈ caps, capCheck tt ld ph d = true ∧ d.C + 1 ≤ D)
    (hcov : coverOKK caps nmin nmax K = true) (hsp : spidersOK ph sp sm nmin nmax = true)
    (cs : List BGSCL.Branch) (hk2 : 2 ≤ cs.length) (hkK : cs.length ≤ K)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length)
    (hn1 : nmin ≤ bsizeList cs + 1) (hn2 : bsizeList cs + 1 ≤ nmax) (hna : ∃ c ∈ cs, ¬ IsAtom c) :
    (∀ c ∈ (sp.getD (bsizeList cs + 1) []).map atomB, IsAtom c) ∧
      bsizeList ((sp.getD (bsizeList cs + 1) []).map atomB) = bsizeList cs ∧
      piRoot cs < piRoot ((sp.getD (bsizeList cs + 1) []).map atomB) := by
  set n := bsizeList cs + 1 with hn
  have hkn := length_le_bsizeList cs
  unfold coverOKK at hcov
  have hn' := (List.all_eq_true.mp hcov) n (by simp only [List.mem_range'_1]; omega)
  have hk' := (List.all_eq_true.mp hn') cs.length (by
    simp only [List.mem_range'_1]; constructor <;> omega)
  obtain ⟨d, hd, hdk⟩ := List.any_eq_true.mp hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdk
  obtain ⟨hkC, hroot⟩ := hdk
  obtain ⟨e, he, hen⟩ := List.any_eq_true.mp hroot
  simp only [Bool.and_eq_true, beq_iff_eq] at hen
  obtain ⟨hchk, hDle⟩ := hcaps d hd
  have hup := capSound tt ld ph D d hT hL hDle hchk e he cs hen.2.symm (by rw [hen.1]; omega)
    (fun x hx => by have := hcap x hx; omega) hna
  have hs := (List.all_eq_true.mp hsp) n (by simp only [List.mem_range'_1]; omega)
  obtain ⟨hssz, hlo⟩ := spider_sound ph sp sm n hs
  rw [hen.1] at hup
  refine ⟨fun c hc => ?_, by omega, piRoot_lt_of_phiF (fq : ℝ) (by omega) (by linarith)⟩
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  exact atom_isAtom a

end EnvCert
end R3Cert
