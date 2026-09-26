/-
  R3Cert.BGEnvCert.Spider -- exact spider values and their certified lower bounds (2026-09-25).

  A spider is a root whose children are atoms: code `0` is the cherry, code `j + 1` is `armB j`
  (`armB 0` = leaf).  Its objective is the explicit rational
      `π = Π T_c · (1 + Σ y_c / k)`,  `T(cherry) = 3/2`, `T(arm_j) = (3/2)^j (4j+3)/(3j+3)`,
  `y(cherry) = 1/3`, `y(arm_j) = 3/(4j+3)` (`piRoot_atoms`).  `spiderOK` checks
  `Φ(n) ≤ 2^P (log π - (n-1) fq)` through `logLB`.  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Check

namespace R3Cert
namespace EnvCert

open R3Cert.BGSCL

/-- The atom with code `c`. -/
def atomB : ℕ → Branch
  | 0 => cherry
  | j + 1 => armB j

def spT (c : ℕ) : ℚ := if c = 0 then 3 / 2 else (3 / 2) ^ (c - 1) * ((4 * ((c - 1 : ℕ) : ℚ) + 3) / (3 * ((c - 1 : ℕ) : ℚ) + 3))
def spY (c : ℕ) : ℚ := if c = 0 then 1 / 3 else 3 / (4 * ((c - 1 : ℕ) : ℚ) + 3)
def spSz (c : ℕ) : ℕ := if c = 0 then 2 else 2 * (c - 1) + 1

/-- The spider objective, exactly. -/
def spQ (cs : List ℕ) : ℚ := (cs.map spT).prod * (1 + (cs.map spY).sum / (cs.length : ℚ))

theorem cav_cherry : cav cherry = (1, 3 / 2) := by
  simp [cherry, cav, cavAgg, bcc]; norm_num

theorem cav_armB_snd (j : ℕ) :
    (cav (armB j)).2 = (3 / 2 : ℝ) ^ j * ((4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3)) := by
  have h1 := cavAgg_fst (List.replicate j cherry)
  have h2 := cavAgg_snd (List.replicate j cherry)
  rw [List.map_replicate, List.prod_replicate, cav_cherry] at h1
  rw [List.map_replicate, List.sum_replicate, bY_cherry, nsmul_eq_mul] at h2
  simp only [armB, cav, List.length_replicate]
  rw [h1, h2]
  have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  field_simp
  ring

theorem atom_T (c : ℕ) : (cav (atomB c)).2 = ((spT c : ℚ) : ℝ) := by
  cases c with
  | zero => simp [atomB, spT, cav_cherry]
  | succ j =>
    simp only [atomB, spT, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, cav_armB_snd]
    push_cast; ring

theorem atom_Y (c : ℕ) : bY (atomB c) = ((spY c : ℚ) : ℝ) := by
  cases c with
  | zero => simp [atomB, spY, bY_cherry]
  | succ j =>
    simp only [atomB, spY, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, bY_armB]
    push_cast; ring

theorem atom_sz (c : ℕ) : bsize (atomB c) = spSz c := by
  cases c with
  | zero => simp [atomB, spSz, bsize_cherry]
  | succ j => simp [atomB, spSz, bsize_armB]

theorem atom_isAtom (c : ℕ) : IsAtom (atomB c) := by
  cases c with
  | zero => exact Or.inl rfl
  | succ j => exact Or.inr ⟨j, rfl⟩

theorem bsizeList_atoms (cs : List ℕ) : bsizeList (cs.map atomB) = (cs.map spSz).sum := by
  rw [bsizeList_eq_sum, List.map_map]
  congr 1
  apply List.map_congr_left; intro c _; exact atom_sz c

theorem piRoot_atoms (cs : List ℕ) : piRoot (cs.map atomB) = ((spQ cs : ℚ) : ℝ) := by
  unfold piRoot spQ
  rw [List.map_map, List.map_map, List.length_map]
  push_cast
  congr 2
  · rw [List.map_map]; apply List.map_congr_left; intro c _; exact atom_T c
  · congr 2; rw [List.map_map]; apply List.map_congr_left; intro c _; exact atom_Y c

/-- The spider certificate for size `n`. -/
def spiderOK (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ) (n : ℕ) : Bool :=
  decide (sp.getD n [] ≠ []) && decide (((sp.getD n []).map spSz).sum + 1 = n) &&
    logOK (spQ (sp.getD n [])) (sm.getD n 0) &&
    decide ((phiOf ph n : ℚ) ≤ (2 : ℚ) ^ PB * (logLB (spQ (sp.getD n [])) (sm.getD n 0) - ((n : ℚ) - 1) * fq))

theorem spider_sound (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ) (n : ℕ)
    (h : spiderOK ph sp sm n = true) :
    bsizeList ((sp.getD n []).map atomB) + 1 = n ∧
      (phiOf ph n : ℝ) / 2 ^ PB ≤ phiF (fq : ℝ) ((sp.getD n []).map atomB) := by
  unfold spiderOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hsz⟩, hlog⟩, hle⟩ := h
  have hsz' : bsizeList ((sp.getD n []).map atomB) + 1 = n := by rw [bsizeList_atoms]; exact hsz
  refine ⟨hsz', ?_⟩
  have hLB := logLB_le_log _ _ hlog
  have hle' := (Rat.cast_le (K := ℝ)).mpr hle
  push_cast at hle'
  have hn : ((bsizeList ((sp.getD n []).map atomB) : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : ((bsizeList ((sp.getD n []).map atomB) + 1 : ℕ) : ℝ) = (n : ℝ) := by rw [hsz']
    push_cast at this; linarith
  unfold phiF
  rw [piRoot_atoms, hn]
  have hP : (0 : ℝ) < 2 ^ PB := by positivity
  rw [div_le_iff₀ hP]
  nlinarith [mul_le_mul_of_nonneg_left hLB hP.le]

end EnvCert
end R3Cert
