/-
  BG spider reduction: the MID range, assembled (2026-09-25).

  * `spider_dominates_lowDegree_mid`: a root of maximum degree `2 ≤ k ≤ 23` with a non-atom child and
    `149 ≤ n − 1 ≤ 490` is strictly beaten by a spider of the same size (cherries + arm_5 + arm_4 for
    `n ≤ 274`, the arm_5/arm_4 spider above).
  * `spider_dominates_of_maxDegreeRoot_150`: combined with the old low-degree theorem (`n − 1 ≥ 491`) and
    the high-degree theorem (`k ≥ 24`, `n − 1 ≥ 90`), every max-degree rooting with `n − 1 ≥ 149` and a
    non-atom child is strictly beaten by a spider of the same size.
  No `sorry`, no `native_decide` (`decide +kernel` only); standard axioms.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSpiderMidRootK2
import R3Cert.BGSpiderMidRootK3
import R3Cert.BGSpiderMidRootK4
import R3Cert.BGSpiderMidRootK5
import R3Cert.BGSpiderMidRootK6
import R3Cert.BGSpiderMidRootK7
import R3Cert.BGSpiderMidRootK8
import R3Cert.BGSpiderMidRootK9
import R3Cert.BGSpiderMidRootK10
import R3Cert.BGSpiderMidRootK11
import R3Cert.BGSpiderMidRootK12
import R3Cert.BGSpiderMidRootK13
import R3Cert.BGSpiderMidRootK14
import R3Cert.BGSpiderMidRootK15
import R3Cert.BGSpiderMidRootK16
import R3Cert.BGSpiderMidRootK17
import R3Cert.BGSpiderMidRootK18
import R3Cert.BGSpiderMidRootK19
import R3Cert.BGSpiderMidRootK20
import R3Cert.BGSpiderMidRootK21
import R3Cert.BGSpiderMidRootK22
import R3Cert.BGSpiderMidRootK23

namespace R3Cert
namespace BGSCL

theorem spider_dominates_lowDegree_mid (cs : List Branch) (hk2 : 2 ≤ cs.length) (hk : cs.length ≤ 23)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (h1 : 149 ≤ bsizeList cs) (h2 : bsizeList cs ≤ 490) :
    ∃ sp : List Branch, bsizeList sp = bsizeList cs ∧ piRoot cs < piRoot sp := by
  have hphi : phiRoot cs < ((lowTabGet (bsizeList cs) : ℤ) : ℝ) / 10 ^ 12 := by
    obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
    rw [hK] at hk2 hk hcap
    interval_cases K
    · exact midroot_2 cs hK hcap hna h1 h2
    · exact midroot_3 cs hK hcap hna h1 h2
    · exact midroot_4 cs hK hcap hna h1 h2
    · exact midroot_5 cs hK hcap hna h1 h2
    · exact midroot_6 cs hK hcap hna h1 h2
    · exact midroot_7 cs hK hcap hna h1 h2
    · exact midroot_8 cs hK hcap hna h1 h2
    · exact midroot_9 cs hK hcap hna h1 h2
    · exact midroot_10 cs hK hcap hna h1 h2
    · exact midroot_11 cs hK hcap hna h1 h2
    · exact midroot_12 cs hK hcap hna h1 h2
    · exact midroot_13 cs hK hcap hna h1 h2
    · exact midroot_14 cs hK hcap hna h1 h2
    · exact midroot_15 cs hK hcap hna h1 h2
    · exact midroot_16 cs hK hcap hna h1 h2
    · exact midroot_17 cs hK hcap hna h1 h2
    · exact midroot_18 cs hK hcap hna h1 h2
    · exact midroot_19 cs hK hcap hna h1 h2
    · exact midroot_20 cs hK hcap hna h1 h2
    · exact midroot_21 cs hK hcap hna h1 h2
    · exact midroot_22 cs hK hcap hna h1 h2
    · exact midroot_23 cs hK hcap hna h1 h2
  obtain ⟨sp, hsz, hlow⟩ := spider_low (bsizeList cs) h1 h2
  refine ⟨sp, hsz, ?_⟩
  have hlt : phiRoot cs < phiRoot sp := lt_of_lt_of_le hphi hlow
  unfold phiRoot at hlt
  rw [hsz] at hlt
  exact (Real.log_lt_log_iff (piRoot_pos _) (piRoot_pos _)).mp (by linarith)

/-- **Spider domination for every max-degree rooting with `n ≥ 150` and a non-atom child.** -/
theorem spider_dominates_of_maxDegreeRoot_150 (cs : List Branch) (hk2 : 2 ≤ cs.length)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length) (hN : 149 ≤ bsizeList cs)
    (hna : ∃ c ∈ cs, ¬ IsAtom c) :
    ∃ sp : List Branch, bsizeList sp = bsizeList cs ∧ piRoot cs < piRoot sp := by
  rcases le_or_gt cs.length 23 with hk | hk
  · rcases le_or_gt (bsizeList cs) 490 with hN2 | hN2
    · exact spider_dominates_lowDegree_mid cs hk2 hk hcap hna hN hN2
    · obtain ⟨a, q, _, hs, hlt⟩ := spider_dominates_lowDegree_uncond cs hk2 hk hcap (by omega)
      exact ⟨spiderB a q, hs, hlt⟩
  · obtain ⟨a, q, _, hs, hlt⟩ := spider_dominates_highDegree_uncond cs (by omega) hna (by omega)
    exact ⟨spiderB a q, hs, hlt⟩

end BGSCL
end R3Cert
