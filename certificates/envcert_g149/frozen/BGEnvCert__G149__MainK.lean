/-
  R3Cert.BGEnvCert.G149.MainK -- the envelope certificate for 7 <= n <= 149, root degree <= 23.
  Assembled from the 11 cap fragments, the sliced shared checks (SharedAll) and the coverage check.
  No sorry; standard axioms only.
-/
import R3Cert.BGEnvCert.G149.Frag1
import R3Cert.BGEnvCert.G149.Frag2
import R3Cert.BGEnvCert.G149.Frag3
import R3Cert.BGEnvCert.G149.Frag4
import R3Cert.BGEnvCert.G149.Frag5
import R3Cert.BGEnvCert.G149.Frag6
import R3Cert.BGEnvCert.G149.Frag7
import R3Cert.BGEnvCert.G149.Frag8
import R3Cert.BGEnvCert.G149.Frag12
import R3Cert.BGEnvCert.G149.Frag16
import R3Cert.BGEnvCert.G149.Frag22
import R3Cert.BGEnvCert.G149.SharedAll
import R3Cert.BGEnvCert.AssembleK

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert R3Cert.BGSCL

def caps : List CapData := [cap1, cap2, cap3, cap4, cap5, cap6, cap7, cap8, cap12, cap16, cap22]

theorem caps_ok : ∀ d ∈ caps, capCheck tanTab ldTab phiTab d = true ∧ d.C + 1 ≤ DMAX := by
  intro d hd
  simp only [caps, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨cap1_ok, by decide⟩
  · exact ⟨cap2_ok, by decide⟩
  · exact ⟨cap3_ok, by decide⟩
  · exact ⟨cap4_ok, by decide⟩
  · exact ⟨cap5_ok, by decide⟩
  · exact ⟨cap6_ok, by decide⟩
  · exact ⟨cap7_ok, by decide⟩
  · exact ⟨cap8_ok, by decide⟩
  · exact ⟨cap12_ok, by decide⟩
  · exact ⟨cap16_ok, by decide⟩
  · exact ⟨cap22_ok, by decide⟩

set_option maxRecDepth 100000 in
theorem cover_ok : coverOKK caps 7 149 23 = true := by decide +kernel

/-- **Root degree ≤ 23, 7 ≤ n ≤ 149.**  A maximum-degree root list with a non-atom child is strictly
    beaten by the certified spider of the same size. -/
theorem envcertK (cs : List BGSCL.Branch) (hk2 : 2 ≤ cs.length) (hkK : cs.length ≤ 23)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length)
    (hn1 : 7 ≤ bsizeList cs + 1) (hn2 : bsizeList cs + 1 ≤ 149) (hna : ∃ c ∈ cs, ¬ IsAtom c) :
    (∀ c ∈ (spTab.getD (bsizeList cs + 1) []).map atomB, IsAtom c) ∧
      bsizeList ((spTab.getD (bsizeList cs + 1) []).map atomB) = bsizeList cs ∧
      piRoot cs < piRoot ((spTab.getD (bsizeList cs + 1) []).map atomB) :=
  envcert_generic_K tanTab ldTab phiTab spTab spM DMAX caps 7 149 23 tan_ok ld_ok caps_ok cover_ok
    spiders_ok cs hk2 hkK hcap hn1 hn2 hna

end R3Cert.EnvCert.G149
