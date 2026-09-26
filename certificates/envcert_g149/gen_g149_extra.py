"""Sliced shared checks and the degree-limited assembly for the G149 envelope certificate.

The generator's monolithic FragShared (tangent / log / spider checks in one `decide`) exhausts the
kernel's per-declaration cache, so the checks are split into small independent theorems
(SharedTan0..19, SharedLd, SharedSp0..10), chained back by `tanOK_split` / `spidersOK_split`
(SharedAll).  MainK assembles the 11 cap fragments with coverage for root degree <= 23
(`envcert_generic_K`).  Usage: gen_g149_extra.py <dir of R3Cert/BGEnvCert/G149>
"""
import os, sys

d = sys.argv[1]
hdr = "import R3Cert.BGEnvCert.G149.Common\nimport R3Cert.BGEnvCert.Force\n\nnamespace R3Cert.EnvCert.G149\nopen R3Cert.EnvCert\n\n"
ftr = "\nend R3Cert.EnvCert.G149\n"
for i in range(20):
    a, b = 5 * i, 5 * i + 5
    open(os.path.join(d, f"SharedTan{i}.lean"), "w").write(hdr + f"set_option maxRecDepth 100000 in\ntheorem tan_ok_{i} : tanOK tanTab {a} {b} = true := by decide +kernel\n" + ftr)
open(os.path.join(d, "SharedLd.lean"), "w").write(hdr + "set_option maxRecDepth 100000 in\ntheorem ld_ok : ldOK ldTab DMAX = true := by decide +kernel\n" + ftr)
sp = [(7, 20)] + [(a, a + 12) for a in range(21, 150, 13)]
sp = [(a, min(b, 149)) for a, b in sp]
for j, (a, b) in enumerate(sp):
    open(os.path.join(d, f"SharedSp{j}.lean"), "w").write(hdr + f"set_option maxRecDepth 100000 in\ntheorem sp_ok_{j} : spidersOK phiTab spTab spM {a} {b} = true := by decide +kernel\n" + ftr)
imports = "\n".join([f"import R3Cert.BGEnvCert.G149.SharedTan{i}" for i in range(20)] + ["import R3Cert.BGEnvCert.G149.SharedLd"] + [f"import R3Cert.BGEnvCert.G149.SharedSp{j}" for j in range(len(sp))])
tan_chain = "  have h0 := tan_ok_0\n" + "".join(f"  have h{i} := tanOK_split tanTab 0 {5*i} {5*i+5} (by omega) (by omega) h{i-1} tan_ok_{i}\n" for i in range(1, 20)) + "  exact h19\n"
sp_chain = "  have g0 := sp_ok_0\n" + "".join(f"  have g{j} := spidersOK_split phiTab spTab spM 7 {sp[j-1][1]} {sp[j][1]} (by omega) (by omega) g{j-1} sp_ok_{j}\n" for j in range(1, len(sp))) + f"  exact g{len(sp)-1}\n"
open(os.path.join(d, "SharedAll.lean"), "w").write(imports + "\n\nnamespace R3Cert.EnvCert.G149\nopen R3Cert.EnvCert\n\ntheorem tan_ok : tanOK tanTab 0 HG = true := by\n" + tan_chain + "\ntheorem spiders_ok : spidersOK phiTab spTab spM 7 149 = true := by\n" + sp_chain + ftr)

caps = ["1", "2", "3", "4", "5", "6", "7", "8", "12", "16", "22"]
imp = "\n".join([f"import R3Cert.BGEnvCert.G149.Frag{c}" for c in caps] + ["import R3Cert.BGEnvCert.G149.SharedAll", "import R3Cert.BGEnvCert.AssembleK"])
lst = ", ".join(f"cap{c}" for c in caps)
pats = " | ".join(["rfl"] * len(caps))
cases = "\n".join(f"  · exact ⟨cap{c}_ok, by decide⟩" for c in caps)
open(os.path.join(d, "MainK.lean"), "w").write(f'''/-
  R3Cert.BGEnvCert.G149.MainK -- the envelope certificate for 7 <= n <= 149, root degree <= 23.
  Assembled from the 11 cap fragments, the sliced shared checks (SharedAll) and the coverage check.
  No sorry; standard axioms only.
-/
{imp}

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert R3Cert.BGSCL

def caps : List CapData := [{lst}]

theorem caps_ok : ∀ d ∈ caps, capCheck tanTab ldTab phiTab d = true ∧ d.C + 1 ≤ DMAX := by
  intro d hd
  simp only [caps, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with {pats}
{cases}

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
''')
