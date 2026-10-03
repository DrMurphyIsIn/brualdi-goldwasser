"""Regenerate the one-line kernel sweep modules and their aggregators (run from formalization/BGUnique):
Sweep/S_n.lean (150 <= n <= 491), SweepAll.lean, SmallSweep/C_k.lean (k = 0..10) and SmallSweep/All.lean."""
import os
H = "namespace R3Cert\nnamespace SpiderStrict\n\n"
T = "\nend SpiderStrict\nend R3Cert\n"
os.makedirs("Sweep", exist_ok=True); os.makedirs("SmallSweep", exist_ok=True)
for n in range(150, 492):
    open(f"Sweep/S_{n}.lean", "w").write(
        "import BGUnique.StrictTable\n\n" + H + f"theorem schunk_{n} : checkNS {n} = true := by decide +kernel\n" + T)
body = "".join(f"import BGUnique.Sweep.S_{n}\n" for n in range(150, 492)) + "\n" + H
body += "theorem checkNS_mid (n : ℕ) (h1 : 150 ≤ n) (h2 : n ≤ 491) : checkNS n = true := by\n  interval_cases n\n"
body += "".join(f"  · exact schunk_{n}\n" for n in range(150, 492)) + T
open("SweepAll.lean", "w").write(body)
for k in range(11):
    open(f"SmallSweep/C_{k}.lean", "w").write(
        "import BGUnique.SmallSweep.Base\n\n" + H + f"theorem chunk_{k} : chunkOK {7 + 13 * k} 13 = true := by decide +kernel\n" + T)
body = "".join(f"import BGUnique.SmallSweep.C_{k}\n" for k in range(11)) + "\n" + H
body += "/-- The plain strict check holds for every `7 ≤ n ≤ 149` outside `failSmall`. -/\n"
body += "theorem checkNS_small (n : ℕ) (h7 : 7 ≤ n) (h149 : n ≤ 149) (hn : n ∉ failSmall) : checkNS n = true := by\n"
for k in range(11):
    body += f"  by_cases hc{k} : n < {20 + 13 * k}\n  · exact checkNS_of_chunk chunk_{k} n (by omega) (by omega) hn\n"
body += "  omega\n" + T
open("SmallSweep/All.lean", "w").write(body)
