"""Build LeanCherry/WinExt2Core.lean and LeanCherry/WinExt2Assemble.lean from the frozen WinExtCore / WinExtAssemble
by textual transformation (the frozen files are not modified).

Run from this directory: python3 make_ext2.py (it overwrites ../LeanCherry/WinExt2Core.lean and
../LeanCherry/WinExt2Assemble.lean)."""
import re
L = '../LeanCherry/'
core = open(L + 'WinExtCore.lean').read()
asm = open(L + 'WinExtAssemble.lean').read()

def rep(s, a, b, count=1):
    assert s.count(a) >= 1, a
    if count == 0:
        return s.replace(a, b)
    assert s.count(a) == count, (a, s.count(a))
    return s.replace(a, b)

# ---------------- core ----------------
body = core[core.index('/-- the facts about the window constants'):]
c = body
c = rep(c, 'structure WFacts (l : ℝ) : Prop where', 'structure WFacts2 (l : ℝ) : Prop where')
c = rep(c, '  l_le_8kap : l ≤ 8 * kapW l\n', '  ydag_ge6 : 1 / 6 ≤ ydag l\n  slope5 : ∀ m : ℝ, 5 ≤ m → l / (m + 1 + l * m * yC l) ≤ kapW l\n')
c = rep(c, '  c2 : ∀ m : ℝ, 1 ≤ m → m ≤ 7 →', '  c2 : ∀ m : ℝ, 1 ≤ m → m ≤ 4 →')
c = rep(c, 'namespace WFacts\n', 'namespace WFacts2\n')
c = rep(c, 'end WFacts\n', 'end WFacts2\n')
c = rep(c, '(H : WFacts l)', '(H : WFacts2 l)')
# step_m8 -> step_m5
i0 = c.index('lemma step_m8'); i1 = c.index('/-! ### k = 0, 1 <= m <= 7 -/')
m8 = c[i0:i1]
m5 = m8
m5 = rep(m5, 'lemma step_m8 (m : ℕ) (hm : 8 ≤ m)', 'lemma step_m5 (m : ℕ) (hm : 5 ≤ m)')
m5 = rep(m5, 'have hmR : (8:ℝ) ≤ m := by exact_mod_cast hm', 'have hmR : (5:ℝ) ≤ m := by exact_mod_cast hm')
m5 = rep(m5, '''    have h9 : 9 ≤ m + 1 + l * (m * y) := by
      have : 0 ≤ l * (m * y) := mul_nonneg hl.le (mul_nonneg hm0 hy0)
      linarith
    have : 1 / (m + 1 + l * (m * y)) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) h9
    linarith [H.ydag_ge]''', '''    have h9 : 6 ≤ m + 1 + l * (m * y) := by
      have : 0 ≤ l * (m * y) := mul_nonneg hl.le (mul_nonneg hm0 hy0)
      linarith
    have : 1 / (m + 1 + l * (m * y)) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) h9
    linarith [H.ydag_ge6]''')
m5 = rep(m5, '''    have hq : c / (1 + c * yC l) ≤ m * kapW l := by
      have h1' : c / (1 + c * yC l) ≤ c := div_le_self hc0.le (by linarith)
      have h2' : 8 * kapW l ≤ m * kapW l := mul_le_mul_of_nonneg_right hmR H.kap_pos.le
      linarith [H.l_le_8kap]''', '''    have hq : c / (1 + c * yC l) ≤ m * kapW l := by
      have e : c / (1 + c * yC l) = m * (l / (m + 1 + l * m * yC l)) := by
        rw [hc]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (H.slope5 m hmR) hm0''')
c = c[:i0] + m5 + c[i1:]
c = rep(c, '/-! ### k = 0, m >= 8 (as in WinBell, with l <= 8 kap taken from the facts) -/',
        '/-! ### k = 0, m >= 5 (the m >= 8 argument of WinBell, with ydag >= 1/6 and the slope bound) -/')
c = rep(c, '/-! ### k = 0, 1 <= m <= 7 -/', '/-! ### k = 0, 1 <= m <= 4 -/')
c = rep(c, 'lemma step_c2 (m : ℕ) (hm : 1 ≤ m) (hm7 : m ≤ 7)', 'lemma step_c2 (m : ℕ) (hm : 1 ≤ m) (hm7 : m ≤ 4)')
c = rep(c, 'have hm7R : (m:ℝ) ≤ 7 := by exact_mod_cast hm7', 'have hm7R : (m:ℝ) ≤ 4 := by exact_mod_cast hm7')
c = rep(c, 'rcases (by omega : m ≤ 7 ∨ 8 ≤ m) with h7 | h8', 'rcases (by omega : m ≤ 4 ∨ 5 ≤ m) with h7 | h8')
c = rep(c, 'have := H.step_m8 m h8 ybar ht0 ht1', 'have := H.step_m5 m h8 ybar ht0 ht1')
hdr = '''/-
LeanCherry.WinExt2Core -- the window extended to [2, 2.35], part 1: the window witness argument with a sharper k = 0 split.

`WFacts2 l` is `WFacts l` (LeanCherry.WinExtCore) with the reduced (C2) condition required only for m <= 4, and
the k = 0, m >= 5 types handled by the m >= 8 argument of LeanCherry.WinBell: for m >= 5 the child value
1/(m+1+l m y) is at most 1/6 <= ydag (so h vanishes there), and the slope bound l/(m+1+l m y_ch) <= kap
replaces l <= 8 kap; the value at y_ch is the arm deficit (exact, all m >= 1).  This removes the m = 5..7
instances of the reduced condition log((m+1+l m y_ch)/(m+1)) <= f* - eps, which fail below 2.35.
-/
import LeanCherry.WinExtCore

open Real

namespace LeanCherry

noncomputable section

open Classical Br

'''
open(L + 'WinExt2Core.lean', 'w').write(hdr + c)

# ---------------- assemble ----------------
okstart = asm.index('/-- the inequalities a box must satisfy -/'); okend = asm.index('/-- the derived enclosures at a point l of the box -/')
okdef = asm[okstart:okend]
okdef = rep(okdef, 'structure BoxOK (p : BoxP) : Prop where', 'structure BoxOK2 (p : BoxP) : Prop where')
okdef = rep(okdef, '  hC0 : (8 + 7 * (p.b / (2 + p.b))) / (8 * p.sl) - 1 + p.εh / 2 ≤ 0\n',
            '  hC04 : (5 + 4 * (p.b / (2 + p.b))) / (5 * p.sl) - 1 + p.εh / 2 ≤ 0\n  hydl6 : 1 / 6 ≤ p.ydl\n')
okdef = rep(okdef, '/-- the inequalities a box must satisfy -/', '/-- the inequalities a box must satisfy (BoxOK with the m = 7 condition hC0 replaced by m = 4, plus ydag >= 1/6) -/')
rest = asm[asm.index('namespace BoxOK\n'):]
r = rest
r = rep(r, 'namespace BoxOK\n', 'namespace BoxOK2\n')
r = rep(r, 'end BoxOK\n', 'end BoxOK2\n')
r = rep(r, 'variable {p : BoxP} (H : BoxOK p)', 'variable {p : BoxP} (H : BoxOK2 p)')
r = r.replace('(H : BoxOK p)', '(H : BoxOK2 p)').replace('(_H : BoxOK p)', '(_H : BoxOK2 p)')
names = ['hk0', 'hw0', 'C0m', 'eps_le_h', 'Cm', 'slopem', 'm1', 'c4']
for n in names:
    r = re.sub(r'\blemma ' + n + r' ', 'lemma ' + n + '2 ', r)
    r = re.sub(r'E\.' + n + r'\b', 'E.' + n + '2', r)
r = r.replace('(hm7 : m ≤ 7)', '(hm7 : m ≤ 4)')
r = r.replace('Box.ratio_mono7', 'ratio_mono4').replace('H.hC0', 'H.hC04')
r = rep(r, '/-- C0 for real m in [1, 7] -/', '/-- C0 for real m in [1, 4] -/')
r = rep(r, '/-- C_m for real m in [1, 7] -/', '/-- C_m for real m in [1, 4] -/')
r = rep(r, 'theorem BoxOK.wfacts {p : BoxP} (H : BoxOK2 p) {l : ℝ} (hl1 : p.a ≤ l) (hl2 : l ≤ p.b) : WFacts l := by',
        'theorem BoxOK2.wfacts2 {p : BoxP} (H : BoxOK2 p) {l : ℝ} (hl1 : p.a ≤ l) (hl2 : l ≤ p.b) : WFacts2 l := by')
r = rep(r, '      l_le_8kap := le_trans hl2 (le_trans H.h8 (by have := E.hkl; linarith))\n',
        '      ydag_ge6 := le_trans H.hydl6 E.hydlo\n      slope5 := fun m hm => E.slopem2 H hl2 m (by linarith)\n')
r = rep(r, '/-- `WFacts l` for every l in a box satisfying `BoxOK` -/', '/-- `WFacts2 l` for every l in a box satisfying `BoxOK2` -/')
r = rep(r, 'lemma hlyc : l * yC l = tC l := ltC E.hl.le\n', '')
r = rep(r, 'lemma hyc0 : 0 < yC l := by unfold yC; have := E.hl; positivity\n', '')
mono = '''lemma ratio_mono4 {b sl m : ℝ} (hb : 0 < b) (hsl0 : 0 < sl) (hm : 1 ≤ m) (hm4 : m ≤ 4) :
    (m + 1 + m * (b / (2 + b))) / ((m + 1) * sl) ≤ (5 + 4 * (b / (2 + b))) / (5 * sl) := by
  have hb0 : 0 ≤ b / (2 + b) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 4 - m)) hsl0.le]

'''
hdr2 = '''/-
LeanCherry.WinExt2Assemble -- the window extended to [2, 2.35], part 2: `WFacts2 l` on a box from a bundled set of numeral inequalities.

`BoxOK2 p` is `BoxOK p` (LeanCherry.WinExtAssemble) with the m = 7 reduced condition hC0 replaced by its m = 4
instance hC04, plus 1/6 <= ydl.  The box lemmas are those of WinExtAssemble, restated for `BoxOK2` and m <= 4.
-/
import LeanCherry.WinExt2Core
import LeanCherry.WinExtAssemble

open Real

namespace LeanCherry

noncomputable section

'''
open(L + 'WinExt2Assemble.lean', 'w').write(hdr2 + mono + okdef + r)
print('ok')
