"""Generate and EXACTLY re-check the Lean certificates for the mid range 150 <= n <= 491
(R3Cert/BGSpiderMid*.lean).  Every rational used in Lean is recomputed here with fractions.Fraction and
every inequality the Lean files assert is re-checked exactly before emission.

Pieces:
  * credited rate cells for every cap D = 2..23 and every child count K = 1..D-1
    (`rate_cell_genericK` / `rate_cell_oneK`), with per-cap (alpha_D, kappa_D);
  * per root degree k = 2..23: integer-scaled knapsack types, constants and the kernel check
    `C + VN + dpRow[k-1][N-3] - alpha*N < LOW(N)` for N = n-1 in [149, 490];
  * the table LOW(N): exact spider lower bounds (cherries + arm_5 + arm_4, the exact optimum) for
    N <= 273 and the arm_5/arm_4 floor log(26/23) - 1/96 for N >= 274.
usage: python3 gen_mid_lean.py OUTDIR      (writes the Lean files into OUTDIR)
"""
import math, os, pickle, sys
from fractions import Fraction as Fr
from mpmath import mp, mpf, log as mlog, ceil as mceil, floor as mfloor

mp.dps = 50
HERE = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------------------------ Taylor log enclosures (as in Lean)
def P6(c):
    return 1 + c + c ** 2 / 2 + c ** 3 / 6 + c ** 4 / 24 + c ** 5 / 120


def err6(a):
    return a ** 6 * Fr(7, 4320)


def rat(x, up, den=10 ** 7):
    return Fr(int(mceil(x * den) if up else mfloor(x * den)), den)


def log_upper(xq):
    """c with log x <= c, certified by x <= P6(c) - err6(|c|), |c| <= 1."""
    t = mlog(mpf(xq.numerator) / xq.denominator)
    for k in range(300):
        c = rat(t + mpf('1e-7') * 1.5 ** k, True)
        if abs(c) <= 1 and xq <= P6(c) - err6(abs(c)):
            return c
    raise ValueError(xq)


def log_lower(xq):
    t = mlog(mpf(xq.numerator) / xq.denominator)
    for k in range(300):
        c = rat(t - mpf('1e-7') * 1.5 ** k, False)
        if abs(c) <= 1 and P6(c) + err6(abs(c)) <= xq:
            return c
    raise ValueError(xq)


def log_upper2(xq):
    t = mlog(mpf(xq.numerator) / xq.denominator)
    for k in range(300):
        c = rat(t + mpf('1e-7') * 1.5 ** k, True)
        h = c / 2
        if abs(h) <= 1 and P6(h) - err6(abs(h)) >= 0 and xq <= (P6(h) - err6(abs(h))) ** 2:
            return c
    raise ValueError(xq)


A_lo = Fr(847797, 110000000)
F_lo = (A_lo + Fr(2027323, 5000000)) / 2
A_hi = Fr(133, 17061)
bj = {5: Fr(0)}
for j in list(range(1, 5)) + list(range(6, 23)):
    T = Fr(3, 2) ** j * Fr(4 * j + 3, 3 * j + 3)
    R = T ** 11 / Fr(621, 64) ** (2 * j + 1)
    bj[j] = (log_upper(R) if j <= 4 else log_upper2(R)) / 11


def yj(j):
    return Fr(3, 4 * j + 3)


PARAMS = {2: (Fr(9799, 10 ** 6), (Fr(4, 1000), Fr(5, 1000), Fr(5, 1000), Fr(0))),
          3: (Fr(2436, 10 ** 6), (Fr(4, 1000), Fr(5, 1000), Fr(5, 1000), Fr(0))),
          4: (Fr(1584, 10 ** 6), (Fr(4, 1000), Fr(5, 1000), Fr(5, 1000), Fr(0))),
          5: (Fr(1332, 10 ** 6), (Fr(8, 1000), Fr(75, 10000), Fr(5, 1000), Fr(0))),
          6: (Fr(869, 10 ** 6), (Fr(4, 1000), Fr(75, 10000), Fr(5, 1000), Fr(0))),
          7: (Fr(690, 10 ** 6), (Fr(0), Fr(5, 1000), Fr(5, 1000), Fr(0))),
          8: (Fr(680, 10 ** 6), (Fr(0), Fr(25, 10000), Fr(5, 1000), Fr(0)))}
for k in range(9, 13):
    PARAMS[k] = (Fr(646, 10 ** 6), (Fr(0), Fr(25, 10000), Fr(5, 1000), Fr(0)))
for k, a in {13: 563, 14: 563, 15: 550, 16: 511, 17: 477, 18: 447, 19: 420, 20: 397, 21: 376, 22: 357,
             23: 355}.items():
    PARAMS[k] = (Fr(a, 10 ** 6), (Fr(0), Fr(5, 1000), Fr(5, 1000), Fr(2, 1000)))


def ym_(D):
    return Fr(1, 2 * D - 1)


def NbK(D, kap, s):
    ym = ym_(D)
    k1, k2, k3, k4 = kap
    return max(-A_lo - (Fr(2, 5) - Fr(1, 3)) / 4 - k1 + s * Fr(2, 5),
               -A_lo - (1 / (2 + ym) - Fr(1, 3)) / 4 - k1 + s / (2 + ym),
               -Fr(1, 5) / 32 - k2 + s / 5,
               -(1 / (3 + 2 * ym)) / 32 - k2 + s / (3 + 2 * ym),
               -Fr(1, 7) / 384 - k3 + s / 7,
               -(1 / (4 + 3 * ym)) / 384 - k3 + s / (4 + 3 * ym),
               -k4 + s * ym,
               -k4 + s / (5 + 4 * ym))


def Nb1K(D, kap, s):
    ym = ym_(D)
    k1, k2, k3, k4 = kap
    f = lambda y: 1 / (4 * (2 + y))
    return max(-A_lo - (Fr(2, 5) - Fr(1, 3)) / 4 - k1 + s * Fr(2, 5) + f(Fr(2, 5)),
               -A_lo - (1 / (2 + ym) - Fr(1, 3)) / 4 - k1 + s / (2 + ym) + f(1 / (2 + ym)),
               -Fr(1, 5) / 32 - k2 + s / 5 + f(Fr(1, 5)),
               -(1 / (3 + 2 * ym)) / 32 - k2 + s / (3 + 2 * ym) + f(1 / (3 + 2 * ym)),
               -Fr(1, 7) / 384 - k3 + s / 7 + f(Fr(1, 7)),
               -(1 / (4 + 3 * ym)) / 384 - k3 + s / (4 + 3 * ym) + f(1 / (4 + 3 * ym)),
               -k4 + s * ym + f(ym),
               -k4 + s / (5 + 4 * ym) + f(1 / (5 + 4 * ym)))


def cell(D, K, al, kap, S0):
    d = K + 1
    s = 1 / (d + S0)
    c = log_upper((1 + S0 / d) ** 11 * Fr(64, 621))
    ell = c / 11
    if K == 1:
        u = max([Nb1K(D, kap, s)] + [s * yj(j) + 1 / (4 * (2 + yj(j))) + bj[j] + al * (2 * j + 1)
                                     for j in range(1, D)])
        return u + ell - s * S0 + A_hi - Fr(1, 12) + al + kap[0], dict(S0=S0, c=c, u=u)
    ym = ym_(D)
    rhom = {2: (1 / (3 + 2 * ym)) / 32, 3: (1 / (4 + 3 * ym)) / 384}.get(K, Fr(0))
    u = max([-F_lo + al + s, NbK(D, kap, s)] + [bj[j] + al * (2 * j + 1) + s * yj(j) for j in range(1, D)])
    um = max(-A_lo + 2 * al + s / 3, u)
    km = kap[min(K, 4) - 1]
    return (K - 1) * um + u + ell - s * S0 + al + rhom + km, dict(S0=S0, c=c, u=u, um=um, rhom=rhom, km=km)


def best_cell(D, K):
    al, kap = PARAMS[D]
    best = None
    for i in range(0, 300):
        S0 = Fr(i, 100) * Fr(K, 3) if K > 1 else Fr(i, 300)
        if K > 1 and S0 > K:
            break
        try:
            v, dat = cell(D, K, al, kap, S0)
        except ValueError:
            continue
        if best is None or v < best[0]:
            best = (v, dat)
    assert best[0] <= 0, (D, K, float(best[0]))
    return best


# ------------------------------------------------------------------ spider lower bounds and root checks
SC = 10 ** 12


def ceil_(x):
    return -((-x.numerator) // x.denominator)


def floor_(x):
    return x.numerator // x.denominator


L_lo = Fr(613011, 5000000)
B4LO = Fr(-22581, 22000000) - Fr(1, 10 ** 7)          # Lean `bell_arm4_ge_tight`


def spider_table():
    # exact spider-family optima for n <= 520, recomputed (no cached data file)
    sys.path.insert(0, HERE)
    import bg_spider_reduction as B
    sp = B.spider_max(520)
    low, spi = {}, {}
    for N in range(149, 491):
        n = N + 1
        if N >= 274:
            low[N] = floor_(SC * (L_lo - Fr(1, 96)))
            continue
        reps = sp[n][1][0]
        c, a, q = reps.count("C"), reps.count("A5"), reps.count("A4")
        assert c + a + q == len(reps) and 2 * c + 11 * a + 9 * q == N
        x = 1 + (Fr(c, 3) + Fr(3, 23) * a + Fr(3, 19) * q) / (c + a + q)
        lx = log_lower(x)
        val = c * (-A_hi) + q * B4LO + lx
        low[N] = floor_(SC * val)
        spi[N] = (c, a, q, x, lx)
    return low, spi


NEGI = -(10 ** 40)


def dprow(tys, L, c):
    r = [0] * L
    for _ in range(c):
        acc = [NEGI] * L
        for s, w in tys:
            for i in range(s, L):
                v = r[i - s] + w
                if v > acc[i]:
                    acc[i] = v
        r = acc
    return r


def root_cert(k, low, tchoice=None):
    al, kap = PARAMS[k]
    cands = [tchoice] if tchoice else [Fr(t, 1000) for t in range(1100, 1400, 5)]
    best = None
    for t in cands:
        s = 1 / (k * t)
        lt = log_upper(t)
        CI = ceil_(SC * (lt + 1 / t - 1))
        VN = NbK(k, kap, s)
        VNI = ceil_(SC * VN)
        WL = ceil_(SC * (-F_lo + s + al))
        WC = ceil_(SC * (-A_lo + s / 3 + 2 * al))
        WA = {j: ceil_(SC * (bj[j] + s * yj(j) + al * (2 * j + 1))) for j in range(1, k)}
        alI = floor_(SC * al)
        tys = [(3, VNI), (1, WL), (2, WC)] + [(2 * j + 1, WA[j]) for j in range(1, k)]
        row = dprow(tys, 491, k - 1)
        margin = min(low[N] - (CI + VNI + row[N - 3] - alI * N) for N in range(149, 491))
        if best is None or margin > best[0]:
            best = (margin, dict(t=t, lt=lt, CI=CI, VNI=VNI, WL=WL, WC=WC, WA=WA, alI=alI, tys=tys))
    assert best[0] > 0, (k, best[0])
    return best


# ------------------------------------------------------------------ Lean emission
def q(x):
    x = Fr(x)
    return f"({x.numerator}/{x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"


def lean_cells(D):
    al, kap = PARAMS[D]
    k1, k2, k3, k4 = kap
    kargs = f"(α := {q(al)}) (k1 := {q(k1)}) (k2 := {q(k2)}) (k3 := {q(k3)}) (k4 := {q(k4)})"
    out = [f"""/- Generated by proof/verification/finite_cert/gen_mid_lean.py: credited rate cells, cap D = {D}. -/
import R3Cert.BGSpiderMid

namespace R3Cert
namespace BGSCL
"""]
    for K in range(1, D):
        v, dat = best_cell(D, K)
        S0, c = dat['S0'], dat['c']
        d = K + 1
        qv = 1 + S0 / d
        dd = f"((({K}:ℕ):ℝ)) + 1" if K > 1 else "(1:ℝ) + 1"
        hl = f"""(by
      have e : (1 + {q(S0)} / ({dd})) = {q(qv)} := by norm_num
      rw [e, log_sub_fstar_eq (by norm_num)]
      have h := log_le_of_taylor (x := {q(qv)} ^ 11 * (64 / 621)) (c := {q(c)}) (a := {q(abs(c))})
        (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
      linarith)"""
        arm = f"""(by intro j h1 h2; have h3 : j ≤ {D - 1} := (by omega); interval_cases j <;> norm_num [bjT])"""
        if K == 1:
            out.append(f"""theorem mcell_{D}_{K} (cs : List Branch) (hlen : cs.length = 1) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ {D})
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + {q(al)}
      + kapF {q(k1)} {q(k2)} {q(k3)} {q(k4)} (Branch.node cs)
      + (cs.map (rateGK {q(al)} {q(k1)} {q(k2)} {q(k3)} {q(k4)})).sum ≤ 0 :=
  rate_cell_oneK (D := {D}) (by norm_num) (by norm_num) {kargs} (S0 := {q(S0)}) (ℓ := {q(c / 11)})
    (u := {q(dat['u'])}) (by norm_num)
    {hl}
    {arm}
    (by unfold Nb1K; simp only [max_le_iff]; norm_num)
    (by norm_num) cs hlen hcap hna
""")
        else:
            if K == 2:
                hrho = f"(fun cs' h hc => le_trans (rho_len2_le (D := {D}) (by norm_num) cs' h hc) (by norm_num))"
            elif K == 3:
                hrho = f"(fun cs' h hc => le_trans (rho_len3_le (D := {D}) (by norm_num) cs' h hc) (by norm_num))"
            else:
                hrho = "(fun cs' h _ => by rw [ρwit_node_of_four_le cs' (by omega)])"
            out.append(f"""theorem mcell_{D}_{K} (cs : List Branch) (hlen : cs.length = {K}) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ {D})
    (hna : ¬ IsAtom (Branch.node cs)) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + {q(al)}
      + kapF {q(k1)} {q(k2)} {q(k3)} {q(k4)} (Branch.node cs)
      + (cs.map (rateGK {q(al)} {q(k1)} {q(k2)} {q(k3)} {q(k4)})).sum ≤ 0 :=
  rate_cell_genericK (D := {D}) (K := {K}) (by norm_num) (by norm_num) {kargs} (S0 := {q(S0)})
    (ℓ := {q(c / 11)}) (umax := {q(dat['um'])}) (unc := {q(dat['u'])}) (ρm := {q(dat['rhom'])})
    (km := {q(dat['km'])}) (by norm_num)
    {hl}
    (by norm_num)
    {arm}
    (by unfold NbK; simp only [max_le_iff]; norm_num)
    (by norm_num) (by norm_num)
    {hrho}
    (fun cs' h => by rw [kapF_node_len, h]; norm_num)
    (by norm_num) cs hlen hcap hna
""")
    cases = "\n".join(f"  · exact mcell_{D}_{K} cs hK hcap hna" for K in range(1, D))
    out.append(f"""theorem rateCellKap_{D} : RateCellKap {D} {q(al)} {q(k1)} {q(k2)} {q(k3)} {q(k4)} := by
  intro cs hlen hcap hna
  obtain ⟨K, hK⟩ : ∃ K, cs.length = K := ⟨_, rfl⟩
  have hK0 : 1 ≤ K := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd (Or.inr ⟨0, rfl⟩) hna
    · simp at hK; omega
  have hKD : K ≤ {D - 1} := by omega
  interval_cases K
{cases}

end BGSCL
end R3Cert
""")
    return "\n".join(out)


def lean_spiders(low, spi):
    lines = ["""/- Generated by proof/verification/finite_cert/gen_mid_lean.py: spider lower bounds, 149 <= N <= 490. -/
import R3Cert.BGSpiderMid

namespace R3Cert
namespace BGSCL

/-- Lower bounds (scaled by 10^12) on the best spider value `log pi - N F*` for `N = n - 1`. -/
def lowTabGet : ℕ → ℤ"""]
    for N in range(149, 491):
        lines.append(f"  | {N} => {low[N]}")
    lines.append("  | _ => 0\n")
    FLOORI = floor_(SC * (L_lo - Fr(1, 96)))
    lines.append(f"""theorem spider_floor_mid (N : ℕ) (hN : 274 ≤ N) (hN2 : N ≤ 490) (hlow : lowTabGet N = {FLOORI}) :
    ∃ sp : List Branch, bsizeList sp = N ∧ ((lowTabGet N : ℤ) : ℝ) / 10 ^ 12 ≤ phiRoot sp := by
  refine ⟨spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11), ?_, ?_⟩
  · rw [bsizeList_spiderB]; omega
  · have haq : 1 ≤ (N - 9 * ((5 * N) % 11)) / 11 + (5 * N) % 11 := by omega
    have hq10 : (((5 * N) % 11 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (by omega : (5 * N) % 11 ≤ 10)
    have hlo := phiRoot_spider_ge _ _ haq
    have h4 := bell_arm4_ge
    have h4' : (-1 / 96 : ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) * bell (armB 4) := by
      have hqnn : (0:ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hL := log_26_23_ge
    rw [hlow]
    norm_num
    linarith
""")
    for N in range(149, 274):
        c, a, qq, x, lx = spi[N]
        lines.append(f"""theorem spider_low_{N} :
    bsizeList (spiderC {c} {a} {qq}) = {N} ∧ ((lowTabGet {N} : ℤ) : ℝ) / 10 ^ 12 ≤ phiRoot (spiderC {c} {a} {qq}) := by
  refine ⟨by rw [bsizeList_spiderC], ?_⟩
  rw [phiRoot_spiderC, bell_cherry]
  have hA := cherry_anchor_le_tight
  have h4 := bell_arm4_ge_tight
  have e : (1 + ((({c}:ℕ):ℝ) * (1 / 3) + ((({a}:ℕ):ℝ)) * (3 / 23) + ((({qq}:ℕ):ℝ)) * (3 / 19))
      / (((({c}:ℕ):ℝ)) + ((({a}:ℕ):ℝ)) + ((({qq}:ℕ):ℝ)))) = {q(x)} := by norm_num
  rw [e]
  have hl := le_log_of_taylor (x := {q(x)}) (c := {q(lx)}) (a := {q(abs(lx))}) (by norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  have hv : lowTabGet {N} = {low[N]} := rfl
  rw [hv]
  push_cast
  nlinarith
""")
    disp = []
    for N in range(149, 491):
        if N < 274:
            c, a, qq, _, _ = spi[N]
            disp.append(f"  · exact ⟨spiderC {c} {a} {qq}, spider_low_{N}⟩")
        else:
            disp.append(f"  · exact spider_floor_mid {N} (by norm_num) (by norm_num) rfl")
    lines.append("""theorem spider_low (N : ℕ) (h1 : 149 ≤ N) (h2 : N ≤ 490) :
    ∃ sp : List Branch, bsizeList sp = N ∧ ((lowTabGet N : ℤ) : ℝ) / 10 ^ 12 ≤ phiRoot sp := by
  interval_cases N
""" + "\n".join(disp) + "\n\nend BGSCL\nend R3Cert\n")
    return "\n".join(lines)


def lean_root(k, cert):
    al, kap = PARAMS[k]
    k1, k2, k3, k4 = kap
    t, lt = cert['t'], cert['lt']
    WA = cert['WA']
    walines = "\n".join(f"  | {j} => {WA[j]}" for j in range(1, k))
    tys = ", ".join(f"({s}, {w})" for s, w in cert['tys'])
    return f"""/- Generated by proof/verification/finite_cert/gen_mid_lean.py: root certificate, root degree k = {k}. -/
import R3Cert.BGSpiderMidCellsD{k}
import R3Cert.BGSpiderMidSpiders

namespace R3Cert
namespace BGSCL

def WA_{k} : ℕ → ℤ
{walines}
  | _ => 0

def tys_{k} : List (ℕ × ℤ) := [{tys}]

theorem check_{k} : (List.range' 149 342).all (fun N => decide
    (({cert['CI']} : ℤ) + {cert['VNI']} + (dpRow tys_{k} 491 {k - 1}).getD (N - 3) NEGI - {cert['alI']} * (N : ℤ)
      < lowTabGet N)) = true := by decide +kernel

theorem midroot_{k} (cs : List Branch) (hlen : cs.length = {k}) (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ {k})
    (hna : ∃ c ∈ cs, ¬ IsAtom c) (h1 : 149 ≤ bsizeList cs) (h2 : bsizeList cs ≤ 490) :
    phiRoot cs < ((lowTabGet (bsizeList cs) : ℤ) : ℝ) / 10 ^ 12 := by
  have hσ : (1 / ((cs.length : ℝ) * {q(t)})) = 1 / ((({k}:ℕ):ℝ) * {q(t)}) := by rw [hlen]
  obtain ⟨ht, hn⟩ := htype_of (D := {k}) (by norm_num) (by norm_num) rateCellKap_{k}
    (SC := 10 ^ 12) (σ := 1 / ((({k}:ℕ):ℝ) * {q(t)})) (by norm_num) (by positivity)
    (tys := tys_{k}) (VNI := {cert['VNI']}) (WL := {cert['WL']}) (WC := {cert['WC']}) (WA := WA_{k})
    (by unfold NbK; simp only [max_le_iff]; norm_num) (by norm_num) (by norm_num)
    (by intro j h1 h2; have h3 : j ≤ {k - 1} := (by omega); interval_cases j <;> norm_num [bjT, WA_{k}])
    (by simp [tys_{k}]) (by simp [tys_{k}]) (by simp [tys_{k}])
    (by intro j h1 h2; have h3 : j ≤ {k - 1} := (by omega); interval_cases j <;> simp [tys_{k}, WA_{k}])
  have hb := phiRoot_le_dp (D := {k}) (tys := tys_{k}) (SC := 10 ^ 12) (α := {q(al)}) (t := {q(t)})
    (VNI := {cert['VNI']}) (by norm_num) (by norm_num) cs hcap (by rw [hσ]; exact ht) hna
    (by rw [hσ]; exact hn) 491 (by omega)
  rw [hlen] at hb
  have hlt := log_le_of_taylor (x := {q(t)}) (c := {q(lt)}) (a := {q(abs(lt))}) (by norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
  have hc := check_{k}
  rw [List.all_eq_true] at hc
  have hN := hc (bsizeList cs) (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  simp only [decide_eq_true_eq] at hN
  have hNR : ((({cert['CI']} : ℤ) + {cert['VNI']} + (dpRow tys_{k} 491 {k - 1}).getD (bsizeList cs - 3) NEGI
      - {cert['alI']} * (bsizeList cs : ℤ) : ℤ) : ℝ) < ((lowTabGet (bsizeList cs) : ℤ) : ℝ) := by exact_mod_cast hN
  push_cast at hNR
  have hNn : (0:ℝ) ≤ (bsizeList cs : ℝ) := Nat.cast_nonneg _
  have hCI : Real.log {q(t)} + 1 / {q(t)} - 1 ≤ ({cert['CI']} : ℝ) / 10 ^ 12 := by
    have : {q(lt)} + 1 / {q(t)} - 1 ≤ ({cert['CI']} : ℝ) / 10 ^ 12 := by norm_num
    linarith
  have hal : ({cert['alI']} : ℝ) / 10 ^ 12 ≤ {q(al)} := by norm_num
  have hmul : {q(al)} * (bsizeList cs : ℝ) ≥ ({cert['alI']} : ℝ) / 10 ^ 12 * (bsizeList cs : ℝ) :=
    mul_le_mul_of_nonneg_right hal hNn
  have hNR' : ((({cert['CI']} : ℝ) + {cert['VNI']} + (((dpRow tys_{k} 491 {k - 1}).getD (bsizeList cs - 3) NEGI : ℤ) : ℝ)
      - {cert['alI']} * (bsizeList cs : ℝ))) / 10 ^ 12 < ((lowTabGet (bsizeList cs) : ℤ) : ℝ) / 10 ^ 12 :=
    div_lt_div_of_pos_right (by linarith) (by norm_num)
  linarith

end BGSCL
end R3Cert
"""


if __name__ == "__main__":
    outdir = sys.argv[1]
    low, spi = spider_table()
    print("spider table: lowest LOW", min(low.values()) / SC)
    for D in range(2, 24):
        open(os.path.join(outdir, f"BGSpiderMidCellsD{D}.lean"), "w").write(lean_cells(D))
        print("cells D", D, "ok", flush=True)
    open(os.path.join(outdir, "BGSpiderMidSpiders.lean"), "w").write(lean_spiders(low, spi))
    TCH = {}
    if len(sys.argv) > 2:
        TCH = pickle.load(open(sys.argv[2], "rb"))
    for k in range(2, 24):
        m, cert = root_cert(k, low, TCH.get(k))
        print("root k", k, "t", cert['t'], "margin (1e-12 units)", m, flush=True)
        open(os.path.join(outdir, f"BGSpiderMidRootK{k}.lean"), "w").write(lean_root(k, cert))
