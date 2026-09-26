/-
  R3Cert.BGEnvCert.Check -- the Boolean certificate check and its soundness (2026-09-25).

  Fixed point: `P = 34` fractional bits; lanes of `W = 56` bits; a stored `W_s`/`Wn_s` lane `x`
  means `(x - OFF)/2^P`, a `c`-part knapsack lane means `(x - c·OFF)/2^P` (`OFF = 2^47`).  The grid
  is `μ_g = (g+1)/200`, `g < 100`; the rate is a rational `fq ≈ F*` (it cancels between a tree and
  a spider of the same size).

  Per child cap `C` the certificate supplies only the envelope tables `Wa`, `Wn` (one packed `ℕ`
  each), the Bellman witnesses `h` per `(c, g)`, and the root entries `(n, k, g, Troot, m)`.  The
  kernel computes every knapsack table itself (`lvl`, lane-wise max-plus over all row shifts) and
  checks every Bellman lane with a handful of bignum operations (`bchk`).  The tangent constants
  (`TanTab`), `log d` lower bounds (`LdTab`) and spider values (`PhiTab`) are checked separately
  (`tanOK`, `ldOK`), so each piece is an independent `decide +kernel` goal.

  `capSound`: a passing check bounds `log π(cs) - (n-1) fq < Φ(n)/2^P` for every root child list
  `cs` of the prescribed shape.  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Table
import R3Cert.BGEnvCert.LogBound
import R3Cert.BGEnvCert.Envelope

namespace R3Cert
namespace EnvCert

open R3Cert.BGSCL

/-! ### Parameters. -/

def WL : ℕ := 56
def PB : ℕ := 34
def OFF : ℕ := 2 ^ 47
def HG : ℕ := 100
def UDEN : ℕ := 2 ^ 30

/-- The price grid `μ_g = (g+1)/200`. -/
def muQ (g : ℕ) : ℚ := ((g : ℚ) + 1) / 200

/-- The rational rate (`≈ F* = log(621/64)/11`; any value works, it cancels). -/
def fq : ℚ := 28392988613 / 137438953472

/-- Lane `i` of a packed table. -/
def lane (v i : ℕ) : ℕ := v / 2 ^ (WL * i) % 2 ^ WL

theorem WL_pos : 2 ≤ WL := by decide

theorem half_WL : 2 ^ (WL - 1) = 256 * OFF := by decide

/-! ### Certificate data. -/

/-- Tangent entries per `g`: `(h, u·2^30, m, A, N)`. -/
abbrev TanTab := List (List (ℕ × ℕ × ℤ × ℤ × ℤ))
/-- `log d` lower bounds per `d`: `(m, Ld)`. -/
abbrev LdTab := List (ℤ × ℤ)
/-- Spider lower bounds `Φ(n)` (scaled by `2^P`) per `n`. -/
abbrev PhiTab := List ℤ

/-- Per-cap certificate data. -/
structure CapData where
  C : ℕ
  R : ℕ
  kmax : ℕ
  Wa : ℕ
  Wn : ℕ
  witA : List (List (List ℕ))
  witN : List (List (List ℕ))
  roots : List (ℕ × ℕ × ℕ × ℤ × ℤ)

def tanFind : List (ℕ × ℕ × ℤ × ℤ × ℤ) → ℕ → Option (ℕ × ℤ × ℤ × ℤ)
  | [], _ => none
  | e :: t, h => if e.1 = h then some e.2 else tanFind t h

theorem tanFind_mem : ∀ (l : List (ℕ × ℕ × ℤ × ℤ × ℤ)) (h : ℕ) (r : ℕ × ℤ × ℤ × ℤ),
    tanFind l h = some r → (h, r) ∈ l
  | [], _, _, hf => by simp [tanFind] at hf
  | e :: t, h, r, hf => by
    unfold tanFind at hf
    split_ifs at hf with he
    · simp only [Option.some.injEq] at hf
      subst hf; subst he; simp
    · exact List.mem_cons_of_mem _ (tanFind_mem t h r hf)

/-- `Cst(c,g,h) = A + N(c+1) - Ld(c+1)` (scaled by `2^P`). -/
def cstOf (tt : TanTab) (ld : LdTab) (c g h : ℕ) : Option ℤ :=
  match tanFind (tt.getD g []) h with
  | some (_, _, A, N) => some (A + N * ((c : ℤ) + 1) - (ld.getD (c + 1) (0, 0)).2)
  | none => none

def witOK1 (tt : TanTab) (ld : LdTab) (c g h : ℕ) : Bool :=
  decide (h < HG) &&
    match cstOf tt ld c g h with
    | some K => decide (K ≤ (c : ℤ) * OFF) && decide ((c : ℤ) * OFF - K + 2 * OFF ≤ 256 * OFF)
    | none => false

def pairs (tt : TanTab) (ld : LdTab) (c g : ℕ) (hs : List ℕ) : List (ℕ × ℕ) :=
  hs.map fun h => (h, ((c : ℤ) * OFF - (cstOf tt ld c g h).getD 0).toNat)

/-! ### The kernel-computed knapsack tables. -/

/-- Level `1`: `K_1 = Wa`, `Kx_1 = Wa` without row 2, `R_1 = Wn`. -/
def lv0 (d : CapData) : ℕ × ℕ × ℕ := (d.Wa, dropRow2 WL HG d.Wa, d.Wn)

/-- One more part: `K_{c+1}`, `Kx_{c+1}` (some part `≠ 2`), `R_{c+1}` (some non-atom part). -/
def lvS (d : CapData) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (fold2 WL HG d.R t.1 d.Wa t.1 d.Wa (fun _ => false) (d.R - 1) 0,
   fold2 WL HG d.R t.2.1 d.Wa t.1 d.Wa (fun m => m != 2) (d.R - 1) 0,
   fold2 WL HG d.R t.2.2 d.Wa t.1 d.Wn (fun _ => true) (d.R - 1) 0)

/-- Tables of level `j + 1`. -/
def lvl (d : CapData) : ℕ → ℕ × ℕ × ℕ
  | 0 => lv0 d
  | j + 1 => lvS d (lvl d j)

/-! ### The checks. -/

def bellLevel (tt : TanTab) (ld : LdTab) (d : CapData) (c : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  (List.range HG).all fun g =>
    let ha := (d.witA.getD (c - 1) []).getD g []
    let hn := (d.witN.getD (c - 1) []).getD g []
    ha.all (witOK1 tt ld c g) && hn.all (witOK1 tt ld c g) &&
    bchk WL HG d.R OFF t.1 d.Wa g 2 (pairs tt ld c g ha) &&
    bchk WL HG d.R OFF (if c = 1 then keepGe3 WL HG d.Wa else t.2.1) d.Wn g 3 (pairs tt ld c g hn)

def phiOf (ph : PhiTab) (n : ℕ) : ℤ := ph.getD n 0

def rootOK1 (ph : PhiTab) (d : CapData) (c : ℕ) (t : ℕ × ℕ × ℕ) (e : ℕ × ℕ × ℕ × ℤ × ℤ) : Bool :=
  e.2.1 != c ||
    (decide (e.1 - 1 < d.R) && decide (e.2.2.1 < HG) &&
      decide ((lane t.2.2 (HG * (e.1 - 1) + e.2.2.1) : ℤ) + e.2.2.2.1 < phiOf ph e.1 + (c : ℤ) * OFF))

def levelOK (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) (c : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  (!(decide (c ≤ d.C)) || bellLevel tt ld d c t) && d.roots.all (rootOK1 ph d c t)

def capLoop (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) : ℕ → ℕ → ℕ × ℕ × ℕ → Bool
  | 0, _, _ => true
  | j + 1, c, t => levelOK tt ld ph d c t && capLoop tt ld ph d j (c + 1) (lvS d t)

/-- The root tangent constant `Troot ≥ 2^P (log t + 1/t - 1)`, `t = 1/(k μ_g)`. -/
def trootOK (e : ℕ × ℕ × ℕ × ℤ × ℤ) : Bool :=
  decide (1 ≤ e.2.1) &&
    logOK (1 / ((e.2.1 : ℚ) * muQ e.2.2.1)) e.2.2.2.2 &&
    decide ((2 : ℚ) ^ PB * (logUB (1 / ((e.2.1 : ℚ) * muQ e.2.2.1)) e.2.2.2.2
      + (e.2.1 : ℚ) * muQ e.2.2.1 - 1) ≤ (e.2.2.2.1 : ℚ))

def leafOK (d : CapData) : Bool :=
  (List.range HG).all fun g => decide ((2 : ℚ) ^ PB * (muQ g - fq) ≤ (lane d.Wa (HG + g) : ℚ) - OFF)

/-- All lanes `< 2^(w-1)`. -/
def halfOK (n v : ℕ) : Bool := (v &&& gd WL n) == 0
/-- All lanes of `Y` `≤` the corresponding lanes of `X`. -/
def allLe (n X Y : ℕ) : Bool := (geD WL n X Y &&& gd WL n) == gd WL n
/-- `v` packs `n` lanes, all `< B`. -/
def dataOK (n v B : ℕ) : Bool := decide (v < 2 ^ (WL * n)) && halfOK n v && allLe n ((B - 1) * rep WL n) v

def capCheck (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) : Bool :=
  decide (3 ≤ d.R) && decide (1 ≤ d.C) && decide (d.kmax ≤ d.C + 1) && decide (d.C + 1 ≤ 120) &&
    dataOK (HG * d.R) d.Wa (2 * OFF) && dataOK (HG * d.R) d.Wn (2 * OFF) && leafOK d &&
    d.roots.all trootOK && d.roots.all (fun e => decide (e.2.1 ≤ d.kmax)) &&
    capLoop tt ld ph d (max d.C d.kmax) 1 (lv0 d)

def tanOK1 (g : ℕ) (e : ℕ × ℕ × ℤ × ℤ × ℤ) : Bool :=
  let u : ℚ := (e.2.1 : ℚ) / UDEN
  decide (e.1 < HG) && decide (0 < u) && decide (2 * muQ g ≤ u) &&
    decide ((u - muQ g) / u ^ 2 ≤ muQ e.1) &&
    decide ((2 : ℚ) ^ PB * ((u - muQ g) / u ^ 2) ≤ (e.2.2.2.2 : ℚ)) &&
    logOK u e.2.2.1 &&
    decide ((2 : ℚ) ^ PB * (logUB u e.2.2.1 + 2 * muQ g / u - 1 - fq) ≤ (e.2.2.2.1 : ℚ))

/-- The tangent table, for `g ∈ [a, b)`. -/
def tanOK (tt : TanTab) (a b : ℕ) : Bool :=
  (List.range' a (b - a)).all fun g => (tt.getD g []).all (tanOK1 g)

/-- `Ld(d) ≤ 2^P log d` for `2 ≤ d ≤ D`. -/
def ldOK (ld : LdTab) (D : ℕ) : Bool :=
  (List.range' 2 (D - 1)).all fun d =>
    logOK (d : ℚ) (ld.getD d (0, 0)).1 &&
      decide (((ld.getD d (0, 0)).2 : ℚ) ≤ (2 : ℚ) ^ PB * logLB (d : ℚ) (ld.getD d (0, 0)).1)

/-! ### Soundness: data bounds. -/

theorem gd_eq (n : ℕ) : gd WL n = pk WL n (fun _ => 2 ^ (WL - 1)) := pk_const WL n _ (by decide)

theorem rep_lane {n v : ℕ} (hv : v < 2 ^ (WL * n)) : v = pk WL n (lane v) := pk_self WL n v hv

theorem lane_pk {n : ℕ} {a : ℕ → ℕ} (ha : Bdd WL n a) {i : ℕ} (hi : i < n) : lane (pk WL n a) i = a i :=
  pk_lane WL n a ha i hi

theorem lane_lt (v i : ℕ) : lane v i < 2 ^ WL := Nat.mod_lt _ (by positivity)

theorem dataOK_spec {n v B : ℕ} (hB1 : 1 ≤ B) (hB : B ≤ 2 ^ (WL - 1)) (h : dataOK n v B = true) :
    Rep WL n v B (lane v) := by
  unfold dataOK halfOK allLe at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hv, hhalf⟩, hle⟩ := h
  have hrep := rep_lane hv
  have hb : Bdd WL n (lane v) := fun i _ => lane_lt v i
  have hw : 1 ≤ WL := by decide
  have h2 := half_lt WL hw
  -- all lanes are `< 2^(w-1)`
  have hhalf' : Half WL n (lane v) := by
    intro i hi
    rw [hrep, gd_eq, pk_land WL n _ _ hb (fun _ _ => by show 2 ^ (WL - 1) < 2 ^ WL; omega),
      ← pk_const_zero WL n] at hhalf
    have := pk_inj WL n _ _ (fun j _ => Nat.and_lt_two_pow _ (by show 2 ^ (WL - 1) < 2 ^ WL; omega))
      (fun _ _ => by positivity) hhalf i hi
    rw [land_top WL _ hw (hb i hi)] at this
    split_ifs at this with hh
    · exact absurd this (by positivity)
    · omega
  refine ⟨hrep, fun i hi => ?_⟩
  have hX : (B - 1) * rep WL n = pk WL n (fun _ => B - 1) := pk_const WL n _ hw
  have hXh : Half WL n (fun _ => B - 1) := fun _ _ => by show B - 1 < 2 ^ (WL - 1); omega
  rw [hX, hrep, geD_pk WL n hw _ _ hXh (fun j hj => (hhalf' j hj).le), gd_eq, pk_land WL n _ _ (geD_bdd WL n hw _ _ hXh)
      (fun _ _ => by show 2 ^ (WL - 1) < 2 ^ WL; omega)] at hle
  have := pk_inj WL n _ _ (fun j _ => Nat.and_lt_two_pow _ (by show 2 ^ (WL - 1) < 2 ^ WL; omega))
    (fun _ _ => by show 2 ^ (WL - 1) < 2 ^ WL; omega) hle i hi
  try simp only at this
  have hlt := geD_bdd WL n hw _ (lane v) hXh i hi
  try simp only at hlt
  rw [land_top WL _ hw hlt] at this
  split_ifs at this with hh
  · omega
  · exact absurd this.symm (by positivity)

/-! ### Soundness: the knapsack levels. -/

section Levels

variable {d : CapData}

theorem rep_zero (n B : ℕ) (hB : 1 ≤ B) : Rep WL n 0 B (fun _ => 0) :=
  ⟨(pk_const_zero WL n).symm, fun _ _ => by show 0 < B; omega⟩

theorem RepL_of {n v B : ℕ} {a : ℕ → ℕ} (h : Rep WL n v B a) (hB : B ≤ 2 ^ WL) : Rep WL n v B (lane v) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [h.1]; apply pk_congr; intro i hi; rw [← h.1]; rw [h.1, lane_pk (h.bdd hB) hi]
  · have := h.2 i hi; rw [h.1, lane_pk (h.bdd hB) hi]; exact this

theorem lane_of_rep {n v B : ℕ} {a : ℕ → ℕ} (h : Rep WL n v B a) (hB : B ≤ 2 ^ WL) {i : ℕ} (hi : i < n) :
    lane v i = a i := by rw [h.1, lane_pk (h.bdd hB) hi]

theorem pow_WL_ge (c : ℕ) (hc : c ≤ 127) : 2 * c * OFF + OFF ≤ 2 ^ (WL - 1) := by
  rw [half_WL]; unfold OFF; nlinarith [Nat.one_le_two_pow (n := 47)]

/-- The three tables of level `j + 1` have lanes `< 2 (j+1) OFF`. -/
theorem lvl_rep (hR : 3 ≤ d.R) (hWa : Rep WL (HG * d.R) d.Wa (2 * OFF) (lane d.Wa))
    (hWn : Rep WL (HG * d.R) d.Wn (2 * OFF) (lane d.Wn)) :
    ∀ j, j + 1 ≤ 127 →
      Rep WL (HG * d.R) (lvl d j).1 (2 * (j + 1) * OFF) (lane (lvl d j).1) ∧
      Rep WL (HG * d.R) (lvl d j).2.1 (2 * (j + 1) * OFF) (lane (lvl d j).2.1) ∧
      Rep WL (HG * d.R) (lvl d j).2.2 (2 * (j + 1) * OFF) (lane (lvl d j).2.2) := by
  have hle : ∀ c, c ≤ 127 → 2 * c * OFF ≤ 2 ^ WL := fun c hc => by
    have := pow_WL_ge c hc; have := pow_half_le WL; omega
  intro j
  induction j with
  | zero =>
    intro _
    simp only [lvl, lv0, zero_add, mul_one]
    refine ⟨hWa, ?_, hWn⟩
    exact RepL_of (dropRow2_rep (hle 1 (by norm_num)) hR hWa) (hle 1 (by norm_num))
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hB : 2 * (j + 1) * OFF + 2 * OFF ≤ 2 ^ (WL - 1) := by have := pow_WL_ge (j + 2) (by omega); nlinarith
    have hH : 1 ≤ HG := by decide
    have hw : 1 ≤ WL := by decide
    have e : 2 * (j + 1) * OFF + 2 * OFF = 2 * (j + 1 + 1) * OFF := by ring
    have hz := rep_zero (HG * d.R) (2 * (j + 1) * OFF + 2 * OFF) (by have : 1 ≤ OFF := Nat.one_le_two_pow; nlinarith)
    obtain ⟨L1, hL1, -, -⟩ := fold2_spec WL HG d.R hw hH hB h1 hWa h1 hWa (fun _ => false) (d.R - 1) 0 _
      (by omega) hz
    obtain ⟨L2, hL2, -, -⟩ := fold2_spec WL HG d.R hw hH hB h2 hWa h1 hWa (fun m => m != 2) (d.R - 1) 0 _
      (by omega) hz
    obtain ⟨L3, hL3, -, -⟩ := fold2_spec WL HG d.R hw hH hB h3 hWa h1 hWn (fun _ => true) (d.R - 1) 0 _
      (by omega) hz
    rw [e] at hL1 hL2 hL3
    simp only [lvl, lvS]
    exact ⟨RepL_of hL1 (hle _ (by omega)), RepL_of hL2 (hle _ (by omega)), RepL_of hL3 (hle _ (by omega))⟩

/-- The knapsack inequalities between consecutive levels. -/
theorem lvl_step (hR : 3 ≤ d.R) (hWa : Rep WL (HG * d.R) d.Wa (2 * OFF) (lane d.Wa))
    (hWn : Rep WL (HG * d.R) d.Wn (2 * OFF) (lane d.Wn)) (j : ℕ) (hj : j + 2 ≤ 127)
    (m N h : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) (hN : N < d.R) (hh : h < HG) :
    lane (lvl d j).1 (HG * (N - m) + h) + lane d.Wa (HG * m + h) ≤ lane (lvl d (j + 1)).1 (HG * N + h) ∧
    lane (lvl d j).2.1 (HG * (N - m) + h) + lane d.Wa (HG * m + h) ≤ lane (lvl d (j + 1)).2.1 (HG * N + h) ∧
    (m ≠ 2 → lane (lvl d j).1 (HG * (N - m) + h) + lane d.Wa (HG * m + h)
      ≤ lane (lvl d (j + 1)).2.1 (HG * N + h)) ∧
    lane (lvl d j).2.2 (HG * (N - m) + h) + lane d.Wa (HG * m + h) ≤ lane (lvl d (j + 1)).2.2 (HG * N + h) ∧
    lane (lvl d j).1 (HG * (N - m) + h) + lane d.Wn (HG * m + h) ≤ lane (lvl d (j + 1)).2.2 (HG * N + h) := by
  obtain ⟨h1, h2, h3⟩ := lvl_rep hR hWa hWn j (by omega)
  have hB : 2 * (j + 1) * OFF + 2 * OFF ≤ 2 ^ (WL - 1) := by have := pow_WL_ge (j + 2) (by omega); nlinarith
  have hBw : 2 * (j + 1) * OFF + 2 * OFF ≤ 2 ^ WL := le_trans hB (pow_half_le WL)
  have hH : 1 ≤ HG := by decide
  have hw : 1 ≤ WL := by decide
  have hz := rep_zero (HG * d.R) (2 * (j + 1) * OFF + 2 * OFF) (by have : 1 ≤ OFF := Nat.one_le_two_pow; nlinarith)
  have hi : HG * N + h < HG * d.R := by
    have : HG * N + HG ≤ HG * d.R := by nlinarith
    omega
  obtain ⟨L1, hL1, -, hT1⟩ := fold2_spec WL HG d.R hw hH hB h1 hWa h1 hWa (fun _ => false) (d.R - 1) 0 _
    (by omega) hz
  obtain ⟨L2, hL2, -, hT2⟩ := fold2_spec WL HG d.R hw hH hB h2 hWa h1 hWa (fun m => m != 2) (d.R - 1) 0 _
    (by omega) hz
  obtain ⟨L3, hL3, -, hT3⟩ := fold2_spec WL HG d.R hw hH hB h3 hWa h1 hWn (fun _ => true) (d.R - 1) 0 _
    (by omega) hz
  have e1 : lane (lvl d (j + 1)).1 (HG * N + h) = L1 (HG * N + h) := lane_of_rep hL1 hBw hi
  have e2 : lane (lvl d (j + 1)).2.1 (HG * N + h) = L2 (HG * N + h) := lane_of_rep hL2 hBw hi
  have e3 : lane (lvl d (j + 1)).2.2 (HG * N + h) = L3 (HG * N + h) := lane_of_rep hL3 hBw hi
  have t1 := hT1 m hm1 (by omega) N hN h hh hmN
  have t2 := hT2 m hm1 (by omega) N hN h hh hmN
  have t3 := hT3 m hm1 (by omega) N hN h hh hmN
  refine ⟨?_, ?_, fun hm2 => ?_, ?_, ?_⟩
  · rw [e1]; exact t1.1
  · rw [e2]; exact t2.1
  · rw [e2]; exact t2.2 (by simp [hm2])
  · rw [e3]; exact t3.1
  · rw [e3]; exact t3.2 rfl

end Levels

/-! ### Soundness: the loop. -/

theorem capLoop_spec (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) :
    ∀ (j c : ℕ), 1 ≤ c → capLoop tt ld ph d j c (lvl d (c - 1)) = true →
      ∀ c', c ≤ c' → c' < c + j → levelOK tt ld ph d c' (lvl d (c' - 1)) = true := by
  intro j
  induction j with
  | zero => intro c _ _ c' h1 h2; omega
  | succ j ih =>
    intro c hc h c' h1 h2
    simp only [capLoop, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · have hnext : lvS d (lvl d (c - 1)) = lvl d (c + 1 - 1) := by
        rw [show c + 1 - 1 = (c - 1) + 1 by omega]; rfl
      rw [hnext] at h
      exact ih (c + 1) (by omega) h.2 c' (by omega) (by omega)

/-! ### Soundness: the tangent constants. -/

theorem tanB_entry (tt : TanTab) (ld : LdTab) (D : ℕ) (hT : tanOK tt 0 HG = true) (hL : ldOK ld D = true)
    (c g h : ℕ) (hc1 : 1 ≤ c) (hcD : c + 1 ≤ D) (hg : g < HG) (K : ℤ) (hK : cstOf tt ld c g h = some K) :
    TanB (fq : ℝ) (muQ g : ℝ) (muQ h : ℝ) c ((K : ℝ) / 2 ^ PB) := by
  unfold cstOf at hK
  split at hK
  · rename_i unum m A N hf
    simp only [Option.some.injEq] at hK
    have hmem := tanFind_mem _ _ _ hf
    have hok : tanOK1 g (h, unum, m, A, N) = true := by
      unfold tanOK at hT
      rw [List.all_eq_true] at hT
      have := hT g (by simp [List.mem_range']; exact hg)
      rw [List.all_eq_true] at this
      exact this _ hmem
    unfold tanOK1 at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨_, hu0⟩, hu⟩, hν⟩, hN⟩, hlog⟩, hA⟩ := hok
    have hld : ldOK ld D = true := hL
    unfold ldOK at hld
    rw [List.all_eq_true] at hld
    have hd := hld (c + 1) (by simp only [List.mem_range'_1]; omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨hdlog, hdle⟩ := hd
    have hLd := logLB_le_log _ _ hdlog
    have hUB := log_le_logUB _ _ hlog
    set u : ℚ := (unum : ℚ) / UDEN
    set Ld := (ld.getD (c + 1) (0, 0)).2
    have hPB : (0 : ℝ) < 2 ^ PB := by positivity
    rw [← hK]
    have hT := tanB_of (f := (fq : ℝ)) (μ := (muQ g : ℝ)) (ν := (muQ h : ℝ)) (u := (u : ℝ))
      (A := (A : ℝ) / 2 ^ PB) (N := (N : ℝ) / 2 ^ PB) (Ld := (Ld : ℝ) / 2 ^ PB) c
      (by unfold muQ; push_cast; positivity)
      (by
        have : (muQ g : ℝ) ≤ 1 / 2 := by
          unfold muQ; push_cast
          have : (g : ℝ) ≤ 99 := by
            have : g ≤ 99 := by unfold HG at hg; omega
            exact_mod_cast this
          linarith
        have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
        linarith)
      (by exact_mod_cast hu0) (by exact_mod_cast hu) (by exact_mod_cast hν)
      (by
        rw [le_div_iff₀ hPB]
        have := (Rat.cast_le (K := ℝ)).mpr hN
        push_cast at this; linarith)
      (by
        rw [le_div_iff₀ hPB]
        have h1 := (Rat.cast_le (K := ℝ)).mpr hA
        push_cast at h1 hUB
        nlinarith)
      (by
        rw [div_le_iff₀ hPB]
        have h1 := (Rat.cast_le (K := ℝ)).mpr hdle
        push_cast at h1 hLd
        nlinarith [mul_le_mul_of_nonneg_left hLd hPB.le])
    convert hT using 1
    push_cast; ring
  · simp at hK

end EnvCert
end R3Cert
