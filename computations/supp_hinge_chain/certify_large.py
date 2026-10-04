"""Chain route (rem:lam-large-check; cherry regime, large lam): sharp ceiling log T_b <= |b| F*, F* = (1/2)log(1+lam/2), for lam in [LAM0, LAM1] (>= 1+sqrt5).
Witness per lam-box: U(y) = min(0, l_1(y), ..., l_n(y)), l_i affine with negative slope (concave by construction, U <= 0), with
U = 0 on [0, y_fr], y_fr = y_ch(lam_lo) >= y_ch(lam) on the box.  The lines come from an (untrusted) LP; everything is re-checked here.
Induction (non-leaf branches b: l(b) <= U(y_b)); every non-leaf vertex v is exactly one of:
 (B)  base (not single-child): pooled over non-leaf children (Jensen, U concave).  k >= 1 leaf children: by hand (as for the hinge at lam_c;
      y_v <= y_ch so U(y_v) = 0; k = 1: R/d <= 1/2; k >= 2: (1+lam/2)^{3/2} >= 1+lam for lam >= lam_c).  k = 0, m >= 2: boxes / tail.
 (R1) single child c which is a base: l(v) = l(c) + log(1 + lam y_c/2) - F*, l(c) <= pooled base expression; top message 1/(2+lam y_c).
 (T)  single child c1 which is single-child with child c2 (non-leaf): U(y) + log((4+lam+2 lam y)/(4+2lam)) <= U(f(f(y))), f(y) = 1/(2+lam y).
Tails (lemmas in the docstring of tails()): base k=0, m >= M0; R1 with k' >= KR or m' >= MR."""
import sys, math, time
import numpy as np
from scipy.optimize import linprog
from mpmath import iv, mpf
iv.dps = 30
# ---------------- untrusted witness construction (float LP) ----------------
def lp_witness(lams, NX=70, K=5, M=14, rounds=12):
    Fsv = [math.log1p(l/2)/2 for l in lams]; yfr = 1/(2 + min(lams)); lmax = max(lams)
    xs = np.unique(np.concatenate([[0.0, yfr], np.geomspace(yfr, 0.5, NX)])); N = len(xs) + 1
    flat = [i for i, x in enumerate(xs) if x <= yfr + 1e-15]
    def interp(y):
        r = np.zeros(N); y = min(max(y, 0.0), 0.5); i = min(max(np.searchsorted(xs, y) - 1, 0), len(xs) - 2)
        w = (y - xs[i])/(xs[i+1] - xs[i]); r[i] = 1-w; r[i+1] = w; return r
    def base_parts(lam, Fs, k, m, yb):
        d = k+m+1; R = k + m*yb; return (-k*Fs + math.log1p(lam*R/d) - Fs), 1/(d + lam*R)
    def c_base(lam, Fs, k, m, yb):
        cst, yv = base_parts(lam, Fs, k, m, yb); r = (m*interp(yb) if m else np.zeros(N)) - interp(yv); r[N-1] = 1.0; return r, -cst
    def c_r1(lam, Fs, k, m, yb):
        cst, yb_ = base_parts(lam, Fs, k, m, yb); cst += math.log1p(lam*yb_/2) - Fs
        r = (m*interp(yb) if m else np.zeros(N)) - interp(1/(2 + lam*yb_)); r[N-1] = 1.0; return r, -cst
    def c_T(lam, y):
        f2 = 1/(2 + lam/(2 + lam*y)); r = interp(y) - interp(f2); r[N-1] = 1.0
        return r, -math.log((4 + lam + 2*lam*y)/(4 + 2*lam))
    conc = []
    for i in range(len(xs)-2):
        d1, d2 = xs[i+1]-xs[i], xs[i+2]-xs[i+1]; rr = np.zeros(N); rr[i] = 1/d1; rr[i+1] = -1/d1-1/d2; rr[i+2] = 1/d2; conc.append(rr)
    A, b = [], []
    g0 = np.geomspace(yfr*1e-2, 0.5, 14); gf = np.geomspace(yfr*1e-3, 0.5, 120)
    for lam, Fs in zip(lams, Fsv):
        for y in g0: r, bb = c_T(lam, y); A.append(r); b.append(bb)
        for k in range(0, 4):
            for m in range(0, 6):
                if k+m == 0 or (k == 0 and m == 1): continue
                for yb in (g0 if m else [0.0]):
                    if k == 0: r, bb = c_base(lam, Fs, k, m, yb); A.append(r); b.append(bb)
                    r, bb = c_r1(lam, Fs, k, m, yb); A.append(r); b.append(bb)
    bounds = [(0.0, 0.0) if i in flat else (None, 0.0) for i in range(len(xs))] + [(None, 1.0)]
    for it in range(rounds):
        c = np.zeros(N); c[N-1] = -1
        res = linprog(c, A_ub=np.array(conc + A), b_ub=np.array([0.0]*len(conc) + b), bounds=bounds, method="highs")
        if not res.success: return None
        u = res.x[:N-1]; t = -res.fun; U = lambda y: np.interp(y, xs, u); cuts = []
        for lam, Fs in zip(lams, Fsv):
            f2 = 1/(2 + lam/(2 + lam*gf)); v = U(gf) + np.log((4 + lam + 2*lam*gf)/(4 + 2*lam)) - U(f2) + t
            i = int(np.argmax(v));  cuts += [(v[i], 'T', lam, Fs, 0, 0, gf[i])] if v[i] > 1e-9 else []
            for k in range(0, K+1):
                for m in range(0, M+1):
                    if k+m == 0 or (k == 0 and m == 1): continue
                    YB = gf if m else np.array([0.0]); d = k+m+1; R = k+m*YB; yv = 1/(d+lam*R)
                    base = -k*Fs + (m*U(YB) if m else 0) + np.log1p(lam*R/d) - Fs
                    if k == 0:
                        v = base - U(yv) + t; i = int(np.argmax(v))
                        if v[i] > 1e-9: cuts.append((v[i], 'B', lam, Fs, k, m, float(YB[i])))
                    v = base + np.log1p(lam*yv/2) - Fs - U(1/(2+lam*yv)) + t; i = int(np.argmax(v))
                    if v[i] > 1e-9: cuts.append((v[i], 'R', lam, Fs, k, m, float(YB[i])))
        if not cuts: return t, xs, u
        cuts.sort(key=lambda z: -z[0])
        for _, kind, lam, Fs, k, m, y in cuts[:600]:
            r, bb = (c_T(lam, y) if kind == 'T' else c_base(lam, Fs, k, m, y) if kind == 'B' else c_r1(lam, Fs, k, m, y)); A.append(r); b.append(bb)
    return t, xs, u
# ---------------- rigorous checks ----------------
def lines_from(xs, u, yfr):
    """affine pieces (slope, intercept) as exact binary-float rationals, only for segments right of the flat part."""
    L = []
    for i in range(len(xs)-1):
        if xs[i+1] <= yfr: continue
        a = (u[i+1]-u[i])/(xs[i+1]-xs[i]); c = u[i] - a*xs[i]
        # lift by 1e-12 so every line is >= 0 on the flat part despite float rounding (still a min of lines: concave)
        if a < 0: L.append((iv.mpf(float(a)), iv.mpf(float(c)) + iv.mpf('1e-12')))   # exact: binary floats are rationals
    return L
def Uiv(Y, Ls):
    vals = [iv.mpf(0)] + [a*Y + c for a, c in Ls]
    return iv.mpf([min(v.a for v in vals), min(v.b for v in vals)])
def bisect(fun, lo, hi, depth=34):
    """certify sup fun(Y) < 0 on [lo,hi] by bisection; returns (ok, boxes, bad_interval)"""
    stack = [(mpf(lo), mpf(hi), 0)]; nb = 0
    while stack:
        p, q, dp = stack.pop()
        if fun(iv.mpf([p, q])).b < 0: nb += 1; continue
        if dp >= depth: return False, nb, (float(p), float(q))
        h = (p+q)/2; stack += [(p, h, dp+1), (h, q, dp+1)]
    return True, nb, None
def cert_box(a, b):
    a, b = mpf(a), mpf(b)
    wt = lp_witness([float(a), float((a*b)**0.5), float(b)])
    if wt is None: return False, "LP failed", 0
    t, xs, u = wt; yfr_f = 1/(2 + float(a))
    Ls = lines_from(xs, u, yfr_f)
    LAM = iv.mpf([a, b]); Fs = iv.log(1 + LAM/2)/2; ych = 1/(2 + LAM); yfr = 1/(2 + iv.mpf(a))
    half = iv.mpf('0.5')
    # structural checks: U = 0 on [0, yfr] (every line >= 0 at yfr, slopes negative); lam_lo >= lam_c
    if not all((al*yfr + c).a >= 0 for al, c in Ls): return False, "flat part not certified", 0
    if (1 + iv.sqrt(5)).b > a: return False, "box below lam_c", 0
    # first line (smallest |slope|, i.e. the one active just right of the flat part): pick the line with the rightmost root
    roots = [(-c/al) for al, c in Ls]; i1 = max(range(len(Ls)), key=lambda i: float(roots[i].mid))
    a1, c1 = Ls[i1]; z1 = -c1/a1                                            # U(y) <= a1 (y - z1) for all y
    Umin = Uiv(half, Ls)                                                   # U nonincreasing: min on [0,1/2] at 1/2
    ydag = (iv.exp(Fs) - 1)/LAM
    if not (z1.b < ydag.a): return False, "z1 >= ydag", 0   # G-D1 strict
    nb = 0
    # ---- (T) two-step chains
    T = lambda Y, LL=LAM: Uiv(Y, Ls) + iv.log((4 + LL + 2*LL*Y)/(4 + 2*LL)) - Uiv(1/(2 + LL/(2 + LL*Y)), Ls)
    ok, n, bad = bisect(lambda Y: T(Y), 0, '0.5'); nb += n
    if not ok: return False, ("T", bad), nb
    # ---- (B) base k = 0, m >= 2: finite range + tail
    slope_need = LAM/(1 + LAM*z1)                                          # need m |a1| >= this
    M0 = int(max(math.ceil(float((1/yfr).b)), math.ceil(float((slope_need/(-a1)).b)))) + 1
    for m in range(2, M0):
        f = lambda Y, m=m: m*Uiv(Y, Ls) + iv.log(1 + LAM*m*Y/(m+1)) - Fs - Uiv(1/(m + 1 + LAM*m*Y), Ls)
        ok, n, bad = bisect(f, 0, '0.5'); nb += n
        if not ok: return False, ("B", m, bad), nb
    # tail m >= M0: y_v <= 1/(m+1) <= yfr => U(y_v) = 0; max_Y (m U(Y) + log(1+lam Y)) <= log(1+lam z1) <= F* (z1 <= ydag)  [checked]
    # ---- (R1) one-step chains over bases (k', m'), not (0,0) or (0,1)
    grow = iv.log(1 + LAM*ych/2) - Fs                                       # gain bound when base has a leaf child (y_b <= y_ch)
    KR = 1
    while not ((-(KR + 1)*Fs + iv.log(1 + LAM) + grow - Umin).b < 0): KR += 1   # G-D1 strict
    for k in range(0, KR):
        # m' tail: -(k+1)F* + log(1+lam z1) + lam k/(m+1) + log(1 + lam/(2(m+1))) - F* - Umin <= 0, and m|a1| >= slope_need
        MR = max(2, int(math.ceil(float((slope_need/(-a1)).b))) + 1)
        while not ((-(k+1)*Fs + iv.log(1 + LAM*z1) + LAM*k/(MR + 1) + iv.log(1 + LAM/(2*(MR + 1))) - Fs - Umin).b < 0): MR += 1   # G-D1 strict
        for m in range(0, MR):
            if k + m == 0 or (k == 0 and m == 1): continue
            def f(Y, k=k, m=m):
                d = k + m + 1; R = k + m*Y; yb = 1/(d + LAM*R)
                base = -k*Fs + (m*Uiv(Y, Ls) if m else 0) + iv.log(1 + LAM*R/d) - Fs
                return base + iv.log(1 + LAM*yb/2) - Fs - Uiv(1/(2 + LAM*yb), Ls)
            ok, n, bad = bisect(f, 0, '0.5' if m else 0); nb += n
            if not ok: return False, ("R1", k, m, bad), nb
    return True, (round(t, 4), M0, KR), nb
if __name__ == "__main__":
    lo, hi, ratio = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    a = lo; tot = 0; t0 = time.time()
    while a < hi:
        b_ = min(a*ratio, hi); ok, info, nb = cert_box(a, b_); tot += nb
        if not ok:
            # split once into 4
            sub = [a*(b_/a)**(i/4) for i in range(5)]; allok = True
            for i in range(4):
                ok2, info2, nb2 = cert_box(sub[i], sub[i+1]); tot += nb2
                if not ok2: print(f"FAIL [{sub[i]:.3f},{sub[i+1]:.3f}]: {info2}", flush=True); allok = False; break
                print(f"  [{sub[i]:.3f}, {sub[i+1]:.3f}] ok (split sub-box) {info2}  ({nb2} boxes)", flush=True)   # M-D2
            if not allok: break
        else:
            print(f"  [{a:.3f}, {b_:.3f}] ok {info}  ({nb} boxes, {time.time()-t0:.0f}s)", flush=True)
        a = b_
    else:
        print(f"THEOREM D: lam in [{lo}, {hi}] CERTIFIED; {tot} boxes; {time.time()-t0:.0f}s")
