"""Rigorous certificate: sharp ceiling for lam in [LAM0, LAM1] (arm regime), pooled form (leaves exact, Jensen over
non-leaf children, messages in [0,1/2]).  Witness U = min(0, -s1 (y - y0), -eps - kap (y - ych)), where
  F* = max_j r_j(lam), ych = 1/(2+lam), eps = 2F* - log(1+lam/2), ydag = (e^{F*}-1)/lam, y0 = THETA ydag,
  s1 = eps/(ych - y0), kap = KK F*/(1/2 - ych).
Obligation: for every (k leaf children, m non-leaf children, mean ybar), other than the cherry (k=1, m=0; exact):
  Phi = -k F* + m U(ybar) + log(1 + lam R/d) - F* - U(1/(d + lam R)) <= 0,  d = k+m+1, R = k + m ybar.
Pieces (see the witness covers of [0.1,3.22]): exact lemmas for (a) arms satisfying the slope conditions on R1 = {y_v <= y0},
(b) k = 0 tail m >= M_t, (c) k >= 1 tails; mpmath.iv boxes for everything else."""
import sys, math, time
from mpmath import iv, mpf
iv.dps = 25
THETA, KK = iv.mpf('0.8'), iv.mpf('0.5')
def r_j(j, x):   # arm rate, interval
    return (j*iv.log(1 + x/2) + iv.log(1 + x*j/((2 + x)*(j + 1)))) / (2*j + 1)
def Fstar_point(x):
    """Rigorous enclosure of F*(x) = sup_j r_j(x) (x a point interval, lam < 1+sqrt5)."""
    xf = float(x.mid); L = 0.5*math.log1p(xf/2)
    rf = [(j*math.log1p(xf/2) + math.log1p(xf*j/((2+xf)*(j+1))))/(2*j+1) for j in range(1, 200000)]
    js = max(range(len(rf)), key=lambda i: rf[i]) + 1
    J = max(4*js, 200)
    lo = max(r_j(j, x).a for j in range(max(1, js-3), js+4))
    hi = max(r_j(j, x).b for j in range(1, J+1))
    # tail j > J: r_j <= L + g/(2J+1), g = log((2+2x)/(2+x)) - L_x  (numerator increasing in j, bounded by its limit)
    Lx = iv.log(1 + x/2)/2; g = iv.log((2 + 2*x)/(2 + x)) - Lx
    tail = (Lx + g/(2*J + 1)).b
    return iv.mpf([lo, max(hi, tail)]), js
def eps_enclosure(a, b, ja, jb):
    """Tight enclosure of eps(lam) = 2 max_j (r_j - L) over [a, b] by the mean-value form per arm, with a rigorous
    tail for large j: 2(r_j - L) <= 2 g_max/(2j+1) (numerator increasing in j, bounded by its limit g)."""
    L = iv.mpf([a, b]); mid = iv.mpf((a + b)/2); w = (b - a)/2; W = iv.mpf([-w, w])
    J = max(4*max(ja, jb), 400)
    def f(j, x):  return 2*(r_j(j, x) - iv.log(1 + x/2)/2)
    def fp(j, x):
        u1 = (j*iv.mpf('0.5')/(1 + x/2)); up = (iv.mpf(j)/(j + 1))*2/(2 + x)**2; u = x*j/((2 + x)*(j + 1))
        return 2*((u1 + up/(1 + u))/(2*j + 1) - iv.mpf('0.25')/(1 + x/2))
    lo = max((f(j, mid) + fp(j, L)*W).a for j in range(max(1, min(ja, jb) - 3), max(ja, jb) + 4))
    hi = max((f(j, mid) + fp(j, L)*W).b for j in range(1, J + 1))
    gmax = (iv.log((2 + 2*L)/(2 + L)) - iv.log(1 + L/2)/2).b
    hi = max(hi, 2*gmax/(2*J + 1))
    return iv.mpf([lo, hi])
def witness(L, Fs, eps=None):
    ych = 1/(2 + L)
    if eps is None: eps = 2*Fs - iv.log(1 + L/2)
    ydag = (iv.exp(Fs) - 1)/L; y0 = THETA*ydag
    s1 = eps/(ych - y0); kap = KK*Fs/(iv.mpf('0.5') - ych)
    return ych, eps, y0, s1, kap
def U(y, W):
    ych, eps, y0, s1, kap = W
    a = iv.mpf(0); b = -s1*(y - y0); c = -eps - kap*(y - ych)
    return iv.mpf([min(a.a, b.a, c.a), min(a.b, b.b, c.b)])
def Phi(k, m, L, Y, Fs, W):
    d = k + m + 1; R = k + m*Y
    return -k*Fs + (m*U(Y, W) if m else 0) + iv.log(1 + L*R/d) - Fs - U(1/(d + L*R), W)
def cert_box(a, b):
    L = iv.mpf([a, b])
    Fa, ja = Fstar_point(iv.mpf(a)); Fb, jb = Fstar_point(iv.mpf(b))
    Fs = iv.mpf([Fa.a, Fb.b])                                    # F* increasing in lam
    W = witness(L, Fs, eps_enclosure(a, b, ja, jb)); ych, eps, y0, s1, kap = W
    assert (y0.b < ych.a) and (kap.a > s1.b) and eps.a > 0, "witness shape"
    half = iv.mpf('0.5'); nb = 0
    # ---- k = 0 ----
    Mt = int(max(math.ceil(1/float(y0.a)), math.ceil(float((L.b/(s1*(1 + L*y0))).b)))) + 1
    for m in range(1, Mt):
        ym = 1/(m + 1 + L*m*ych)
        # the lemma needs l(A_m) <= 0, i.e. r_m <= F*; F* = sup_j r_j by definition, and we also
        # check the enclosure is consistent with it (Fs.b >= r_m lower end) so a lowered F* cannot slip through.
        analytic = (ym.b <= y0.a) and (s1.b <= (L*ym).a) and ((L*ym).b <= kap.a)
        stack = [(mpf(0), mpf('0.5'), 0)]
        while stack:
            p, q, dep = stack.pop(); Y = iv.mpf([p, q])
            if analytic and not (r_j(m, iv.mpf(a)).a <= Fa.b and r_j(m, iv.mpf(b)).a <= Fb.b):
                raise AssertionError('G2/E2: F* enclosure below arm rate at a box endpoint')
            if analytic and (1/(m + 1 + L*m*p)).b <= y0.a:        # cell inside R1: Phi <= l(A_m) <= 0 (lemma a)
                nb += 1; continue
            if Phi(0, m, L, Y, Fs, W).b < 0: nb += 1; continue
            if dep > 30: return False, ("k=0", m, float(p), float(q)), nb
            h = (p + q)/2; stack += [(p, h, dep+1), (h, q, dep+1)]
    # ---- k >= 1 ----
    Umax = eps + kap*(half - ych)                                 # -U(y) <= Umax on [0, 1/2]
    K0 = 1
    while not (((K0 + 1)*Fs - iv.log(1 + L) - Umax).a >= 0): K0 += 1
    delta = iv.log(1 + L/2) - iv.log(1 + L*ych)
    for k in range(1, K0):
        need = max(float((1/y0).b), float((L*k/(delta + (k-1)*Fs)).b), float((L/kap).b))
        M1 = int(math.ceil(need)) + 2
        for m in range(0, M1):
            if k == 1 and m == 0: continue                        # cherry: exact equality
            stack = [(mpf(0), mpf('0.5'), 0)] if m else [(mpf(0), mpf(0), 0)]
            while stack:
                p, q, dep = stack.pop(); Y = iv.mpf([p, q])
                if Phi(k, m, L, Y, Fs, W).b < 0: nb += 1; continue
                if dep > 30: return False, ("k>=1", k, m, float(p), float(q)), nb
                h = (p + q)/2; stack += [(p, h, dep+1), (h, q, dep+1)]
    return True, (ja, jb, Mt, K0), nb
if __name__ == "__main__":
    LAM0, LAM1, STEP = mpf(sys.argv[1]), mpf(sys.argv[2]), mpf(sys.argv[3])
    x = LAM0; tot = 0; t0 = time.time(); failures = []
    while x < LAM1:
        y = min(x + STEP, LAM1)
        ok, info, nb = cert_box(x, y); tot += nb
        if not ok:
            # retry with finer lambda-boxes
            sub = (y - x)/8; z = x; okall = True
            while z < y:
                w_ = min(z + sub, y); ok2, info2, nb2 = cert_box(z, w_); tot += nb2
                if not ok2: okall = False; failures.append((float(z), float(w_), info2)); break
                z = w_
            if not okall: print("FAIL", failures[-1]); break
        x = y
    print(f"lam in [{LAM0}, {LAM1}]: {'CERTIFIED' if not failures else 'NOT certified'}; {tot} boxes; {time.time()-t0:.0f}s; last info {info}")
