"""POWER-SHOULDER variant (p = 1.5): U = 0 (y<=q); -eps ((y-q)/(y_ch-q))^p on [q, y_ch]; -eps - kap (y-y_ch) beyond.
Derived from certify_quad.py (quadratic shoulder); same proof structure, left slope at y_ch = p eps/(y_ch - q).
Original docstring of the quadratic variant follows.
Rigorous certificate, low arm regime: sharp ceiling for lam in [LAM0, LAM1] with the quadratic-shoulder witness
  U(y) = 0 (y <= q);  -k2 (y-q)^2 (q <= y <= y_ch);  -eps - kap (y - y_ch) (y >= y_ch),
  q = THETA * ydag, ydag = (e^{F*}-1)/lam, k2 = eps/(y_ch-q)^2, kap = KF F*/(1/2 - y_ch)  (concavity: kap >= 2 eps/(y_ch-q)).
Pooled form (leaves exact, Jensen over non-leaf children). Pieces:
 (a) exact arm lemma on R1 = {y_v <= q}: if y_m <= q and 2eps/(y_ch-q) <= lam y_m <= kap then Phi_m <= l(A_m) <= 0 on R1;
 (b) k=0 tail m >= max(1/q, (log(1+lam/2) - F*)/|U(ydag)|): R1 is everything; ybar <= ydag gives Phi <= log(1+lam ydag) - F* = 0,
     ybar >= ydag gives Phi <= m U(ydag) + log(1+lam/2) - F* <= 0;
 (c) k >= 1 tails as in certify_arm.py (with q in place of y0); (d) interval boxes elsewhere; cherry exact."""
import sys, math, time
from mpmath import iv, mpf
from certify_arm import r_j, Fstar_point, eps_enclosure
iv.dps = 25
THETA, KF, PW = iv.mpf('0.93'), iv.mpf('0.15'), iv.mpf('1.5')
def witness(L, Fs, eps):
    ych = 1/(2 + L); ydag = (iv.exp(Fs) - 1)/L; q = THETA*ydag
    k2 = None; kap = KF*Fs/(iv.mpf('0.5') - ych); s1q = PW*eps/(ych - q)
    return dict(ych=ych, eps=eps, q=q, k2=k2, kap=kap, s1q=s1q, ydag=ydag)
def Upt(p, W):
    """Enclosure of U at a point p (p an mpf) with interval parameters: hull of the pieces that may apply."""
    q, ych, k2, eps, kap = W['q'], W['ych'], W['k2'], W['eps'], W['kap']
    P = iv.mpf(p); S = []
    if p <= q.b: S.append(iv.mpf(0))
    if p >= q.a and p <= ych.b:
        z = (P - q)/(ych - q); t = iv.mpf([max(mpf(0), z.a), max(mpf(0), z.b)]); S.append(-eps*t*iv.sqrt(t))
    if p >= ych.a: S.append(-eps - kap*(P - ych))
    return iv.mpf([min(s.a for s in S), max(s.b for s in S)])
def U(Y, W):   # U nonincreasing and continuous: U(Y) subset [U(Y.b), U(Y.a)]
    Y = iv.mpf(Y); return iv.mpf([Upt(Y.b, W).a, Upt(Y.a, W).b])
def Phi(k, m, L, Y, Fs, W):
    d = k + m + 1; R = k + m*Y
    return -k*Fs + (m*U(Y, W) if m else 0) + iv.log(1 + L*R/d) - Fs - U(1/(d + L*R), W)
def cert_box(a, b):
    L = iv.mpf([a, b])
    Fa, ja = Fstar_point(iv.mpf(a)); Fb, jb = Fstar_point(iv.mpf(b)); Fs = iv.mpf([Fa.a, Fb.b])
    eps = eps_enclosure(a, b, ja, jb); W = witness(L, Fs, eps)
    q, ych, kap, s1q, ydag = W['q'], W['ych'], W['kap'], W['s1q'], W['ydag']
    assert q.b < ych.a and eps.a > 0 and kap.a >= s1q.b, "witness shape"
    half = iv.mpf('0.5'); nb = 0
    # (b) k = 0 tail
    # U(ydag) in closed form with q = THETA*ydag kept correlated: U(ydag) = -eps((1-THETA)ydag/(ych-THETA ydag))^p
    assert ydag.b <= ych.a, 'P1: closed form for U(ydag) needs ydag <= y_ch'
    Uydag = (-eps*(((1 - THETA)*ydag/(ych - THETA*ydag))**PW)).b
    assert Uydag < 0
    Mt = int(max(math.ceil(float((1/q).b)), math.ceil(float(((iv.log(1 + L/2) - Fs)/(-iv.mpf(Uydag))).b)))) + 1
    for m in range(1, Mt):
        ym = 1/(m + 1 + L*m*ych)
        # the lemma needs l(A_m) <= 0, i.e. r_m <= F*; F* = sup_j r_j by definition, and we also
        # check the enclosure is consistent with it (Fs.b >= r_m lower end) so a lowered F* cannot slip through.
        analytic = (ym.b <= q.a) and (s1q.b <= (L*ym).a) and ((L*ym).b <= kap.a)
        stack = [(mpf(0), mpf('0.5'), 0)]
        while stack:
            p, r, dep = stack.pop(); Y = iv.mpf([p, r])
            if analytic and not (r_j(m, iv.mpf(a)).a <= Fa.b and r_j(m, iv.mpf(b)).a <= Fb.b):
                raise AssertionError('G2/E2: F* enclosure below arm rate at a box endpoint')
            if analytic and (1/(m + 1 + L*m*p)).b <= q.a: nb += 1; continue
            if Phi(0, m, L, Y, Fs, W).b < 0: nb += 1; continue
            if dep > 32: return False, ("k=0", m, float(p), float(r)), nb
            h = (p + r)/2; stack += [(p, h, dep+1), (h, r, dep+1)]
    # (c) k >= 1
    Umax = eps + kap*(half - ych)
    K0 = 1
    while not (((K0 + 1)*Fs - iv.log(1 + L) - Umax).a >= 0): K0 += 1
    delta = iv.log(1 + L/2) - iv.log(1 + L*ych)
    for k in range(1, K0):
        need = max(float((1/q).b), float((L*k/(delta + (k-1)*Fs)).b), float((L/kap).b))
        M1 = int(math.ceil(need)) + 2
        for m in range(0, M1):
            if k == 1 and m == 0: continue
            stack = [(mpf(0), mpf('0.5'), 0)] if m else [(mpf(0), mpf(0), 0)]
            while stack:
                p, r, dep = stack.pop(); Y = iv.mpf([p, r])
                if Phi(k, m, L, Y, Fs, W).b < 0: nb += 1; continue
                if dep > 32: return False, ("k>=1", k, m, float(p), float(r)), nb
                h = (p + r)/2; stack += [(p, h, dep+1), (h, r, dep+1)]
    return True, (ja, jb, Mt, K0), nb
if __name__ == "__main__":
    LAM0, LAM1, STEP = mpf(sys.argv[1]), mpf(sys.argv[2]), mpf(sys.argv[3])
    x = LAM0; tot = 0; t0 = time.time(); failures = []
    while x < LAM1:
        y = min(x + STEP, LAM1); ok, info, nb = cert_box(x, y); tot += nb
        if not ok:
            sub = (y - x)/8; z = x
            while z < y:
                w_ = min(z + sub, y); ok2, info2, nb2 = cert_box(z, w_); tot += nb2
                if not ok2: failures.append((float(z), float(w_), info2)); break
                z = w_
            if failures: print("FAIL", failures[-1]); break
        x = y
    print(f"lam in [{LAM0}, {LAM1}]: {'CERTIFIED' if not failures else 'NOT certified'}; {tot} boxes; {time.time()-t0:.0f}s")
