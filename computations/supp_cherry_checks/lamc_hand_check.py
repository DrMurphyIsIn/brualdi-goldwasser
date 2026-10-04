"""Checks of the anchor (prop:lam-anchor; rem:lam-anchor-check): hand proof of the ceiling at the single point lam_c = 1+sqrt5) -- verification of every identity and constant.
Proof (prop:lam-anchor): pooled hinge witness U(y) = -kap (y - y_ch)^+, kap = phi log phi, F* = L = log phi.
This script checks:
 (1) exact identities (sympy):  1+lam/2 = phi^2, 1+lam = phi^3, 2+lam = 2 phi^2, y_ch = 1/(2 phi^2), 1 + lam y_ch = phi,
     1/2 - y_ch = 1/(2 phi), 2 phi + 1 = phi^3, 1 + lam m y_ch/(m+1) = (m phi + 1)/(m+1).
 (2) rigorous constants (arb): kap > lam/phi^3 (region-A monotonicity for m >= 2); kap < 2 (region-B monotonicity);
     k = 2: phi^3 > 1 + 2 lam/3; the m = 2 value; the m = 1 maximum (critical point in closed form, value < 0);
     r_m < L for every arm (needed only for the remark that the cherry is the unique equality case).
 (3) brute force: for every NON-LEAF planted branch with n <= NMAX (leaves are exact, counted by k), l(b) <= U(y_b) at lam_c (float, exact cavity), and l(b) = 0 only
     for the cherry."""
import sys, math
import sympy as sp
from flint import arb
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14
# ---------- (1) exact identities ----------
s5 = sp.sqrt(5); phi = (1 + s5)/2; lam = 1 + s5; ych = 1/(2 + lam); m = sp.symbols('m', positive=True)
ids = {
    '1+lam/2 = phi^2': 1 + lam/2 - phi**2, '1+lam = phi^3': 1 + lam - phi**3, '2+lam = 2phi^2': 2 + lam - 2*phi**2,
    '1+lam*ych = phi': 1 + lam*ych - phi, '1/2-ych = 1/(2phi)': sp.Rational(1, 2) - ych - 1/(2*phi),
    '2phi+1 = phi^3': 2*phi + 1 - phi**3, '1+lam m ych/(m+1) = (m phi+1)/(m+1)': 1 + lam*m*ych/(m+1) - (m*phi + 1)/(m+1),
}
for k, v in ids.items():
    assert sp.simplify(sp.nsimplify(v)) == 0, k
print("(1) exact identities: all", len(ids), "verified")
# ---------- (2) rigorous constants ----------
P = (1 + arb(5).sqrt())/2; LAM = 1 + arb(5).sqrt(); L = P.log(); KAP = P*L; YCH = 1/(2 + LAM)
def neg(x, name):
    assert x < 0, (name, x); print(f"   {name}: {x.mid().str(8)} +/- {x.rad().str(3)}  < 0")
print("(2) rigorous constants (arb):")
neg(LAM/P**3 - KAP, "region A, m >= 2: lam/phi^3 - kap")
neg(KAP - 2, "region B: kap - 2")
neg(1 + 2*LAM/3 - P**3, "k = 2: 1 + 2lam/3 - phi^3")
neg((2*P + 1)/(3*P) - 1, "m = 2 kink, log argument (2phi+1)/(3phi) - 1")
v2 = ((P**2)/3).log() + L*(1/P**2 - 1/(2*P))
neg(v2, "m = 2 value log(phi^2/3) + log(phi)(phi^-2 - (2phi)^-1)")
# m = 1, region A (t >= y_ch, s = 2 + lam t in [phi^2, 2 + lam/2]): Psi = -kap(t - ych) + log(s/2) - L + kap(1/s - ych);
# Psi' = (-kap s^2 + lam s - kap lam)/s^2 has roots s = (lam +- sqrt(lam^2 - 4 kap^2 lam))/(2 kap); the larger is the unique max.
disc = LAM**2 - 4*KAP**2*LAM; assert disc > 0
s_star = (LAM + disc.sqrt())/(2*KAP); s_lo = (LAM - disc.sqrt())/(2*KAP)
assert s_lo < P**2 and P**2 < s_star and s_star < 2 + LAM/2, "critical point placement"
t_star = (s_star - 2)/LAM
v1 = -KAP*(t_star - YCH) + (s_star/2).log() - L + KAP*(1/s_star - YCH)
print(f"   m = 1: critical point s* = {s_star.mid().str(8)}, t* = {t_star.mid().str(8)} (in (y_ch, 1/2)); the smaller root {s_lo.mid().str(6)} < phi^2")
neg(v1, "m = 1 maximum value")
# arms strictly below the cherry rate at lam_c (r_j - L = (h_j - L)/(2j+1), h_j - L <= g - b/(j+1), g(lam_c) = 0):
worst = max(((j*(1 + LAM/2).log() + (1 + j*LAM/((j+1)*(2+LAM))).log())/(2*j+1) - L) for j in range(1, 2001))
neg(worst, "max_{j <= 2000} (r_j - L)  [all j: h_j - L <= -b/(j+1) < 0, see proof]")
# ---------- (3) brute force ----------
_src = open('small_lambda_monotone.py').read(); exec(_src[:_src.index('worst = {}\nS =')])
lamf = 1 + 5**.5; phif = (1 + 5**.5)/2; Lf = math.log(phif); kapf = phif*Lf; ychf = 1/(2 + lamf)
def walk(t):
    d = len(t) + 1; l = 0.0; R = 0.0
    for c in t:
        lc, yc = walk(c); l += lc; R += yc
    return l + math.log1p(lamf*R/d) - Lf, 1/(d + lamf*R)
worst, zeros, cnt = -9, [], 0
for n in range(1, NMAX+1):
    for t in trees(n):
        if n == 1: continue                    # leaves are exact in the pooled induction (counted by k), not bound by U
        l, y = walk(t); cnt += 1
        U = -kapf*max(0.0, y - ychf)
        worst = max(worst, l - U)
        if abs(l) < 1e-12: zeros.append(t)
print(f"(3) brute force 2 <= n <= {NMAX}: {cnt} non-leaf branches; max (l - U(y)) = {worst:+.3e} (must be <= 0); l = 0 exactly for: {zeros}")
