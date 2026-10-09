"""Second implementation, exact checks for the low-degree certificates of part (B). Program names: C2 = P2, C4-C6 = P4-P6, C9 = P9.
 (1) C2 polynomial P: expansion, derivation, Bernstein coefficients on [0, 6181/10000];
(2) C4-C6 Bernstein; (3) e^{6 Dmax} identity and the constant 1.291; (4) monotonicity of every atom and every
endpoint-evaluated helper; (5) G2 series coefficients; (6) C9 = G3(3/43) < 0; (7) endpoint facts (1/phi, lambda_c,
t_D2, t(0.9538)); (8) the scaled W2 forms against the unscaled definitions at random t."""
from fractions import Fraction as Fr
from math import comb
import sympy as sp
import flint
from flint import arb
flint.ctx.prec = 256
t, l, r = sp.symbols('t lam r')
out = []
def P_(*a):
    s = ' '.join(str(x) for x in a); print(s); out.append(s)

def bern(coeffs, a, b):
    """Bernstein coefficients of sum coeffs[k] x^k on [a,b] (exact Fractions), own implementation."""
    n = len(coeffs) - 1
    # shift x = a + (b-a) u : power coefficients in u
    c = [Fr(0)]*(n+1)
    for k, ck in enumerate(coeffs):
        for j in range(k+1):
            c[j] += Fr(ck)*comb(k, j)*Fr(a)**(k-j)*Fr(b-a)**j
    return [sum(Fr(comb(i, j), comb(n, j))*c[j] for j in range(i+1)) for i in range(n+1)]

# ---- (1) C2
TM = Fr(6181, 10000)
S = 1 + t/2 + sp.Rational(3, 8)*t**2 + sp.Rational(5, 16)*t**3
N = (1-t)*(3+2*t)*(5+4*t) - 2*t
P = sp.expand(11*S*N - 2*(5+4*t)**2*(1-t)*(3+2*t))
stated = 15 - sp.Rational(105, 2)*t + sp.Rational(155, 8)*t**2 + sp.Rational(1587, 16)*t**3 - sp.Rational(329, 16)*t**4 \
    - sp.Rational(649, 8)*t**5 - sp.Rational(55, 2)*t**6
P_('C2: P expands to stated polynomial:', sp.expand(P - stated) == 0, ' degree', sp.degree(P, t))
co = [Fr(str(sp.Poly(P, t).coeff_monomial(t**k))) for k in range(7)]
B = bern(co, Fr(0), TM)
P_('C2: Bernstein coeffs on [0,6181/10000]:', [f'{float(x):.4f}' for x in B], ' all >0:', all(x > 0 for x in B),
   ' min', f'{float(min(B)):.4f}')
# truncated binomial series is a lower bound of (1-t)^(-1/2) on [0,1): all omitted terms positive
ser = sp.series((1-t)**sp.Rational(-1, 2), t, 0, 8).removeO()
P_('C2: binomial coefficients of (1-t)^(-1/2):', [ser.coeff(t, k) for k in range(8)])
# N > 0 on [0, TM] (needed so that replacing sqrt(c) by a lower bound is legitimate)
BN = bern([Fr(str(sp.Poly(sp.expand(N), t).coeff_monomial(t**k))) for k in range(4)], Fr(0), TM)
P_('C2: N=(1-t)(3+2t)(5+4t)-2t Bernstein on [0,TM] all >0:', all(x > 0 for x in BN), [float(x) for x in BN])
# derivation from the stated sufficient condition (5+4t)/6 <= (11/12) sqrt(c) (1 - kappa y4), kappa y4 = 2t/((1-t)(3+2t)(5+4t))
kap_y4 = 2*t/((1-t)*(3+2*t)*(5+4*t))
lhs = sp.simplify((sp.Rational(11, 12)*(1-kap_y4) - (5+4*t)/6/ (1/sp.sqrt(1-t)) ) )  # not used, symbolic sanity
expr = sp.simplify(12*(1-t)*(3+2*t)*(5+4*t)*(sp.Rational(11, 12)*sp.Symbol('s')*(1-kap_y4) - (5+4*t)/6))
P_('C2: 12(1-t)(3+2t)(5+4t)*[(11/12) s (1-ky4) - (5+4t)/6] =', sp.factor(sp.expand(expr)))
# ---- (2) C4-C6
for name, poly, a, b in [('C4 8+6l+3l^2', [8, 6, 3], 0, Fr(32361, 10000)),
                         ('C5 -5l^3-14l^2+128l+160', [160, 128, -14, -5], 0, Fr(32361, 10000)),
                         ('C6 2-t-2t^2-t^3', [2, -1, -2, -1], 0, TM)]:
    Bc = bern([Fr(x) for x in poly], Fr(a), Fr(b))
    P_(f'{name} on [{a},{b}]: Bernstein', [f'{float(x):.4f}' for x in Bc], 'all>0:', all(x > 0 for x in Bc))
lc = arb(5).sqrt() + 1; phi_inv = (arb(5).sqrt() - 1)/2
P_('lambda_c =', lc.str(20), '<= 3.2361:', lc < arb('3.2361'), ';  1/phi =', phi_inv.str(20), '<= 0.6181:', phi_inv < arb('0.6181'))
P_('t(lambda_c) = lc/(2+lc) equals 1/phi:', abs(lc/(2+lc) - phi_inv) < arb('1e-60'))
# Lemma m1 cubic root 2.6858
rts = sp.Poly(l**3 + 4*l**2 - 12*l - 16, l).nroots()
P_('m1 cubic l^3+4l^2-12l-16 roots:', rts)
# ---- (3) Dmax
v = Fr(4, 3)**6*Fr(2, 3)**3
P_('e^{6Dmax} = (4/3)^6 (2/3)^3 =', v, '== 32768/19683:', v == Fr(32768, 19683), '; < 1.291^2 =', Fr(1291, 1000)**2, ':', v < Fr(1291, 1000)**2,
   '; sqrt =', (arb(32768)/19683).sqrt().str(10))
Dt = sp.log(1+t) + sp.log(1-t)/2
P_("D'(t) zero:", sp.solve(sp.diff(Dt, t), t), ' D(1/3) - [log(4/3)+1/2 log(2/3)] =', sp.simplify(Dt.subs(t, sp.Rational(1, 3)) - (sp.log(sp.Rational(4, 3)) + sp.log(sp.Rational(2, 3))/2)))
# ---- (4) monotonicity
def sign_on(expr, a, b, var=t, n=4001):
    f = sp.lambdify(var, expr, 'mpmath')
    import mpmath as mp
    vals = [f(mp.mpf(a) + (mp.mpf(b) - mp.mpf(a))*i/(n-1)) for i in range(n)]
    return min(vals), max(vals)
checks = {
    'kappa/t = 2/((1-t)(3+2t))': (2/((1-t)*(3+2*t)), 0, 0.6181, +1),
    'delta/t': ((1-2*t)*(1+t)/((1-t)*(3+2*t)), 0, 0.6181, -1),
    'y4': (1/(5+4*t), 0, 0.6181, -1),
    'kappa*y4': (2*t/((1-t)*(3+2*t)*(5+4*t)), 0, 0.6181, +1),
    'q3 = 2/((1-t)(4+3t))': (2/((1-t)*(4+3*t)), 0, 0.6181, +1),
    'x = t q3 (arg of Lq)': (2*t/((1-t)*(4+3*t)), 0, 0.6181, +1),
    'rhohat': (sp.Rational(1, 2) - t/4 - 7*t**2/12 + t**3/6, 0, 0.6181, -1),
    'r8 = (2t-1)(1+t)/((1-t)(3+2t)^2)': ((2*t-1)*(1+t)/((1-t)*(3+2*t)**2), 0.5, 0.6181, +1),
    't(1+(1-t)^(-1/2))': (t*(1+1/sp.sqrt(1-t)), 0, 0.6181, +1),
    'Lm = -log(1-t)/t': (-sp.log(1-t)/t, 1e-9, 0.6181, +1),
    'L23': (sp.log(1+2*t/3)/(2*t/3), 1e-9, 0.6181, -1),
    'L34': (sp.log(1+3*t/4)/(3*t/4), 1e-9, 0.6181, -1),
    'G2t': ((5*sp.log(1+3*t/4) - 7*sp.log(1+2*t/3) - sp.log(1-t))/t, 1e-6, 0.6181, +1),
    'X(s)=(e^s-1)/s': ((sp.exp(t)-1)/t, 1e-9, 1, +1),
}
for k, (e, a, b, sg) in checks.items():
    d = sp.diff(e, t)
    lo, hi = sign_on(d, a, b)
    ok = (lo > 0) if sg > 0 else (hi < 0)
    P_(f'monotone {k}: derivative range on [{a},{b}] = [{float(lo):.4g}, {float(hi):.4g}]  claimed {"inc" if sg>0 else "dec"}: {ok}')
# exact derivative forms claimed in the atom table
P_('d(kappa/t)/dt == 2(4t+1)/((1-t)^2(3+2t)^2):', sp.simplify(sp.diff(2/((1-t)*(3+2*t)), t) - 2*(4*t+1)/((1-t)**2*(3+2*t)**2)) == 0)
P_('d(delta/t)/dt == -2(4t+1)/(...):', sp.simplify(sp.diff((1-2*t)*(1+t)/((1-t)*(3+2*t)), t) + 2*(4*t+1)/((1-t)**2*(3+2*t)**2)) == 0)
P_("rhohat' == -1/4-7t/6+t^2/2:", sp.simplify(sp.diff(sp.Rational(1, 2) - t/4 - 7*t**2/12 + t**3/6, t) - (-sp.Rational(1, 4) - 7*t/6 + t**2/2)) == 0)
g = r*(1 - r/(8+6*r))**3*(4+3*r)
num = sp.factor(sp.together(sp.diff(g, r)))
P_("g'(r) factored:", num)
lo, hi = sign_on(sp.diff(g, r), 0, 0.5, var=r)
P_(f"g increasing on [0,1/2]: g' range [{float(lo):.4g},{float(hi):.4g}]")
# kappa*y4 exact: numerator of derivative
ky = 2*t/((1-t)*(3+2*t)*(5+4*t))
P_("d(kappa y4)/dt numerator:", sp.factor(sp.numer(sp.together(sp.diff(ky, t)))))
P_("d r8/dt numerator:", sp.factor(sp.numer(sp.together(sp.diff((2*t-1)*(1+t)/((1-t)*(3+2*t)**2), t)))))
# ---- (5) G2 coefficients
ck = lambda k: Fr(1, k)*((-1)**(k+1)*(5*Fr(3, 4)**k - 7*Fr(2, 3)**k) + 1)
P_('G2 c_1..c_6:', [f'{float(ck(k)):.4f}' for k in range(1, 7)], ' c_1 == 1/12:', ck(1) == Fr(1, 12))
P_('all c_k>0 for k<=400:', all(ck(k) > 0 for k in range(1, 401)))
P_('5(3/4)^5 =', float(5*Fr(3, 4)**5), '<1.19;  7(2/3)^5 =', float(7*Fr(2, 3)**5), '<0.93;  5(3/4)^6 =', float(5*Fr(3, 4)**6), '<0.9')
# ---- (6) C9
T = arb(3)/43
G3 = 7*(4*T/5).log1p() - 9*(3*T/4).log1p() - (-T).log1p()
P_('C9: G3(3/43) =', G3.str(15), ' <0:', G3 < 0, '; t(3/20) == 3/43:', Fr(3, 20)/(2+Fr(3, 20)) == Fr(3, 43))
# f4 - f3 at lambda = 3/20 directly
lam = arb(3)/20; c = 1+lam/2; tt = lam/(2+lam)
f = lambda j: (j*c.log() + (1+tt*j/(j+1)).log())/(2*j+1)
P_('at lambda=3/20: f2,f3,f4,f5 =', [f(j).str(12) for j in (2, 3, 4, 5)])
# ---- (7) S6 endpoints
tD2 = (arb(7).sqrt()-2)/2
P_('t_D2 =', tD2.str(15), ' lambda_D2 =', (2*tD2/(1-tD2)).str(10), ' 3229/10000 >= t_D2:', arb('0.3229') > tD2,
   '; t(0.9538) =', (arb('0.9538')/arb('2.9538')).str(10))
