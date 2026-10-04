"""A hand-checkable (polynomial) proof of (S6) on [lam_a, lam_D2] via Taylor bounds with remainders.

(S6), lam <= 2:  Psi = eps (3/2 + delta/u) - D(2) >= 0, increasing in F, so take F = f_3 (any lower bound of f* works).
With F = f_3: eps_3 = 2 D(3)/7 and Psi = (3/7) L32 - (4/7) D(2) + (2/7) D(3) delta/u_3, where
   D(j) = log(1 + t j/(j+1)) + log(1-t)/2,  L32 = D(3) - D(2) = log((1+3t/4)/(1+2t/3)),
   u_3 = 1 + t - exp(f_3),  delta = t(1-2t)(1+t)/((1-t)(3+2t)).
So Psi >= 0  <=>  3 L32 + 2 D(3) delta / u_3 >= 4 D(2).
Rigorous polynomial bounds for 0 <= t <= 1/3 (all series alternate or have positive terms):
   log(1+x) >= sum_{k=1}^{2n} (-1)^{k+1} x^k/k ,  log(1+x) <= sum_{k=1}^{2n+1} (-1)^{k+1} x^k/k   (0 <= x <= 1)
   -log(1-t) >= sum_{k=1}^{N} t^k/k ,  -log(1-t) <= sum_{k=1}^{N} t^k/k + t^{N+1}/((N+1)(1-t))
   exp(x) >= sum_{k=0}^{K} x^k/k!   (x >= 0)
   L32 = log(1 + x) with x = (t/12)/(1 + 2t/3) (exact), bounded below by the even partial sum.
Then  3 L32_lo + 2 D3_lo * delta / u3_hi - 4 D2_hi  is a rational function of t; we certify it is > 0 on [t_a, t_D2]
by exact Sturm root counting of its numerator (denominators are checked positive).
Also D(3) > 0 on the interval is certified (needed to use D3_lo * delta/u3_hi as a lower bound).
"""
import sys
import sympy as sp

t = sp.symbols('t', positive=True)
NORD = int(sys.argv[2]) if len(sys.argv) > 2 else 5


def log1p_lo(x, n=NORD):   # even number of terms (lower bound), 0 <= x <= 1
    n2 = n if n % 2 == 0 else n + 1
    return sum((-1) ** (k + 1) * x ** k / k for k in range(1, n2 + 1))


def log1p_hi(x, n=NORD):   # odd number of terms (upper bound)
    n2 = n if n % 2 == 1 else n + 1
    return sum((-1) ** (k + 1) * x ** k / k for k in range(1, n2 + 1))


def mlog1m_lo(x, n=NORD):  # -log(1-x) lower bound
    return sum(x ** k / k for k in range(1, n + 1))


def mlog1m_hi(x, n=NORD):  # -log(1-x) upper bound
    return sum(x ** k / k for k in range(1, n + 1)) + x ** (n + 1) / ((n + 1) * (1 - x))


def exp_lo(x, K=4):
    return sum(x ** k / sp.factorial(k) for k in range(0, K + 1))


half = sp.Rational(1, 2)
# D(2) upper bound: log(1+2t/3) upper, (1/2) log(1-t) = -(1/2)(-log(1-t)) upper uses -log lower
D2_hi = log1p_hi(2 * t / 3) - half * mlog1m_lo(t)
# D(3) lower bound
D3_lo = log1p_lo(3 * t / 4) - half * mlog1m_hi(t)
# L32 lower bound: log(1+x), x = (t/12)/(1+2t/3)
x32 = (t / 12) / (1 + 2 * t / 3)
L32_lo = log1p_lo(x32)
# f_3 lower bound and u_3 upper bound
f3_lo = (3 * mlog1m_lo(t) + log1p_lo(3 * t / 4)) / 7
u3_hi = 1 + t - exp_lo(f3_lo)
delta = t * (1 - 2 * t) * (1 + t) / ((1 - t) * (3 + 2 * t))

lam_a = sp.Rational(sys.argv[1]) if len(sys.argv) > 1 else sp.Rational(641, 5000)
t_a = lam_a / (2 + lam_a)
t_b = sp.Rational(3229, 10000)   # > t_D2 = (sqrt7 - 2)/2 = 0.32287...
assert t_b > (sp.sqrt(7) - 2) / 2


from cert import certify


def pos(expr, name):
    return certify(expr, t, t_a, t_b, name)


ok = True
ok &= pos(D3_lo, "D(3) > 0 (lower bound positive)")
ok &= pos(u3_hi, "u_3 upper bound > 0")
target = 3 * L32_lo + 2 * D3_lo * delta / u3_hi - 4 * D2_hi
ok &= pos(target, f"(S6) on lam in [{lam_a}, 0.9538]")
# report the margin profile
for tv in [t_a, (t_a + t_b) / 2, t_b]:
    print(f"   t={float(tv):.4f}: lower bound {float(target.subs(t, tv)):+.3e}")
print("RESULT:", "PROVED" if ok else "NOT PROVED", f"(Taylor order {NORD})")
