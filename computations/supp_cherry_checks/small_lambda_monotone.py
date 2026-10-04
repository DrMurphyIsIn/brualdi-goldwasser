"""Small lam: is l_s(b) nonincreasing in s on (0, s1], i.e. E_s[#dimers] = s T'(s)/T(s) <= n s F*'(s), with F* = r_3 (best arm A3 for
s < 0.4305)?  Equality for A3 at every s.  At s -> 0 this is the planted Randic bound R_-1(b) <= (15/56) n."""
import math
exec(open('monotone_ratio.py').read().split('worst = {}')[0])
def r3(s):  return (3*math.log1p(s/2) + math.log1p(3*s/(4*(2+s))))/7
def r3p(s):
    return (3*(0.5/(1+s/2)) + ((3/4)*2/(2+s)**2)/(1 + 3*s/(4*(2+s))))/7
worst = {}
S = [1e-4, 0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.43]
first = (-9, None)
for n in range(1, 17):
    for t in trees(n):
        T = poly(t)[1]
        R = T[1] if len(T) > 1 else 0.0              # first coefficient = planted R_-1
        fo = R - 15*n/56
        if fo > first[0] + 1e-12: first = (fo, n, t)
        for s in S:
            val = sum(c*s**k for k, c in enumerate(T)); der = sum(k*c*s**(k-1) for k, c in enumerate(T) if k)
            g = s*der/val - n*s*r3p(s)
            if g > worst.get(s, (-9,))[0]: worst[s] = (g, n, t)
print("first order: max_b (R_-1(b) - 15n/56) over n<=16 =", f"{first[0]:+.4e}", "at n =", first[1], "(A3 has n = 7)")
for s in S:
    g, n, t = worst[s]; print(f"s={s:<7}: max_b (E[dimers] - n s F*'(s)) = {g:+.3e}  (n={n}){'   <-- equality branch is A3' if abs(g) < 1e-12 and n == 7 else ''}")
