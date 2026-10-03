"""Strict comparison certificates for the cherry-free candidates.  For each residue class s and side,
P(x) = winner-minus-loser cleared quadratic (as in R3Cert.BGSpiderCandBase.P); we need P(x) > 0 on the admissible
range of x.  Unbounded ranges: coefficients of P(L + t) all >= 0 with constant > 0.  Bounded ranges [L, U]:
Bernstein coefficients of P on [L, U] all > 0."""
from fractions import Fraction as Q
G4,G5,G6=Q(513,80),Q(621,64),Q(6561,448); B4,B5,B6=Q(3,19),Q(3,23),Q(1,9)
def Pcoef(c,a,d,k1,w4,w6,k2):
    # P(x) = A2*(D2x + R2x)*D1x - A1*(D1x+R1x)*D2x with D1x = c+a+d+k1+x etc.  return [p0,p1,p2] in x
    A2=G4**w4*G5**k2*G6**w6; A1=Q(3,2)**c*G4**a*G5**k1*G6**d
    # linear forms u0+u1 x
    D1=(c+a+d+k1,1); R1=(Q(c,3)+a*B4+d*B6+k1*B5,B5); D2=(w4+w6+k2,1); R2=(w4*B4+w6*B6+k2*B5,B5)
    def mul(p,q): return (p[0]*q[0], p[0]*q[1]+p[1]*q[0], p[1]*q[1])
    def add(p,q): return (p[0]+q[0],p[1]+q[1])
    t1=mul(add(D2,R2),D1); t2=mul(add(D1,R1),D2)
    return [A2*t1[i]-A1*t2[i] for i in range(3)]
def shift(p,L): # p(L+t)
    p0,p1,p2=p; return [p0+p1*L+p2*L*L, p1+2*p2*L, p2]
def bern(p,L,U): # P(L+t), t in [0,T]: b0 (T-t)^2 + b1 t (T-t) + b2 t^2, with T = U-L
    q=shift(p,L); T=U-L; c0,c1,c2=q
    return [c0/(T*T)*T*T, None, None] if T==0 else [c0, (2*c0+c1*T)/T*1, c0+c1*T+c2*T*T]
cases=[]
for s in range(1,11):
    # m range: n = 1 + 11 m + 13 s >= 492  ->  m >= ceil((491-13s)/11)
    mmin=-(-(491-13*s)//11)
    if s<=2 or s>=5 or s in (3,4):
        # side "Y wins": s in {1,2}, s=3 n>=733, s=4 n>=2330 : loser X (base x = m+2s-9)
        if s in (1,2,3,4):
            m_lo = mmin if s<=2 else (63 if s==3 else 207)
            # check thresholds: n=1+11m+13s
            L = m_lo+2*s-9
            cases.append(dict(s=s,win='Y',c=0,a=11-s,d=0,k1=0,w4=0,w6=s,k2=9-2*s,L=L,U=None))
        if s>=3:
            # side "X wins": s>=5 any m; s=3 n<=722 (m<=62); s=4 n<=2319 (m<=206). loser Y.
            if s>=5:
                cases.append(dict(s=s,win='X',c=0,a=0,d=s,k1=0,w4=11-s,w6=0,k2=2*s-9,L=mmin,U=None))
            else:
                m_hi = 62 if s==3 else 206
                L=mmin+2*s-9; U=m_hi+2*s-9
                cases.append(dict(s=s,win='X',c=0,a=0,d=s,k1=9-2*s,w4=11-s,w6=0,k2=0,L=L,U=U))
ok=True
for cs in cases:
    p=Pcoef(cs['c'],cs['a'],cs['d'],cs['k1'],cs['w4'],cs['w6'],cs['k2'])
    if cs['U'] is None:
        q=shift(p,cs['L']); good = q[0]>0 and q[1]>=0 and q[2]>=0; kind='mono'
    else:
        T=cs['U']-cs['L']; q0,q1,q2=shift(p,cs['L'])
        b0=q0; b1=2*q0+q1*T; b2=q0+q1*T+q2*T*T  # P = b0 (T-t)^2/T^2 + b1 t(T-t)/T^2 + b2 t^2/T^2
        q=[b0,b1,b2]; good = all(v>0 for v in q); kind='bern'
    ok &= good
    print(f"s={cs['s']} win={cs['win']} L={cs['L']} U={cs['U']} {kind} signs={[ '+' if v>0 else ('0' if v==0 else '-') for v in q]} {'OK' if good else 'FAIL'}")
print("ALL OK" if ok else "SOME FAIL")

def fr(q):
    q=Q(q); return f"({q.numerator} / {q.denominator} : ℚ)" if q.denominator!=1 else f"({q.numerator} : ℚ)"
out=[]
for cs in cases:
    s,win=cs['s'],cs['win']; c,a,d,k1,w4,w6,k2,L,U=[cs[k] for k in ('c','a','d','k1','w4','w6','k2','L','U')]
    p=Pcoef(c,a,d,k1,w4,w6,k2); name=f"strict_cert_{s}_{win}"
    hyp=f"(m : ℕ) (hm : {L} ≤ m)" + (f" (hmU : m ≤ {U})" if U is not None else "")
    lines=[f"theorem {name} {hyp} :",
           f"    Φ {c} {a} (m + {k1}) {d} < Φ 0 {w4} (m + {k2}) {w6} := by",
           f"  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)"]
    if U is None:
        q=shift(p,L)
        rhs=f"{fr(q[0])} + {fr(q[1])} * t + {fr(q[2])} * t ^ 2"
        tail=f"  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)"
    else:
        T=U-L; q0,q1,q2=shift(p,L); b0=q0; b1=2*q0+q1*T; b2=q0+q1*T+q2*T*T
        rhs=f"{fr(b0/(T*T))} * ({T} - t) ^ 2 + {fr(b1/(T*T))} * (t * ({T} - t)) + {fr(b2/(T*T))} * t ^ 2"
        tail=(f"  have hmU' : (m : ℚ) ≤ ({U} : ℚ) := by exact_mod_cast hmU\n"
              f"  exact bern_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)")
    lines += [f"  have key : ∀ t : ℚ, P {c} {a} {d} {k1} {w4} {w6} {k2} ({L} + t) =",
              f"      {rhs} := by",
              f"    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring",
              f"  have hm' : ({L} : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm",
              f"  have e := key ((m : ℚ) - {L})",
              f"  rw [show ({L} : ℚ) + ((m : ℚ) - {L}) = m by ring] at e",
              f"  rw [e]", tail, ""]
    out.append("\n".join(lines))
open('BGUnique/StrictCerts.body','w').write("\n".join(out))
print("wrote", len(out), "certs")
