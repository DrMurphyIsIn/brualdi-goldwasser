from fractions import Fraction as Fr
al=lambda j:Fr(4*j+3,3*(j+1)); g=lambda j:Fr(3,2)**j*al(j); b=lambda j:Fr(3,4*j+3)
G4,G5,G6=g(4),g(5),g(6); B4,B5,B6=b(4),b(5),b(6)
print("G4,G5,G6",G4,G5,G6,"B",B4,B5,B6)
lam=G4*G6/G5**2; K0=G5**9/G4**11
print("lambda=",lam,float(lam)," K0=",K0,float(K0))
K={s:K0*lam**s for s in range(0,11)}
for s in range(1,11):
    assert K[s]==G6**s*G5**(9-2*s)/G4**(11-s)
    print(" K_%d = %s = %.10f"%(s,K[s],float(K[s])))
assert K[4]>1>K[5]
def Phi(c,a,bb,d):
    return Fr(3,2)**c*G4**a*G5**bb*G6**d*(1+(Fr(c,3)+a*B4+bb*B5+d*B6)/(c+a+bb+d))
def q(s,D):
    u=Fr(12*(11-s),437); v=Fr(4*s,207); k=K[s]
    return (k-1)*Fr(26,23)*D*(D+2)-k*v*(D+2)-u*D
for s in range(1,5):
    print(" s=%d: q(0)=%.4g lead=(K-1)26/23=%s"%(s,float(q(s,0)),(K[s]-1)*Fr(26,23)))
for s,Ds in [(1,[27,28,42,45]),(2,[38,39,42,45]),(3,[65,66]),(4,[210,211])]:
    for D in Ds:
        print("   q_%d(%d) = %.6g"%(s,D,float(q(s,D))), " exact sign", (q(s,D)>0)-(q(s,D)<0), " n=",11*D+2*s+1)
# cross-check race sign against direct Phi comparison for all D up to 3000
for s in range(1,11):
    for D in range(max(s,9-2*s+s) if s<5 else s, 3000):
        a=D-s  # 5-arms in A6 candidate
        if a<0: continue
        aY=a+2*s-9
        if aY<0: continue
        X=Phi(0,0,a,s); Y=Phi(0,11-s,aY,0)
        assert 11*D+2*s+1==1+13*s+11*a==1+9*(11-s)+11*aY
        sgn=(X>Y)-(X<Y)
        if s>=5: assert sgn==-1
        else: assert sgn==((q(s,D)>0)-(q(s,D)<0)), (s,D)
print("race sign == q sign for all D<3000, all s; s>=5: A4 always wins")
# margins at switches
for n,s in [(722,3),(733,3),(2319,4),(2330,4)]:
    D=(n-1-2*s)//11; a=D-s
    X=Phi(0,0,a,s); Y=Phi(0,11-s,a+2*s-9,0)
    print(" n=%d: F(A4 version)/F(A6 version)-1 = %.3e"%(n,float(Y/X-1)))
# absorption thresholds
for j,thr in [(4,24),(5,34)]:
    for D0 in range(0,200):
        ok=True
        for R0 in (Fr(D0,9),Fr(D0,3)):
            val=3*D0**2+D0*(3*R0-4*j*j-11*j-6)+R0*(12*j*j+33*j+24)-4*j*j-2*j
            ok&= val>0
        if D0>=thr: assert ok
    print(" absorption P+A%d->A%d holds for all D0>=%d, R0 in [D0/9,D0/3]"%(j,j+1,thr))
