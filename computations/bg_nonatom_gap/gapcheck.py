"""Second, independent implementation: non-atom gap (prop:bg-gap) and the degree>=24 constants (prop:bg-high)."""
from indep import *
def xa(a):
    return Fr(1) if a=='L' else (Fr(1,3) if a=='C' else Fr(3,4*a+3))
def slackA(j):  # root slack of A_j: Phi_j(j/3), exact since all children messages equal
    return Phi(j,I(j)/3)
def Dm(c):
    r=I(3)/(4*c+3); return SL-r+2*KAP*(r-Q)*r**2
def Dp(c):
    r=I(3)/(4*c+3); return GAM-r+2*KAP*(r-Q)*r**2
def wc(c,x):
    X=I(x)
    if x<=Fr(1,3): return KAP*(TH-X)**2-Dm(c)*(TH-X)
    return Dp(c)*(X-TH)
# also check w_c directly equals h - l numerically at random points
import random
res={}
for c in range(2,10):
    assert Dm(c).b<0<Dp(c).a
    tau=SL-Dm(c)
    for x in [random.random() for _ in range(5)]:
        X=I(x); hl=H(X)-(BETA+tau*(X-TH)); w=wc(c,Fr(x))
        assert abs(float(hl.a)-float(w.a))<1e-12
    mc=Phi(c,I(c)/3)
    cands=[('L',mc+wc(c,Fr(1)))]+[(f'A{j}',mc+wc(c,xa(j))+slackA(j)) for j in range(1,61)]+[('A>60',mc+wc(c,xa(61)))]
    b=min(cands,key=lambda t:t[1].a)
    res[c]=b
    print(f"c={c}: m_c={fmt(mc,6)} D-={fmt(Dm(c),5)} D+={fmt(Dp(c),5)} min={float(b[1].a):.6f} at {b[0]}")
p1=Phi(1,I(3)/7); print("Phi_1(3/7) >=",float(p1.a))
# Psi convexity factor: 1-2 kappa y(3y-2q) >= 1 - 2kappa*(1/3)(1-2q)
print("convexity factor >=",float((1-2*KAP*TH*(1-2*Q)).a))
# B&B minimum of Phi_c over [0,c] for c=10..12 and a sweep 2..60
def bblow(f,lo,hi,depth=0,target=None,maxn=20000):
    import heapq
    hp=[(float(f(I(lo,hi)).a),lo,hi)]; best=float('inf'); n=0
    while n<maxn:
        v,a,b=heapq.heappop(hp)
        m=(a+b)/2; best=min(best,float(f(I(m)).b))
        if best-v<1e-7: return v,best
        for (u,t) in ((a,m),(m,b)): heapq.heappush(hp,(float(f(I(u,t)).a),u,t))
        n+=1
    return hp[0][0],best
for c in (10,11,12,13,14,20):
    lo,up=bblow(lambda X,c=c:Phi(c,X),mpf(0),mpf(c)); print(f"min Phi_{c} in [{lo:.6f},{up:.6f}]")
p=1+Q
def Qc(c): return LAM-KAP*Q**2-iv.log((1+p*c)/(c+1))-c/(4*KAP*(1+p*c)**2)
print("Q(10)",fmt(Qc(10)),"Q(13)",fmt(Qc(13)))
# prop:bg-high (root degree >= 24)
mu0=I(23)/624
import math
def gatom(a):
    if a=='L': Z=Fr(1); n=1
    elif a=='C': Z=Fr(3,2); n=2
    else: Z=Fr(3,2)**a*(1+Fr(a,3)/(a+1)); n=2*a+1
    return n*LAM-iv.log(I(Z))
for a in ['L','C',1,2,3,4,5,6,7]:
    x=xa(a); g=gatom(a); print(f"atom {a}: g={fmt(g,7)} h(x)={fmt(H(I(x)),7)} g-mu0(x-q)={fmt(g-mu0*(I(x)-Q),5)}")
gapC=I(Fr(1426,100000))-mu0**2/(4*KAP)
print("delta0-mu0^2/4k =",fmt(gapC,8)," 10/960=",10/960, " g(A4)<=1/960?", gatom(4).b<=I(1)/960)
print("min point q+mu0/2kappa =",fmt(Q+mu0/(2*KAP)))
print("benchmark floor log(26/23)-10/960 =",fmt(iv.log(I(26)/23)-I(10)/960,8),"; nonspider ceiling",fmt(iv.log(I(26)/23)-gapC,8))
