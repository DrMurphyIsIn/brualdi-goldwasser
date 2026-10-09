"""Second, independent implementation of the rate potential at lambda = 1 (all 253 one-variable inequalities Phi^H_c>=0 on [0,c]), H convexity, Psi_k."""
import sys, time
from indep import *
iv.prec=110
ETAS={1:Fr(2791,2500000),2:Fr(2791,2500000),3:Fr(2791,2500000),4:Fr(2791,2500000),5:Fr(2791,2500000),
6:Fr(9387,10000000),7:Fr(4183,5000000),8:Fr(7507,10000000),9:Fr(1701,2500000),10:Fr(311,500000),
11:Fr(179,312500),12:Fr(5309,10000000),13:Fr(2473,5000000),14:Fr(463,1000000),15:Fr(34,78125),
16:Fr(2053,5000000),17:Fr(1943,5000000),18:Fr(461,1250000),19:Fr(351,1000000),20:Fr(837,2500000),
21:Fr(1,3125),22:Fr(613,2000000)}
def Hq(Y,E): return KAP*sq(Y-Q)-E*(11-AW*(Y-Q))
def Hl(Y,E): return BETA+GAM*(Y-TH)-E*(2-I(3)/2*(Y-TH))
def dHq(Y,E): return 2*KAP*(Y-Q)+E*AW
def dHl(Y,E): return GAM+E*I(3)/2
def Henc(X,E):
    r=None
    for k,Y in split(X):
        v=(Hq if k=='q' else Hl)(Y,E); r=v if r is None else hull(r,v)
    return r
def Fenc(c,S,E):
    r=1/(c+1+S)
    return LAM-E+c*Henc(S/c,E)-iv.log(1+S/(c+1))-Henc(r,E)
def dF(c,S,E,piece):
    r=1/(c+1+S)
    dHy=(dHq if piece=='q' else dHl)(S/c,E)
    dHr=dHl(r,E) if c==1 else dHq(r,E)   # c=1: r in [1/3,1/2]; c>=2: r<=1/3
    return dHy-r+dHr*r**2
Z5=I(5)/3
def prove(c,E,a,b,depth=0):
    X=iv.mpf([a,b])
    if Fenc(c,X,E).a>=0: return 1
    if depth>=12:
        if c==1 and b==1:
            if dF(1,X,E,'l').b<=0 and a>=mpf(1)/2: return 1
        if c==5 and a<=Z5.b and b>=Z5.a:
            okL = a>Z5.b or dF(5,iv.mpf([a,Z5.b]),E,'q').b<=0
            okR = b<Z5.a or dF(5,iv.mpf([Z5.a,b]),E,'l').a>=0
            if okL and okR: return 1
    if depth>70: raise Exception(f"FAIL c={c} [{a},{b}]")
    m=(a+b)/2
    return prove(c,E,a,m,depth+1)+prove(c,E,m,b,depth+1)
def check(C,c):
    return prove(c,I(ETAS[C]),mpf(0),mpf(c))
def Psi(k,E):
    # f(y)=log(1+y)-k H(y) is concave; rigorous upper bound by best-first subdivision
    import heapq
    f=lambda Y: iv.log(1+Y)-k*Henc(Y,E)
    hp=[(-float(f(iv.mpf([0,1])).b),mpf(0),mpf(1))]; best=-1e9
    for _ in range(4000):
        v,a,b=heapq.heappop(hp); m=(a+b)/2
        best=max(best,float(f(I(m)).a))
        if -v-best<1e-8: heapq.heappush(hp,(v,a,b)); break
        for u,t in ((a,m),(m,b)): heapq.heappush(hp,(-float(f(iv.mpf([u,t])).b),u,t))
    return -min(x[0] for x in hp)
if __name__=="__main__":
    t=time.time(); cnt=0; boxes=0
    for C in range(1,23):
        for c in range(1,C+1):
            boxes+=check(C,c); cnt+=1
        print(f"C={C} all c<=C ok ({time.time()-t:.0f}s)",flush=True)
    print("one-variable checks passed:",cnt,"boxes:",boxes)
    for C,e in ETAS.items():
        assert (I(e)*(AW-I(3)/2)).b<(GAM-SL).a
    print("H convex for all C")
    # stated values of Psi_k (upper bounds, rounded up)
    claimed={2:0.29989,3:0.27126,4:0.26579,5:0.26031,6:0.25484,7:0.24772,8:0.24276,9:0.23873,10:0.23543,11:0.23269,12:0.23036,
             13:0.22838,14:0.22665,15:0.22514,16:0.22381,17:0.22263,18:0.22158,19:0.22062,20:0.21977,21:0.21898,22:0.21826,23:0.21761}
    import json; out={}
    for k in range(2,24):
        u=Psi(k,I(ETAS[k-1])); out[k]=u
        print(f"Psi_{k} <= {u:.7f}   stated {claimed[k]}  {'OK' if u<=claimed[k] else 'STATED VALUE TOO SMALL (rounded down)'}")
    json.dump(out,open('psi_indep.json','w'))
