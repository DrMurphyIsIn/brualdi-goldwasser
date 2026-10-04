"""Independent interval certification (mpmath.iv, written separately; imports none of the first implementation)."""
import os; os.environ["OMP_NUM_THREADS"]="1"
from mpmath import iv, mpf, mp
from fractions import Fraction as Fr
iv.prec=200; mp.prec=200
def I(a,b=None):
    if b is None:
        if isinstance(a,Fr): return iv.mpf(a.numerator)/a.denominator
        return iv.mpf(a)
    return iv.mpf([a,b])
LAM=iv.log(I(621)/64)/11
BETA=2*LAM-iv.log(I(3)/2)
Q=I(3)/23; TH=I(1)/3
KAP=BETA/(TH-Q)**2
GAM=I(3)/2*(LAM-BETA)
SL=2*KAP*(TH-Q)          # left slope at 1/3
def hull(a,b): return iv.mpf([min(a.a,b.a),max(a.b,b.b)])
def sq(D):
    if D.a>=0 or D.b<=0: return D*D
    return iv.mpf([0,max(-D.a,D.b)**2])
def split(X):
    out=[]
    if X.a<=TH.b: out.append(('q',iv.mpf([X.a,min(X.b,TH.b)])))
    if X.b>=TH.a: out.append(('l',iv.mpf([max(X.a,TH.a),X.b])))
    return out
AW=I(621)/14
def H(X,eta=0):
    E=I(Fr(eta)) if not isinstance(eta,iv.mpf) else eta
    r=None
    for k,Y in split(X):
        v= KAP*sq(Y-Q)-E*(11-AW*(Y-Q)) if k=='q' else BETA+GAM*(Y-TH)-E*(2-I(3)/2*(Y-TH))
        r=v if r is None else hull(r,v)
    return r
def Phi(c,S,eta=0):
    E=I(Fr(eta))
    return LAM-E+c*H(S/c,eta)-iv.log(1+S/(c+1))-H(1/(c+1+S),eta)
def fmt(x,n=7): return f"[{float(x.a):.{n}g}, {float(x.b):.{n}g}]"
if __name__=="__main__":
    print("lam",fmt(LAM,10),"beta",fmt(BETA,10),"kappa",fmt(KAP,8),"gamma",fmt(GAM,8),"s",fmt(SL,8))
    print("gamma-s",fmt(GAM-SL))
    print("h(1)-lam",fmt(BETA+GAM*(1-TH)-LAM))
    print("Phi_1(1) (should contain 0)",fmt(Phi(1,I(1))))
    print("Phi_5(5/3) (should contain 0)",fmt(Phi(5,I(5)/3)))
