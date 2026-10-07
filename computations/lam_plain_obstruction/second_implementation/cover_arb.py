"""Independent rigorous cover of lam in [79/20, 10^6] for the two-point obstruction
   mu(lam;a,b) = L_b + (1-b)/(a - y2(a)) (L_a - F) - 2F > 0,  F = log(1+lam/2)/2.
python-flint/Arb, lam enclosed as a ball built from EXACT rational endpoints; own cell subdivision
(geometric initial grid, per-cell (a,b) from a float optimiser, rounded to rationals); bisection on failure."""
import os; os.environ["OMP_NUM_THREADS"]="1"
from fractions import Fraction as Fr
from flint import arb, fmpq, ctx
import numpy as np
ctx.prec = 256
def A(q): q=Fr(q); return arb(fmpq(q.numerator, q.denominator))
def lam_ball(p,q):
    lo, hi = A(p), A(q)
    return lo.union(hi)
def mu(lam, a, b):
    a, b = A(a), A(b)
    F = (1+lam/2).log()/2
    y2 = 1/(2+lam*a)
    assert (a-y2) > 0 and b < 1 and b > a
    return (1+lam*b/2).log() + (1-b)/(a-y2)*((1+lam*a/2).log()-F) - 2*F
def muf(lam,a,b):
    F=0.5*np.log1p(lam/2); y2=1/(2+lam*a)
    return np.log1p(lam*b/2)+(1-b)/(a-y2)*(np.log1p(lam*a/2)-F)-2*F
def pick(lam):
    # choose a maximizing S(a) on a grid, then b maximizing mu on a grid (float, untrusted)
    F=0.5*np.log1p(lam/2)
    aa=np.linspace(1e-4,0.999,20000); y2=1/(2+lam*aa); ok=aa>y2
    S=np.where(ok,(np.log1p(lam*aa/2)-F)/np.where(ok,aa-y2,1),-1e9)
    a=aa[np.argmax(S)]
    bb=np.linspace(a+1e-6,1-1e-7,20000); m=muf(lam,a,bb); b=bb[np.argmax(m)]
    fa=Fr(a).limit_denominator(10**6); fb=Fr(b).limit_denominator(10**7)
    return fa,fb
def cover(lo,hi,ncell0=400):
    # geometric initial grid in rational arithmetic
    r=(hi/lo)**(1.0/ncell0)
    pts=[Fr(lo)]+[Fr(lo*r**k).limit_denominator(10**6) for k in range(1,ncell0)]+[Fr(hi)]
    pts=sorted(set(pts)); assert pts[0]==Fr(lo) and pts[-1]==Fr(hi)
    stack=[(pts[i],pts[i+1]) for i in range(len(pts)-1)]
    done=0; worst=None; smallest=None
    while stack:
        p,q=stack.pop()
        lam=lam_ball(p,q)
        a,b=pick(float((p+q)/2))
        try: m=mu(lam,a,b); good = m>0
        except AssertionError: good=False
        if good:
            done+=1
            lb=float(m.lower())
            if worst is None or lb<worst[0]: worst=(lb,float(p),float(q),a,b)
            w=q-p
            if smallest is None or w<smallest: smallest=w
        else:
            assert q-p>Fr(1,10**15),("stuck",float(p))
            mid=(p+q)/2; stack+=[(p,mid),(mid,q)]
    return done,worst,float(smallest)
if __name__=="__main__":
    print("point 79/20 with (161/200,999/1000):", mu(A(Fr(79,20)),Fr(161,200),Fr(999,1000)).str(12))
    print("point 79/20 with (4/5,59/60):", mu(A(Fr(79,20)),Fr(4,5),Fr(59,60)).str(12))
    n,worst,sm=cover(Fr(79,20),Fr(10**6))
    print("cells:",n,"min lower bound:",worst,"smallest cell width:",sm)
