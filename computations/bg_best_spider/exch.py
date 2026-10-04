from sympy import *
X=symbols('X')  # D0
def al(j): return Rational(4*j+3,3*(j+1))
def g(c): return Rational(3,2) if c=='P' else Rational(3,2)**c*al(c)
def r(c): return Rational(1,3) if c=='P' else Rational(3,4*c+3)
def cost(c): return 2 if c=='P' else 2*c+1
def analyze(name, old, new, lo, hi, gam=None):
    assert sum(map(cost,old))==sum(map(cost,new))
    G=prod([g(c) for c in new])/prod([g(c) for c in old])
    a,b=len(old),len(new); RO=sum(r(c) for c in old); RN=sum(r(c) for c in new)
    out=[]
    for GG,lab in [(G,'exact')]+([(Rational(gam),'lean')] if gam else []):
        res=[]
        for lam in (lo,hi):
            Y=lam*X
            Dl=expand(GG*(b+X+RN+Y)*(a+X)-(a+X+RO+Y)*(b+X))
            # minimal integer X0>=0 such that Dl(X)>0 for all integer X>=X0
            p=Poly(Dl,X); rts=[rr for rr in p.real_roots()]
            lc=p.LC()
            # find X0
            X0=0
            while not all(Dl.subs(X,x)>0 for x in range(X0,X0+1)) or (rts and X0<=max(rts)):
                X0+=1
                if X0>10000: X0=None;break
            res.append((lam,Dl,X0))
        out.append((lab,res))
    print(f"{name}: Gamma={G} ~ {float(G):.6f}; a={a} b={b}")
    for lab,res in out:
        for lam,Dl,X0 in res:
            print(f"   [{lab}] R0={lam}*D0: {Dl}  -> positive for all integer D0>={X0}")
    return G
for jj,gam in [(1,'1937/1000'),(2,'158/125'),(3,'537/500'),(7,'1051/1000'),(8,'11/10'),(9,'1161/1000'),(10,'1231/1000'),(11,'164/125'),(12,'1403/1000')]:
    analyze(f"11A{jj}->{2*jj+1}A5",[jj]*11,[5]*(2*jj+1),0,1,gam)
analyze("11A6->13A5",[6]*11,[5]*13,0,Rational(1,3),'1271/1250')
analyze("11A4->9A5",[4]*11,[5]*9,Rational(1,9),1,'10113/10000')
analyze("9P->2A4",['P']*9,[4]*2,Rational(1,9),1,'1069/1000')
for jj in range(0,7):
    analyze(f"P+A{jj}->A{jj+1}",['P',jj],[jj+1],Rational(1,9),Rational(1,3))
