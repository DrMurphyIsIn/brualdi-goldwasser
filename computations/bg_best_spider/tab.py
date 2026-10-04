from sympy import *
X=symbols('X')
def al(j): return Rational(4*j+3,3*(j+1))
def g(c): return Rational(3,2) if c=='P' else Rational(3,2)**c*al(c)
def r(c): return Rational(1,3) if c=='P' else Rational(3,4*c+3)
def row(name, old, new, lo, hi, gam):
    G=prod([g(c) for c in new])/prod([g(c) for c in old]); gam=Rational(gam); assert gam<=G
    a,b=len(old),len(new); RO=sum(r(c) for c in old); RN=sum(r(c) for c in new)
    qs=[]
    for lam in (lo,hi):
        Dl=expand(gam*(b+X+RN+lam*X)*(a+X)-(a+X+RO+lam*X)*(b+X))
        p=Poly(Dl,X); c=p.all_coeffs(); den=ilcm(*[fraction(ci)[1] for ci in c]); ci=[ci*den for ci in c]; gg=igcd(*[int(x) for x in ci]); ci=[int(x)//gg for x in ci]
        qs.append(ci)
    return name,gam,float(G),qs
rows=[]
for jj,gam in [(1,'1937/1000'),(2,'158/125'),(3,'537/500'),(7,'1051/1000'),(8,'11/10'),(9,'1161/1000'),(10,'1231/1000'),(11,'164/125'),(12,'1403/1000')]:
    rows.append(row(f"11A_{{{jj}}}\\to{2*jj+1}A_5",[jj]*11,[5]*(2*jj+1),0,1,gam))
rows.append(row("11A_6\\to13A_5",[6]*11,[5]*13,0,Rational(1,3),'1271/1250'))
rows.append(row("11A_4\\to9A_5",[4]*11,[5]*9,Rational(1,9),1,'10113/10000'))
rows.append(row("9P\\to2A_4",['P']*9,[4]*2,Rational(1,9),1,'1069/1000'))
for name,gam,G,qs in rows:
    f=lambda c: "%d X^2 %+d X %+d"%tuple(c)
    print(f"${name}$ & {G:.6f} & ${latex(gam)}$ & ${f(qs[0])}$ & ${f(qs[1])}$ \\\\")
