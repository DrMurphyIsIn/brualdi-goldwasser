import sympy as sp
from sympy import Rational as Q
from fractions import Fraction as Fr
x,y,k,D,R,j,X,Y,u=sp.symbols('x y kappa D0 R0 j X Y u')
al=lambda t:sp.Rational(4*t+3,3*(t+1)) if isinstance(t,int) else (4*t+3)/(3*(t+1)); b=lambda t:sp.Rational(3,4*t+3) if isinstance(t,int) else 3/(4*t+3)
Qk=al(x)*al(y)*(k+b(x)+b(y))
print('balance Q identity:', sp.simplify(Qk-(16*k/9-((k-3)*(4*(x+y)+7)+3)/(9*(x+1)*(y+1)))))
TA=lambda t:Q(3,2)**t*al(t); 
# leaf pair: Omega = prod T * (1+ (R)/D)
Om=lambda Ts,Rs,Dc: Ts*(1+Rs/Dc)
lp=Om(Q(3,2),R+Q(1,3),D+1)-Om(1,R+2,D+2)
print('leafpair:', sp.simplify(lp-(D**2+D*R+4*R)/(2*(D+1)*(D+2))))
jj=sp.symbols('j',integer=True,nonnegative=True)
Tj=lambda t:(Q(3,2))**t*(4*t+3)/(3*(t+1))
ab=Om(Tj(jj+1),R+b(jj+1),D+1)-Om(Q(3,2)*Tj(jj),R+Q(1,3)+b(jj),D+2)
cl=Q(3,2)**(jj+1)*(3*D**2+D*(3*R-4*jj**2-11*jj-6)+R*(12*jj**2+33*jj+24)-4*jj**2-2*jj)/(9*(jj+1)*(jj+2)*(D+1)*(D+2))
print('absorb:', sp.simplify(sp.powsimp(ab-cl,force=True)), [sp.simplify(ab.subs(jj,t)-cl.subs(jj,t)) for t in range(0,6)])
num=lambda t:3*D**2+D*(3*R-4*t**2-11*t-6)+R*(12*t**2+33*t+24)-4*t**2-2*t
for t in [4,5]:
    print('endpoints j',t, sp.factor(num(t).subs(R,D/9)), '|', sp.factor(num(t).subs(R,D/3)))
    d0=next(d for d in range(1,200) if all(num(t).subs({D:dd,R:r}) >0 for dd in range(d,300) for r in [Q(dd,9),Q(dd,3)]))
    print('  first D0 from which both positive',d0)
# counts rows
def TR(atom):
    if atom=='C': return Q(3,2),Q(1,3),2
    t=int(atom[1:]); return TA(t),Q(3,4*t+3),2*t+1
rows=[('A1',11,'A5',3,'1.937',0,1),('A2',11,'A5',5,'1.264',0,1),('A3',11,'A5',7,'1.074',0,1),('A7',11,'A5',15,'1.051',0,1),
('A8',11,'A5',17,'1.1',0,1),('A9',11,'A5',19,'1.161',0,1),('A10',11,'A5',21,'1.231',0,1),('A11',11,'A5',23,'1.312',0,1),
('A12',11,'A5',25,'1.403',0,1),('A6',11,'A5',13,'1.0168',0,Q(1,3)),('A4',11,'A5',9,'1.0113',Q(1,9),1),('C',9,'A4',2,'1.069',Q(1,9),1)]
listed={'A1':('150857X^2+1475029X+4043622','150857X^2+2211228X+2021811'),'A2':('253X^2+1963X+8230','253X^2+5248X+4115'),
'A3':('851X^2+1295X+12474','851X^2+28328X+6237'),'A7':('12121X^2+550861X+3580830','36363X^2-399712X+5371245'),
'A8':('161X^2+6917X+47498','161X^2-486X+23749'),'A9':('48139X^2+2051471X+14717362','48139X^2+94500X+7358681'),
'A10':('76153X^2+3295489X+24505866','228459X^2+1254758X+36758799'),'A11':('611X^2+27107X+207746','611X^2+5164X+103873'),
'A12':('6851X^2+313411X+2464550','6851X^2+75386X+1232275'),'A6':('4347X^2+234199X+1417702','2898X^2+38819X+708851'),
'A4':('246905X^2-1723254X-28591299','49381X^2+3934390X-3176811'),'C':('6555X^2-90343X-147042','1311X^2+54317X-16338')}
def parse(s): return sp.sympify(s.replace('X^2','*X**2').replace('X','*X').replace('**X','*X').replace('+*','+').replace('-*','-').lstrip('*'))
for o,mo,nn,mn,gs,ylo,yhi in rows:
    TO,yO,cO=TR(o); TN,yN,cN=TR(nn)
    assert mo*cO==mn*cN, (o,mo*cO,mn*cN)
    G=TN**mn/TO**mo; g=sp.nsimplify(gs)
    ok=g<=G
    Dl=lambda Rv: sp.expand(g*(mn+X+mn*yN+Rv)*(mo+X)-(mo+X+mo*yO+Rv)*(mn+X))
    res=[]
    for yy,lst in zip([ylo,yhi],listed[o if o!='C' else 'C']):
        P=Dl(yy*X); L=parse(lst.replace(' ',''))
        rat=sp.simplify(P/L); res.append((rat.is_constant() and rat>0))
    roots=[sp.nroots(parse(l.replace(' ',''))) for l in listed[o]]
    print(o,'Gamma',float(G),'gamma<=Gamma',ok,'prop',res, 'roots', [[complex(r) for r in rr] for rr in roots] if o in('A4','C','A7','A8') else '')
# split lemma
Gu=Q(529,486)*(4*u+11)*(u+14)/((u+3)*(4*u+55))
# verify Gamma(u) formula
Ts=lambda t:Q(3,2)**t*(4*t+3)/(3*(t+1))
print('Gamma(u) check', sp.simplify(Ts(u+2)*Ts(5)**2/Ts(u+13)-Gu), sp.simplify(Q(2,3)*Q(23,18)**2*al(u+2)/al(u+13)-Gu))
mO=1;mN=3;RO=3/(4*(u+13)+3);RN=3/(4*(u+2)+3)+2*Q(3,23)
Dl=Gu*(mN+X+RN+Y)*(mO+X)-(mO+X+RO+Y)*(mN+X)
DD=sp.factor(sp.simplify(486*23*(u+3)*(4*u+55)*(4*u+11)*Dl))
D0p=X**2*(15824*u**3+308568*u**2+846285*u+322828)+X*(114080*u**3+2236428*u**2+9353847*u+11182600)+98256*u**3+1659588*u**2+6964998*u+8646528
D1p=X*(15824*u**3+308568*u**2+846285*u+322828)-(341872*u**3+6666504*u**2+30385047*u+40253312)
print('split D=D0+Y D1:', sp.simplify(sp.expand(DD)-(D0p+Y*D1p)))
exp=sp.Rational(63296,3)*X**2*u**3+411424*X**2*u**2+sp.Rational(368,3)*X*u**3+14260*X*u**2+98256*u**3+1659588*u**2+u*(1128380*X**2-774502*X+6964998)+(sp.Rational(1291312,3)*X**2-sp.Rational(6705512,3)*X+8646528)
print('split at Y=X/3:', sp.simplify(sp.expand((D0p+Y*D1p).subs(Y,X/3))-exp))
print('discs', 774502**2-4*1128380*6964998, sp.Rational(6705512,3)**2-4*sp.Rational(1291312,3)*8646528)
# global
om=lambda t:Q(2,3)*al(t)**2
print('omega', om(4),om(5),om(6),om(12), 'limit 32/27', sp.limit(om(u),u,sp.oo))
print('(10/9)^2(529/486)^36', float(Q(100,81)*Q(529,486)**36), '(10/9)^2(529/486)^18',float(Q(100,81)*Q(529,486)**18), '4(32/27)^2',float(4*Q(32,27)**2),'(4/3)^2(578/507)^20', float(Q(16,9)*Q(578,507)**20))
# comparison spider existence w>=36 for n>=441
bad=[]
for n in range(441,5000):
    N=n-1; s=(6*N)%11
    cost=min(13*s, 9*((11-s)%11)) if s else 0
    w=(N-cost)//11
    assert (N-cost)%11==0
    if w<36: bad.append(n)
print('w<36 for n in 441..4999:',bad[:5])
# race
G4,G5,G6=Q(513,80),Q(621,64),Q(6561,448)
assert G4==TA(4) and G5==TA(5) and G6==TA(6)
b4,b5,b6=Q(3,19),Q(3,23),Q(1,9)
print('b6-b5',b6-b5,'b4-b5',b4-b5)
K0=G5**9/G4**11; th=G4*G6/G5**2
print('K0',K0,'theta',th)
Dd=sp.symbols('D')
for s in range(0,11):
    Ks=G6**s*G5**(9-2*s)/G4**(11-s); assert Ks==K0*th**s
    if s in (4,5): print('K',s,Ks,float(Ks))
    if 1<=s<=4:
        qs=Q(26,23)*(Ks-1)*Dd*(Dd+2)-Q(4*s,207)*Ks*(Dd+2)-Q(12*(11-s),437)*Dd
        # verify q_s definition
        a=sp.symbols('a')
        bX=1+(s*b6+(Dd-s)*b5)/Dd; bY=1+((11-s)*b4+(Dd-s+2*s-9)*b5)/(Dd+2)
        assert sp.simplify(Dd*(Dd+2)*(Ks*bX-bY)-qs)==0
        rts=[r for r in sp.nroots(qs) if r>0]
        Ds=int(rts[0]); print('s',s,'Ks',Ks,float(Ks),'root',rts,'signs',qs.subs(Dd,Ds)<0<qs.subs(Dd,Ds+1),'n switch',11*Ds+2*s+1,'|',11*(Ds+1)+2*s+1)
# liminf
from mpmath import mp,mpf,log,exp
mp.dps=30
rho=(mpf(621)/64)**(mpf(1)/11)
print('liminf',mpf(26)/23*(mpf(513)/80)**6*rho**-54)
F=log(mpf(621)/64)/11
g4=9*F-log(mpf(513)/80); g6=13*F-log(mpf(6561)/448)
print('g4,g6',g4,g6,'6g4',6*g4,'4g6',4*g6, 'int compare', (G4**6/G6**4)**11<G5**2, G4**11<G5**9, G6**11<G5**13)
