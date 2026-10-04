from fractions import Fraction as Fr
from sympy import Rational as R, symbols, solve, sqrt, nsimplify, Poly, N
import math
al=lambda j:Fr(4*j+3,3*(j+1)); g=lambda j:Fr(3,2)**j*al(j); b=lambda j:Fr(3,4*j+3)
h=lambda j:Fr(2,3)*al(j)**2
print("h4,h5,h6,h12:",h(4),h(5),h(6),h(12))
lhs3=Fr(4,3)**2*h(12)**20; rhs=Fr(10,9)**2*h(5)**37
print("step3: %.4f < %.4f"%(float(lhs3),float(rhs)), lhs3<rhs)
lhs1=4*Fr(32,27)**2; print("step1: %.4f"%float(lhs1))
for w in range(10,40):
    r=Fr(10,9)**2*h(5)**w
    if r>lhs1 and not hasattr(math,'x1'): print(" step1 needs w5>=",w); math.x1=1
    if r>lhs3: print(" step3 needs w5>=",w); break
# deficits
G5=g(5)
for j in [4,6]:
    print("delta",j, math.log(g(j))-(2*j+1)/11*math.log(G5))
print("delta P", math.log(1.5)-2/11*math.log(G5))
# races
x=symbols('x')
print("s  K_s  (A6 wins iff D > D*)")
for s in range(1,11):
    K=g(6)**s*G5**(9-2*s)/g(4)**(11-s) if 9-2*s>=0 else g(6)**s/(g(4)**(11-s)*G5**(2*s-9))
    u=Fr(12*(11-s),437); v=Fr(4*s,207)
    # check brackets formulas
    a=50; DX=s+a; DY=DX+2
    BX=1+(s*b(6)+a*b(5))/DX; aY=a+2*s-9; BY=1+((11-s)*b(4)+aY*b(5))/(11-s+aY)
    assert BX==Fr(26,23)-v/DX and BY==Fr(26,23)+u/DY and 11-s+aY==DY
    KK=R(K.numerator,K.denominator)
    # (K-1)(26/23) D(D+2) - K v (D+2) - u D = 0
    poly=(KK-1)*R(26,23)*x*(x+2)-KK*R(v.numerator,v.denominator)*(x+2)-R(u.numerator,u.denominator)*x
    rts=[N(r_,20) for r_ in solve(poly,x)]
    print(s, K, "%.8f"%float(K), "roots D:", [ "%.4f"%float(r_) for r_ in rts], " n*=11D+2s+1:", ["%.2f"%float(11*r_+2*s+1) for r_ in rts])
