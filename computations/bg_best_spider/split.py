from sympy import *
u,X,Y=symbols('u X Y',nonnegative=True)
al=lambda x:(4*sympify(x)+3)/(3*(sympify(x)+1)); b=lambda x:3/(4*sympify(x)+3)
g=lambda j: Rational(3,2)**j*al(j)
gam=simplify(g(u+2)*g(5)**2/g(u+13)); print("Gamma(u)=",factor(gam))
Dd=(15824*X**2*u**3 + 308568*X**2*u**2 + 846285*X**2*u + 322828*X**2 + 114080*X*u**3 + 2236428*X*u**2 + 9353847*X*u + 11182600*X + 98256*u**3 + 1659588*u**2 + 6964998*u + 8646528) + Y*(15824*X*u**3 + 308568*X*u**2 + 846285*X*u + 322828*X - 341872*u**3 - 6666504*u**2 - 30385047*u - 40253312)
lhs=(gam*(3+X+b(u+2)+2*b(5)+Y)*(1+X)-(1+X+b(u+13)+Y)*(3+X))*486*23*(u+3)*(4*u+55)*(4*u+11)
print("identity:", simplify(expand(lhs)-Dd)==0)
P0=Dd.subs(Y,0)
E=expand(Dd.subs(Y,X/3)*3/X*X/3) # placeholder
E=(63296*X**2*u**3/3 + 411424*X**2*u**2 + 1128380*X**2*u + Rational(1291312,3)*X**2 + 368*X*u**3/3 + 14260*X*u**2 - 774502*X*u - Rational(6705512,3)*X + 98256*u**3 + 1659588*u**2 + 6964998*u + 8646528)
print("X*Dd = (X-3Y)P0 + 3Y E:", expand(X*Dd-((X-3*Y)*P0+3*Y*E))==0)
print("E == Dd(Y=X/3):", expand(E-Dd.subs(Y,X/3))==0)
q1=1128380*X**2-774502*X+6964998; q2=Rational(1291312,3)*X**2-Rational(6705512,3)*X+8646528
print("disc q1", discriminant(q1,X)<0, "disc q2", discriminant(q2,X)<0)
