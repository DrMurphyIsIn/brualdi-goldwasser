"""Exact dry run of the strict spider sweep (mirrors checkBalS / checkSmallS) for 150 <= n <= 491."""
import re, math, time
src=open('R3Cert/BGSpiderTableData.lean').read()
data=eval('['+re.search(r'def tabData : List \(ℕ × ℕ × ℕ × ℕ\) := \[(.*)\]', src).group(1)+']')
def row(n): return data[n-4]
def fnum(C,s,a,b):
    A=4*s+3; B=4*s+7; D=C+a+b
    return 3**C*(3**s*A)**a*(3**(s+1)*B)**b*(D*(3*A*B)+(C*A*B+9*a*B+9*b*A))
def fden(C,s,a,b):
    A=4*s+3; B=4*s+7; D=C+a+b
    return 2**C*(2**s*(3*(s+1)))**a*(2**(s+1)*(3*(s+2)))**b*(D*(3*A*B))
def balOf(n,C,m):
    V=n-1-2*C; J=(V-m)//2; return (J//m, m-J%m, J%m)
def gnd(c): return (3,2) if c=='c' else (3**c*(4*c+3), 2**c*(3*(c+1)))
def rnd(c): return (1,3) if c=='c' else (3,4*c+3)
def cost(c): return 2 if c=='c' else 2*c+1
def f1(c): g,r=gnd(c),rnd(c); return (g[0]*(r[1]+r[0]), g[1]*r[1])
def f2(c,d):
    rs=rnd(c)[0]*rnd(d)[1]+rnd(d)[0]*rnd(c)[1]; rd=rnd(c)[1]*rnd(d)[1]
    return (gnd(c)[0]*gnd(d)[0]*(2*rd+rs), gnd(c)[1]*gnd(d)[1]*(2*rd))
worst=(1,None); t0=time.time()
for n in range(150,492):
    C0,s0,a0,b0=row(n); assert a0+b0>0; m0=a0+b0
    T=(fnum(C0,s0,a0,b0),fden(C0,s0,a0,b0))
    for C in range((n-1)//2+1):
        for m in range(n-1-2*C+1):
            if 3<=C+m and (n-1-2*C-m)%2==0:
                if C==C0 and m==m0: continue
                x=(fnum(C,0,0,0),fden(C,0,0,0)) if m==0 else (lambda p:(fnum(C,*p),fden(C,*p)))(balOf(n,C,m))
                assert x[0]*T[1] < T[0]*x[1], (n,C,m)
                gap=math.log(T[0]*x[1])-math.log(x[0]*T[1])
                if gap<worst[0]: worst=(gap,(n,C,m))
    kids=['c']+list(range(n+1))
    for c in kids:
        if cost(c)==n-1: x=f1(c); assert x[0]*T[1]<T[0]*x[1]
    for c in kids:
        for d in kids:
            if cost(c)+cost(d)==n-1: x=f2(c,d); assert x[0]*T[1]<T[0]*x[1]
print("strict sweep 150..491 OK; smallest log gap", worst, f"{time.time()-t0:.0f}s")
