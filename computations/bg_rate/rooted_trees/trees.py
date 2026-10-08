"""Helpers for exhaustive_rooted.py: a branch (rooted tree) is the sorted tuple of its child branches.
val(b) = (Z, y, size) in exact rationals; g, sigma, delta (sum of the vertex slacks sigma_v) in floating point."""
import os; os.environ["OMP_NUM_THREADS"]="1"
import math, sys, itertools, random
from fractions import Fraction as Fr
from functools import lru_cache
from mpmath import mp, mpf
mp.dps=30
LAM=float(mp.log(mpf(621)/64)/11); BETA=2*LAM-math.log(1.5); q=3/23; KAP=BETA/(1/3-q)**2; GAM=1.5*(LAM-BETA)
def h(x): return KAP*(x-q)**2 if x<=1/3 else BETA+GAM*(x-1/3)
def w(x): return 11-621/14*(x-q) if x<=1/3 else 2-1.5*(x-1/3)
ETAS={1:2791/2500000,2:2791/2500000,3:2791/2500000,4:2791/2500000,5:2791/2500000,6:9387/10000000,7:4183/5000000,8:7507/10000000,9:1701/2500000,10:311/500000,11:179/312500,12:5309/10000000,13:2473/5000000,14:463/1000000,15:34/78125,16:2053/5000000,17:1943/5000000,18:461/1250000,19:351/1000000,20:837/2500000,21:1/3125,22:613/2000000}
DELTA0=0.01426
LEAF=(); CH=(LEAF,)
def A(j): return tuple([CH]*j)
@lru_cache(maxsize=None)
def val(b):
    Z=Fr(1); S=Fr(0); n=1
    for c in b:
        z,x,m=val(c); Z*=z; S+=x; n+=m
    d=len(b)+1
    return Z*(d+S)/d, 1/(d+S), n
def logF(z): return math.log(z.numerator)-math.log(z.denominator)
@lru_cache(maxsize=None)
def g(b):
    z,x,n=val(b); return n*LAM-logF(z)
def sigma(b):
    xs=[float(val(c)[1]) for c in b]; c=len(xs); S=sum(xs)
    return LAM+sum(h(x) for x in xs)-math.log1p(S/(c+1))-h(1/(c+1+S))
@lru_cache(maxsize=None)
def delta(b):  # sum of slacks
    return sigma(b)+sum(delta(c) for c in b)
def is_atom(b): return b==LEAF or b==CH or all(c==CH for c in b)
@lru_cache(maxsize=None)
def nmin(b):   # number of minimal non-atom vertices
    if is_atom(b): return 0
    if all(is_atom(c) for c in b): return 1
    return sum(nmin(c) for c in b)
@lru_cache(maxsize=None)
def cap(b): return max([len(b)]+[cap(c) for c in b])
def Phi_root(children):
    Z=Fr(1); S=Fr(0); N=0
    for c in children:
        z,x,m=val(c); Z*=z; S+=x; N+=m
    k=len(children); return logF(Z*(1+S/k))-N*LAM, N
