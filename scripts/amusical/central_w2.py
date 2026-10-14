#!/usr/bin/env python3
"""Independent check: tables f with stepSym(g n) = f(stepSym n, stepSym(U n)) and g∘U = U∘g.
A cycle of period p maps to an integer whose forward itinerary is the periodic word
f(s_k, s_{k+1}); that integer is the fixed point x_w of the word's affine map, must be integral
and have itinerary w."""
import itertools
from fractions import Fraction
def U(n): return 3*(n//2) if n%2==0 else (3*(n//4)+1 if n%4==1 else 3*(n//4)+2)
def sym(n): return 0 if n%2==0 else (1 if n%4==1 else 2)
cyc0=[0,1,-1,2,-2,4,-4,44,-44]
def cyc(x):
    c=[x]; y=U(x)
    while y!=x: c.append(y); y=U(y)
    return c
def fixpt(w):
    a,b=Fraction(1),Fraction(0)
    for s in w:
        bits=1 if s==0 else 2; d=(0,1,-1)[s]
        a,b=a*3/2**bits,(b*3+d)/2**bits
    x=b/(1-a)
    if x.denominator!=1: return None
    x=int(x); y=x
    for s in w:
        if sym(y)!=s: return None
        y=U(y)
    return x if y==x else None
surv=[]
for vals in itertools.product(range(3),repeat=9):
    f={(a,b):vals[3*a+b] for a in range(3) for b in range(3)}
    imgs={}
    ok=True
    for x0 in cyc0:
        c=cyc(x0); p=len(c)
        w=[f[(sym(c[k]),sym(c[(k+1)%p]))] for k in range(p)]
        y=fixpt(w)
        if y is None: ok=False;break
        imgs[x0]=y
    if ok: surv.append((vals,imgs))
print(len(surv))
for v,i in surv: print(v,i)
