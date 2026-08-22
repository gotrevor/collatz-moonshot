#!/usr/bin/env -S uv run --quiet python3
"""An integer cycle needs D | W(rot_i) for every rotation, hence D | every
DIFFERENCE W_i - W_j.  D is odd, so D divides the ODD PART of the gcd of all
differences.  Knight: for the Christoffel word one difference is a pure power of
2, so that odd part is 1, so D=1.

Question: how big is that odd part for a GENERAL word?  If bounded, D is bounded,
Baker closes, Front B falls.  So: measure it."""
from math import gcd
import random

def W(v):
    k=len(v); x=sum(v); ds=[p for p in range(k) if v[p]]
    return sum(3**(x-1-i)*2**d for i,d in enumerate(ds))
def rot(v,j): return v[j:]+v[:j]
def oddpart(n):
    n=abs(n)
    while n and n%2==0: n//=2
    return n

def odd_gcd_of_diffs(v):
    Ws=[W(rot(v,j)) for j in range(len(v))]
    g=0
    for i in range(len(Ws)):
        for j in range(i+1,len(Ws)):
            g=gcd(g,Ws[i]-Ws[j])
            if g==1: return 1
    return oddpart(g)

random.seed(11)
print(f"{'k':>3} {'x':>3} {'D':>16} {'oddpart(gcd diffs)':>20}   verdict")
for k in (8,11,14,17,19,23,27,29,34,41):
    x=round(k*0.63093)
    if 2**k<=3**x: x-=1
    D=2**k-3**x
    # (a) the Christoffel / high-cycle word
    ds=[(k*i)//x for i in range(x)]
    vc=[1 if p in ds else 0 for p in range(k)]
    oc=odd_gcd_of_diffs(vc)
    # (b) random words
    worst=0
    for _ in range(60):
        S=sorted(random.sample(range(k),x))
        v=[1 if p in S else 0 for p in range(k)]
        worst=max(worst,odd_gcd_of_diffs(v))
    print(f"{k:>3} {x:>3} {D:>16} christoffel={oc:<6} random-max={worst:<12} "
          f"{'BOUNDED' if worst<1000 else 'grows with D'}")
