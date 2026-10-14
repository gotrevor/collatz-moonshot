#!/usr/bin/env python3
"""Lemma E check with my own sigma: Omega0 points stay in engine pieces (slopes 21/5, 15, 75/7, 3)."""
import json, sys
from fractions import Fraction
P=json.load(open(sys.argv[1]))['pieces']; Ld=13300
look=[None]*Ld
for r,m,r2,m2 in P:
    for x in range(r%m,Ld,m): look[x]=(r,m,r2,m2)
ENG={Fraction(21,5),Fraction(15),Fraction(75,7),Fraction(3)}
def step(x):
    r,m,r2,m2=look[x%Ld]; return r2+m2*((x-r)//m), Fraction(m2,m)
def v(p,x):
    k=0
    while x%p==0: x//=p;k+=1
    return k
def inOmega0(x):
    A=v(5,x); return x!=0 and A%2==1 and x%7!=0 and (x*pow(8,A,19))%19==1
stay=leak=0; ctrl_leak=ctrl=0
for x in range(-60000,60000):
    if x==0 or x%5: continue
    A=v(5,x)
    if x%7==0 or (x*pow(8,A,19))%19!=1: continue
    y=x; ok=True
    for _ in range(120):
        y,s=step(y)
        if s not in ENG: ok=False;break
    if A%2==1: stay+=ok; leak+=(not ok)
    else: ctrl+=1; ctrl_leak+=(not ok)
print("odd-A Omega0: stayed %d leaked %d | even-A controls: %d, leaked %d"%(stay,leak,ctrl,ctrl_leak))
