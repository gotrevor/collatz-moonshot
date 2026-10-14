#!/usr/bin/env python3
"""Independent check of q1 Theorem W3: no bijective reversor iota with
stepSym(iota n) = f(sym(V n), sym n, sym(U n))."""
import itertools, sys
from fractions import Fraction
def U(n): return 3*(n//2) if n%2==0 else (3*(n//4)+1 if n%4==1 else 3*(n//4)+2)
def V(m): return 2*(m//3) if m%3==0 else (4*(m//3)+1 if m%3==1 else 4*(m//3)+3)
def sym(n): return 0 if n%2==0 else (1 if n%4==1 else 2)
assert all(V(U(n))==n and U(V(n))==n for n in range(-1000,1000))
# 1. integer cycles of length <= 12 via exact periodic-point formula over all words
cyc=set()
for p in range(1,13):
    for w in itertools.product(range(3),repeat=p):
        # affine map x -> (3x+d)/2^b composed; solve x = (3^p x + N)/2^e
        a,b=Fraction(1),Fraction(0)
        for s in w:
            bits=1 if s==0 else 2; d={0:0,1:1,2:-1}[s]
            a,b=a*3/2**bits,(b*3+d)/2**bits
        if a==1: continue
        x=b/(1-a)
        if x.denominator==1:
            x=int(x); ok=True; y=x
            for s in w:
                if sym(y)!=s: ok=False;break
                y=U(y)
            if ok and y==x:
                c=[x]; y=U(x)
                while y!=x: c.append(y); y=U(y)
                cyc.add(min(c))
cycles={}
for m in sorted(cyc):
    c=[m]; y=U(m)
    while y!=m: c.append(y); y=U(y)
    cycles[m]=c
print("cycles:",{m:len(c) for m,c in cycles.items()})
# 2. bijective iota permutes cycles preserving length; iota(U^j x0)=V^j(y0)
bylen={}
for m,c in cycles.items(): bylen.setdefault(len(c),[]).append(m)
def window(x): return (sym(V(x)),sym(x),sym(U(x)))
def options_for_len(L):
    ms=bylen[L]
    for perm in itertools.permutations(ms):
        for phases in itertools.product(range(L),repeat=len(ms)):
            cons={}; ok=True
            for src,dst,ph in zip(ms,perm,phases):
                x0=cycles[src][0]; y0=cycles[dst][ph]
                x,y=x0,y0
                for j in range(L):
                    k=window(x); v=sym(y)
                    if cons.get(k,v)!=v: ok=False;break
                    cons[k]=v; x=U(x); y=V(y)
                if not ok: break
            if ok: yield cons
partials=[{}]
for L in sorted(bylen):
    new=[]
    for P in partials:
        for c in options_for_len(L):
            if all(P.get(k,v)==v for k,v in c.items()):
                Q=dict(P); Q.update(c)
                if Q not in new: new.append(Q)
    partials=new
    print("len",L,"partial rules:",len(partials))
blocks=list(itertools.product(range(3),repeat=3))
def surj_upto(f,Lmax=6):
    for L in range(1,Lmax+1):
        imgs=set()
        for x in itertools.product(range(3),repeat=L+2):
            imgs.add(tuple(f[x[i:i+3]] for i in range(L)))
        if len(imgs)<3**L: return L
    return None
tot=0;surv=0
for P in partials:
    free=[b for b in blocks if b not in P]
    for vals in itertools.product(range(3),repeat=len(free)):
        f=dict(P); f.update(zip(free,vals)); tot+=1
        if surj_upto(f) is None: surv+=1; print("SURVIVOR",f)
print("completions",tot,"surjective-up-to-6 survivors",surv)
