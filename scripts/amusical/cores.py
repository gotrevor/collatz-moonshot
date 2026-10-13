#!/usr/bin/env python3
"""Independent sanity check of antikohl §4.1/§4.2 core densities by box counting."""
def U(n): return 3*(n//2) if n%2==0 else (3*(n//4)+1 if n%4==1 else 3*(n//4)+2)
def kappa(x):
    r=x%6
    return {0:2*x+5,2:(2*x+2)//3,4:(2*x-8)//3,1:(2*x+7)//3,3:2*x-5,5:2*x-1}[r]
def kinv(y):
    for c in ((y-5)/2,(3*y-2)/2,(3*y+8)/2,(3*y-7)/2,(y+5)/2,(y+1)/2):
        if c==int(c) and kappa(int(c))==y: return int(c)
    raise Exception(y)
def ctau(x): return 2*x if x%2==1 else (x//2 if x%4==2 else x)
def st(x): return ctau(U(x))
def stinv(y):
    # ctau is an involution; U^-1
    z=ctau(y)
    return 2*(z//3) if z%3==0 else (4*(z//3)+1 if z%3==1 else 4*(z//3)+3)
assert all(kinv(kappa(x))==x for x in range(-3000,3000))
assert all(stinv(st(x))==x and st(stinv(x))==x for x in range(-3000,3000))
X=200000; box=range(-X,X)
inS=lambda x: x%2==1 or x%12==0
for n in range(0,9):
    fw=0; bw=0
    for x in box:
        y=x
        for _ in range(n): y=kinv(y)
        fw+=inS(y)
        y=x; ok=True
        for _ in range(n+1):
            if inS(y): ok=False;break
            y=kappa(y)
        bw+=ok
    print("kappa n=%d  d(k^n S)=%.4f  d(A_n)=%.4f  pred %.4f"%(n,fw/(2*X),bw/(2*X),5/12*(2/3)**n))
inT=lambda x: x%4==2
for n in range(1,9):
    bw=0
    for x in box:
        y=x; ok=True
        for _ in range(n+1):
            if inT(y): ok=False;break
            y=st(y)
        bw+=ok
    print("sigmaTau n=%d d(A_n)=%.4f pred(1/2)(3/4)^(n-1)=%.4f"%(n,bw/(2*X),0.5*0.75**(n-1)))
