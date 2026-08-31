#!/usr/bin/env python3
"""Mod-p certificate probe for rhinLite_integralMatrix_det_ne_zero.

For a prime p > N_max (so p ∤ lcmUpto N and all (j-N), 2, 3 are invertible mod p),
compute the INTEGER form determinant det(B,A1,A2) MOD p, where
  B = lcmUpto(N) * c_N,   A_i = lcmUpto(N) * R_i  (integers),
  R1 = sum_{j!=N} c_j (3^{j-N}-2^{j-N})/(j-N),  R2 similarly with 4,3.
All arithmetic mod p (coeffs of H_N built mod p -> fast even for N=6000).
If det mod p != 0 then the integer determinant is nonzero  => the real integral
determinant is nonzero (they differ by the nonzero factor prod D_N).  This tests
whether a p-adic / native_decide-mod-p route can formalize the node.
"""
import sys
from math import gcd
p = 10007  # prime, > 6000
assert all(p % q for q in range(2, int(p**0.5)+1)), "p not prime"

W = (705, 551, 449, 109, 39, 54)
FACT = [(-3,1),(-2,1),(-4,1),(-12,5),(144,-102,17),(144,-108,19)]

def polymul_mod(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                if bj: r[i+j]=(r[i+j]+ai*bj)%p
    return r
def polypow_mod(base,e,p):
    res=[1]; b=[x%p for x in base]
    while e:
        if e&1: res=polymul_mod(res,b,p)
        e>>=1
        if e: b=polymul_mod(b,b,p)
    return res
def build_HN_mod(t,p):
    poly=[1]
    for c,w in zip(FACT,W):
        poly=polymul_mod(poly, polypow_mod(list(c),2*w*t,p), p)
    return poly

def lcmUpto(N):
    # lcm of 1..N  (Nat.lcmUpto N)
    from math import gcd
    l=1
    for k in range(1,N+1): l=l//gcd(l,k)*k
    return l

def row_mod(t,p):
    N=2000*t
    c=build_HN_mod(t,p)
    assert len(c)==2*N+1
    cN=c[N]%p
    D=lcmUpto(N)%p
    inv=lambda a:pow(a%p,p-2,p)
    i2=inv(2); i3=inv(3); i4=inv(4)
    R1=0;R2=0
    for j,cj in enumerate(c):
        if cj==0 or j==N: continue
        k=j-N
        # 3^k mod p (k may be negative -> use inverse)
        def pw(base,k):
            if k>=0: return pow(base,k,p)
            return pow(inv(base), -k, p)
        t3=pw(3,k); t2=pw(2,k); t4=pw(4,k)
        invk=inv(k%p)
        R1=(R1+cj*((t3-t2)%p)*invk)%p
        R2=(R2+cj*((t4-t3)%p)*invk)%p
    B=(D*cN)%p; A1=(D*R1)%p; A2=(D*R2)%p
    return (B%p,A1%p,A2%p)

def det3_mod(rows,p):
    (a,b,c),(d,e,f),(g,h,i)=rows
    return (a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g))%p

for t0 in (0,1,2):
    rows=[]
    for s in (t0,t0+1,t0+2):
        rows.append((1,0,0) if s==0 else row_mod(s,p))
    d=det3_mod(rows,p)
    print(f"t0={t0}: det mod {p} = {d}  => {'NONZERO (cert)' if d!=0 else 'zero mod p (inconclusive)'}", flush=True)
