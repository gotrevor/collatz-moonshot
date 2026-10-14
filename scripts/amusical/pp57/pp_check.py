#!/usr/bin/env python3
"""Independent check of transitive.md's PP(0): bijection, v3(slope)=1, strong connectivity."""
import json, sys
from math import gcd
from fractions import Fraction
P=json.load(open(sys.argv[1]))['pieces']
def lcm(a,b): return a*b//gcd(a,b)
Ld=1; Li=1
for r,m,r2,m2 in P: Ld=lcm(Ld,m); Li=lcm(Li,m2)
print("pieces",len(P),"domain lcm",Ld,"image lcm",Li)
def cover(L, cls):
    c=bytearray(L)
    for r,m in cls:
        for x in range(r%m, L, m): c[x]+=1
    return min(c), max(c)
print("domain cover (min,max):",cover(Ld,[(r,m) for r,m,_,_ in P]))
print("image  cover (min,max):",cover(Li,[(r2,m2) for _,_,r2,m2 in P]))
def v3(q):
    n,d=q.numerator,q.denominator; k=0
    while n%3==0: n//=3;k+=1
    while d%3==0: d//=3;k-=1
    return k
sl={Fraction(m2,m) for _,m,_,m2 in P}
print("slopes",sorted(sl),"v3 set",{v3(s) for s in sl})
# piece lookup by residue mod Ld
look=[None]*Ld
for r,m,r2,m2 in P:
    for x in range(r%m,Ld,m): look[x]=(r,m,r2,m2)
def sigma(x):
    r,m,r2,m2=look[x%Ld]; t=(x-r)//m; return r2+m2*t
# spot check sigma bijective on a window
xs=range(-20000,20000); ys=[sigma(x) for x in xs]; assert len(set(ys))==len(ys)
def scc(M):
    assert M%Ld==0
    adj=[]
    for u in range(M):
        r,m,r2,m2=look[u%Ld]; s=Fraction(m2,m)
        y=sigma(u); step=M*m2//m; g=gcd(step,M)
        adj.append((y%g,g))
    def bfs(fwd):
        seen=bytearray(M); seen[0]=1; st=[0]; n=1
        if fwd:
            while st:
                u=st.pop(); b,g=adj[u]
                for t in range(b,M,g):
                    if not seen[t]: seen[t]=1; n+=1; st.append(t)
        else:
            radj=[[] for _ in range(M)]
            for u in range(M):
                b,g=adj[u]
                for t in range(b,M,g): radj[t].append(u)
            while st:
                u=st.pop()
                for t in radj[u]:
                    if not seen[t]: seen[t]=1; n+=1; st.append(t)
        return n
    return bfs(True), bfs(False)
for k in sys.argv[2:]:
    M=Ld*int(k); f,b=scc(M); print("M=%d (Ld*%s): reach fwd %d bwd %d of %d -> %s"%(M,k,f,b,M,"SC" if f==b==M else "NOT SC"))
