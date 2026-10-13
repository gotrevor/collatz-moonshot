# survival probabilities of the multiplicative log-walks (offsets ignored)
from math import log
from functools import lru_cache
import sys
sys.setrecursionlimit(100000)
L2,L3=log(2),log(3)
def surv(steps, depth):
    # P(walk stays > 0 for steps 1..depth); state = (i,j) with value i*L3 - j*L2
    from collections import defaultdict
    dist={(0,0):1.0}; alive=1.0
    for k in range(depth):
        nd=defaultdict(float)
        for (i,j),p in dist.items():
            for (di,dj),q in steps:
                ni,nj=i+di,j+dj
                if ni*L3-nj*L2>0: nd[(ni,nj)]+=p*q
        # drop states far above 0 (they survive w.p. ~1): absorb when value > H
        H=40.0
        out=0.0; keep={}
        for s,p in nd.items():
            if s[0]*L3-s[1]*L2>H: out+=p
            else: keep[s]=p
        alive_far = out
        dist=keep
        yield k, sum(dist.values()), alive_far
fwd=[((1,1),0.5),((1,2),0.5)]          # x3/2, x3/4
bwd=[((-1,-1),1/3),((-1,-2),2/3)]      # x2/3, x4/3
def total(steps,depth):
    far=0.0
    for k,inside,out in surv(steps,depth): far+=out
    return far, inside
pf=total(fwd,3000); pb=total(bwd,3000)
print('pf', pf, 'pb', pb, 'product', pf[0]*pb[0], (pf[0]+pf[1])*(pb[0]+pb[1]))
