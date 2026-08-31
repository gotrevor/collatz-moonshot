import math
from fractions import Fraction as F
W=[705,551,449,109,39,54]
def factors(x):
    return [x-3,x-2,x-4,5*x-12,17*x**2-102*x+144,19*x**2-108*x+144]
def logphi2(x):
    fs=factors(x)
    return 2*(sum(w*math.log(abs(f)) for w,f in zip(W,fs))-1000*math.log(x))
logkappa=2000*math.log(2209/10000)
logtarget=math.log(2)+logkappa+math.log(math.log(3/2))
# factored per-window lower bound: min|f_i| over [a,b] via endpoint sampling (each factor monotone-ish)
def facmin(a,b,i,sub=50):
    return min(abs(factors(a+(b-a)*t/sub)[i]) for t in range(sub+1))
def window_logbound(a,b):
    # log of (L^2/b^2000)*log(b/a) with L=prod facmin^w
    logL=sum(w*math.log(facmin(a,b,i)) for i,w in enumerate(W))
    return 2*logL-2000*math.log(b)+math.log(math.log(b/a))
def certsum(edges):
    C=3020.0; tot=0.0
    for a,b in zip(edges,edges[1:]):
        lb=window_logbound(a,b)
        tot+=math.exp(lb+C)
    return math.log(tot)-C
# uniform partition of [2.16,2.25]
for n in [50,100,200,400]:
    A,B=2.16,2.25
    edges=[A+(B-A)*k/n for k in range(n+1)]
    print(f"factored n={n} margin={certsum(edges)-logtarget:+.4f}")
# try wider region with root-avoidance: only pieces not straddling roots(2.136,2.272,2.4)
