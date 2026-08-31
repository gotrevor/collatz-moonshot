import math
W=[705,551,449,109,39,54]
def factors(x):
    return [x-3,x-2,x-4,5*x-12,17*x**2-102*x+144,19*x**2-108*x+144]
def facmin(a,b,i,sub=40):
    return min(abs(factors(a+(b-a)*t/sub)[i]) for t in range(sub+1))
# certificate uses: per window contribution >= (Lk^2/b^2000)*loglow, loglow=(b-a)/b
logkappa=2000*math.log(2209/10000)
# target uses I1(0)=log(3/2); to be rigorous RHS side uses upper bound of log(3/2). Use loguphalf=0.4055 (true) for feasibility check first
def certmargin(edges, loglow_true=False, log32=math.log(1.5)):
    C=3020.0; tot=0.0
    for a,b in zip(edges,edges[1:]):
        logL=sum(w*math.log(facmin(a,b,i)) for i,w in enumerate(W))
        loglow = math.log(b/a) if loglow_true else (b-a)/b
        if loglow<=0: continue
        contriblog=2*logL-2000*math.log(b)+math.log(loglow)
        tot+=math.exp(contriblog+C)
    lhslog=math.log(tot)-C
    rhslog=math.log(2)+logkappa+math.log(log32)
    return lhslog-rhslog
for n in [400,800,1600,3200]:
    A,B=2.16,2.25
    edges=[A+(B-A)*k/n for k in range(n+1)]
    m1=certmargin(edges,loglow_true=False)
    print(f"n={n} factored+(b-a)/b margin={m1:+.4f}")
