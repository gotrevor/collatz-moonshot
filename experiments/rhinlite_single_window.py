import math
W=[705,551,449,109,39,54]
def factors(x): return [x-3,x-2,x-4,5*x-12,17*x**2-102*x+144,19*x**2-108*x+144]
def facmin(a,b,i,sub=200): return min(abs(factors(a+(b-a)*t/sub)[i]) for t in range(sub+1))
def window_contrib_log(a,b):
    # (Lk/b^1000)^2 * log(b/a) lower bound, log-space; use log(b/a)>=(b-a)/b (rational-friendly)
    logL=sum(w*math.log(facmin(a,b,i)) for i,w in enumerate(W))
    loglow=(b-a)/b
    return 2*logL-2000*math.log(b)+math.log(loglow)
# search best single window between roots 2.136 and 2.272
best=None
for a in [2.14+0.002*i for i in range(60)]:
    for b in [a+0.002*j for j in range(1,60)]:
        if b>2.271: continue
        c=window_contrib_log(a,b)
        if best is None or c>best[0]: best=(c,a,b)
print("best single window (factored,(b-a)/b): logcontrib=",round(best[0],4)," a=",round(best[1],4)," b=",round(best[2],4))
for base in [0.2209,0.2207,0.2206,0.2205]:
    tgt=math.log(2)+2000*math.log(base)+math.log(math.log(1.5))
    print(f"  base={base}: target={tgt:.3f} margin={best[0]-tgt:+.3f} ratio={math.exp(best[0]-tgt):.2f}")
