import math
def logkernel(x):
    f=[abs(x-3),abs(x-2),abs(x-4),abs(5*x-12),abs(17*x**2-102*x+144),abs(19*x**2-108*x+144)]
    w=[705,551,449,109,39,54]
    return sum(wi*math.log(fi) for wi,fi in zip(w,f))
def logphi2(x): return 2*(logkernel(x)-1000*math.log(x))
def safe(x):
    try: return logphi2(x)
    except: return -1e18
logkappa=2000*math.log(2209/10000)
logtarget=math.log(2)+logkappa+math.log(math.log(3/2))
C=3020.0
def lowersum(A,B,n,sub=400):
    total=0.0
    for k in range(n):
        a=A+(B-A)*k/n; b=A+(B-A)*(k+1)/n
        mn=min(safe(a+(b-a)*t/sub) for t in range(sub+1))
        if mn< -1e17: continue
        total+=math.exp(mn+C)*math.log(b/a)
    return (math.log(total)-C) if total>0 else -1e18
print("logtarget=",logtarget)
for (A,B) in [(2.14,2.27),(2.15,2.26),(2.16,2.25)]:
    for n in [20,50,100,200,400,800]:
        ls=lowersum(A,B,n)
        print(f"[{A},{B}] n={n} margin={ls-logtarget:+.4f}")
    print()
