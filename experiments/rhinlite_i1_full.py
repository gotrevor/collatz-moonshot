import math
def logkernel(x):
    f=[abs(x-3),abs(x-2),abs(x-4),abs(5*x-12),abs(17*x**2-102*x+144),abs(19*x**2-108*x+144)]
    w=[705,551,449,109,39,54]
    return sum(wi*math.log(fi) for wi,fi in zip(w,f))
def phi2_over_x(x):
    lp=2*(logkernel(x)-1000*math.log(x))-math.log(x)
    return lp   # log of integrand
# integrate exp(lp) over [2,3] with fine grid, factoring out peak
N=200000
xs=[2+ (1.0/N)*i for i in range(N+1)]
lps=[]
for x in xs:
    try: lps.append(phi2_over_x(x))
    except: lps.append(-1e18)
M=max(lps)
# trapezoid on exp(lp-M)
h=1.0/N
s=0.0
for i in range(N):
    a=math.exp(lps[i]-M) if lps[i]>-1e17 else 0
    b=math.exp(lps[i+1]-M) if lps[i+1]>-1e17 else 0
    s+=0.5*(a+b)*h
logI1=M+math.log(s)
logkappa=2000*math.log(2209/10000)
logtarget=math.log(2)+logkappa+math.log(3/2)
print("logI1(1)=",logI1)
print("logtarget=",logtarget)
print("logI1 - logtarget =",logI1-logtarget," ratio=",math.exp(logI1-logtarget))
