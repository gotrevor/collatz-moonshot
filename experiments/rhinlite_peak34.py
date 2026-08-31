import math
W=[705,551,449,109,39,54]
def factors(x): return [x-3,x-2,x-4,5*x-12,17*x**2-102*x+144,19*x**2-108*x+144]
def logphi(x):  # log of kernelAbs/x^1000
    return sum(w*math.log(abs(f)) for w,f in zip(W,factors(x)))-1000*math.log(x)
def safe(x):
    try: return logphi(x)
    except: return -1e18
# peak of phi on [3,4]
xs=[3+0.0002*i for i in range(1,5000)]
b=max(xs,key=safe)
print("[3,4] peak x=",b,"logphi=",safe(b),"phi=(base)=",math.exp(safe(b)/1000))
# base such that base^1000 = phi_peak: base=exp(logphi/1000)
print("required base >=",math.exp(safe(b)/1000))
print("current base 0.2209; peak base=",round(math.exp(safe(b)/1000),6))
# I1 base margin as function of base
logI1=-3020.0081463344245
log32log=math.log(math.log(1.5))
for base in [0.2209,0.2206,0.2205,0.22045,0.2204]:
    log2k=math.log(2)+2000*math.log(base)
    margin=logI1-(log2k+log32log)
    print(f"base={base} I1margin={margin:+.3f} ratio={math.exp(margin):.2f} I2ok={base>math.exp(safe(b)/1000)}")
