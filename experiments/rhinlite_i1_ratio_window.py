import math
def logkernel(x):
    f=[abs(x-3),abs(x-2),abs(x-4),abs(5*x-12),abs(17*x**2-102*x+144),abs(19*x**2-108*x+144)]
    w=[705,551,449,109,39,54]
    return sum(wi*math.log(fi) for wi,fi in zip(w,f))
def logphi2(x):
    return 2*(logkernel(x)-1000*math.log(x))
def safe(x):
    try: return logphi2(x)
    except: return -1e18
logkappa=2000*math.log(2209/10000)
logtarget=math.log(2)+logkappa+math.log(3/2)
print("logtarget(2k log3/2)=",logtarget)
xs=[2+0.0005*i for i in range(1,2000)]
best=max(xs,key=safe)
print("peak x~",best,"logphi2=",safe(best))
for x in [2.1,2.15,2.2,2.25,2.3,2.35,2.5,2.6,2.7]:
    print(x,round(safe(x),4))

# scan windows [a,b] in [2.0,3.0], score = min logphi2 over window + log(log(b/a))
grid=[2+0.002*i for i in range(1,500)]
vals={x:safe(x) for x in grid}
best=None
import math as m
for i in range(len(grid)):
    for j in range(i+1,len(grid)):
        a,b=grid[i],grid[j]
        # min over sampled points in [a,b]
        mn=min(vals[grid[k]] for k in range(i,j+1))
        if mn< -1e17: continue
        score=mn+m.log(m.log(b/a))
        if best is None or score>best[0]:
            best=(score,a,b,mn)
print("best window score=",best[0]," a=",round(best[1],4)," b=",round(best[2],4)," min=",best[3])
print("margin over target:",best[0]-logtarget)
