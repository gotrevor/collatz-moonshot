#!/usr/bin/env python3
"""Laplace constants for the integral-det node (float precision; O(1) quantities).

g_N = H_N/x^N = exp(t*psi(x)),  N=2000t,
psi(x) = 2*705 log|x-3| + 2*551 log|x-2| + 2*449 log|x-4|
       + 2*109 log|5x-12| + 2*39 log|17x^2-102x+144| + 2*54 log|19x^2-108x+144| - 2000 log x.
Two equal global maxima (one in (2,3), one in (3,4)) => I1,I2 share leading rate,
rho_inf = I1/I2 = (x2*/x1*) sqrt(psi''(x2*)/psi''(x1*)).
"""
import math
def psi(x):
    return (2*705*math.log(abs(x-3)) + 2*551*math.log(abs(x-2)) + 2*449*math.log(abs(x-4))
            + 2*109*math.log(abs(5*x-12)) + 2*39*math.log(abs(17*x*x-102*x+144))
            + 2*54*math.log(abs(19*x*x-108*x+144)) - 2000*math.log(x))
def dpsi(x):
    return (2*705/(x-3) + 2*551/(x-2) + 2*449/(x-4) + 2*109*5/(5*x-12)
            + 2*39*(34*x-102)/(17*x*x-102*x+144) + 2*54*(38*x-108)/(19*x*x-108*x+144)
            - 2000/x)
def d2psi(x,h=1e-6):
    return (dpsi(x+h)-dpsi(x-h))/(2*h)
def newton(f,x0,it=80):
    x=x0
    for _ in range(it):
        d=(f(x+1e-7)-f(x-1e-7))/2e-7
        x=x-f(x)/d
    return x
target=2000*math.log(9/40)
print("target psi_max = 2000*log(9/40) =", target)
x1=newton(dpsi,2.5); x2=newton(dpsi,3.5)
for nm,xs in (("x1* in (2,3)",x1),("x2* in (3,4)",x2)):
    print(f"{nm} = {xs:.12f}  psi={psi(xs):.10f}  psi''={d2psi(xs):.6f}")
c1=d2psi(x1); c2=d2psi(x2)
print("psi(x1*)-psi(x2*) =", psi(x1)-psi(x2), " (should be ~0: two equal maxima)")
rho_inf=(x2/x1)*math.sqrt(c2/c1)
print("rho_inf = I1/I2 (leading Laplace) =", f"{rho_inf:.12f}")
print("  cf log(3/2)/log(4/3) =", math.log(1.5)/math.log(4/3))

# grid-scan to confirm the interior critical point is the GLOBAL max on each interval
def scan(lo,hi,n=200000):
    best=(-1e18,None)
    for i in range(1,n):
        x=lo+(hi-lo)*i/n
        v=psi(x)
        if v>best[0]: best=(v,x)
    return best
m1=scan(2.0001,2.9999); m2=scan(3.0001,3.9999)
print("GLOBAL max on [2,3]:", f"psi={m1[0]:.6f} at x={m1[1]:.6f}")
print("GLOBAL max on [3,4]:", f"psi={m2[0]:.6f} at x={m2[1]:.6f}")
print("gap m1-m2 =", m1[0]-m2[0], " (>0 => I1 rate > I2 rate; clean dominance)")
# central-coeff rate gamma per t (c_N ~ exp(t*gamma)); c_N in [17^N,18^N], N=2000t
import math as _m
print("gamma range per t: [2000*log17, 2000*log18] =",2000*_m.log(17),2000*_m.log(18))
print("dominance margins: gamma-m1 =", 2000*_m.log(17)-m1[0], " (c2 M01 vs c1 M02)")
