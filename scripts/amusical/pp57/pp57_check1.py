from pp57 import *
import sys
f = PP(int(sys.argv[1]))
# Omega_0: v5(x)=A odd, 7 !| x, x = 8^{-A} mod 19 ; check engine forever (200 steps)
tot=surv=0
for x in range(-200000, 200000):
    if x == 0: continue
    A = vp(x,5)
    if A % 2 == 1 and x % 7 and (x * pow(8, A, 19)) % 19 == 1:
        tot += 1; y = x; ok = True
        for _ in range(150):
            if not f.is_engine(y): ok = False; break
            y = f(y)
        surv += ok
print("Omega_0 points:", tot, "engine for 150 steps:", surv)
# also: a leaking sample: A even
tot=surv=0
for x in range(1, 200000):
    A = vp(x,5)
    if A >= 1 and A % 2 == 0 and x % 7 and (x * pow(8, A, 19)) % 19 == 1:
        tot += 1; y = x; ok = True
        for _ in range(150):
            if not f.is_engine(y): ok = False; break
            y = f(y)
        surv += ok
print("A even control:", tot, "engine for 150 steps:", surv)
