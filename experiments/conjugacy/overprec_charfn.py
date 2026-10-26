# Over-precision slice character sums for C1+ scoping.
# N_v = sum_{i=1}^a 3^(a-i) 2^(t_i), t_1<...<t_a in [0,j).  Twisting the start class r mod 3^k
# needs F_k'(zeta) = E_v e(zeta N_v / 3^(a+k')), 3 !| zeta, k' >= 1 (k' = 0 is the usual slice sum).
# Exact DP over times: factor for the i-th odd time t is e(zeta 2^t / 3^(i+k')).
import cmath, math, sys
from fractions import Fraction
def F(j, a, zeta, kp):
    S = [0j]*(a+1); S[0] = 1+0j
    for t in range(j):
        p2 = pow(2, t)
        for i in range(min(a, t+1), 0, -1):
            M = 3**(i+kp)
            ph = cmath.exp(2j*math.pi*float(Fraction((zeta*p2) % M, M)))
            S[i] += S[i-1]*ph
    return abs(S[a])/math.comb(j, a)
# control: brute force at small j against actual Collatz starts, k'=0 and k'=1
def tstep(n): return n//2 if n % 2 == 0 else (3*n+1)//2
def brute(j, a, zeta, kp):
    tot = 0j; cnt = 0
    for r in range(2**j):
        x = r; ts = []
        for t in range(j):
            if x % 2: ts.append(t)
            x = tstep(x)
        if len(ts) != a: continue
        N = sum(3**(a-i-1)*2**ts[i] for i in range(a))
        assert 2**j*x == 3**a*r + N
        tot += cmath.exp(2j*math.pi*float(Fraction((zeta*N) % 3**(a+kp), 3**(a+kp)))); cnt += 1
    return abs(tot)/cnt
for (j,a,z,kp) in [(12,5,1,0),(12,5,1,1),(14,6,5,2)]:
    print('control', j,a,z,kp, round(brute(j,a,z,kp),10), round(F(j,a,z,kp),10))
for frac in (0.3, 0.45, 0.55):
    for j in (20, 40, 80, 160, 320):
        a = round(frac*j)
        row = [max(F(j,a,z,kp) for z in (1,2,5,7,11)) for kp in (0,1,2,3)]
        print(f'a/j={frac} j={j:4d} a={a:3d}  ' + '  '.join(f"k'={kp}:{v:.2e}" for kp,v in enumerate(row)))
    sys.stdout.flush()
