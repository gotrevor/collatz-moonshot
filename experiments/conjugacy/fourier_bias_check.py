import sys, numpy as np
sys.path.insert(0, sys.argv[1])
from slice_charfn import slice_pmf
from math import comb, pi, log
def T(n): return n//2 if n%2==0 else (3*n+1)//2
# (1) identity: levelSign j a = sum_xi ghat(xi) F(xi), exact for small j
for j,a in [(8,3),(10,5),(12,6),(12,7)]:
    M=3**a; mass=slice_pmf(j,a)*comb(j,a)
    sign=sum(mass[y]*(1 if y%2==0 else -1) for y in range(M))
    brute=0
    for r in range(2**j):
        x=r; c=0
        for _ in range(j):
            c+=x%2; x=T(x)
        if c==a: brute+= 1 if x%2==0 else -1
    F=np.fft.fft(mass)                       # F[xi] = sum_y mass(y) e(-xi y/M)
    xi=np.arange(M); g=np.array([1 if y%2==0 else -1 for y in range(M)],float)
    ghat=np.fft.fft(g)/M                     # ghat[xi] = (1/M) sum_y g(y) e(-xi y/M)
    recon=(np.conj(ghat)*F).sum().real       # Parseval: sum_y g mass = sum_xi conj(ghat) F
    print(f"j={j} a={a}: levelSign brute={brute} via-mass={sign:.0f} fourier={recon:.6f}")
# (2) Dirichlet weight: sum |ghat| ~ (2/pi) log M, and level-k weight ~ 3^-k (a-k)
for a in (6,9,12):
    M=3**a; xi=np.arange(M); w=1/(M*np.abs(np.cos(pi*xi/M)))
    v=np.array([0 if x==0 else next(k for k in range(a+1) if x%3**(k+1)) for x in xi])
    lev=[w[(v==k)&(xi>0)].sum() for k in range(4)]
    print(f"a={a}: sum|ghat|={w.sum():.3f}  (2/pi)lnM={2/pi*log(M):.3f}  level k=0..3: "+" ".join(f"{x:.3f}" for x in lev))
