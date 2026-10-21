#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Fourier transform of the beyond-Terras sign g_j(r) = (-1)^{T^j r} on Z/2^(j+1) (g_j is 2^j-antiperiodic,
# so G_j lives on odd xi):  G_j(xi) = 2^-(j+1) sum_{r mod 2^(j+1)} g_j(r) e(xi r / 2^(j+1)).
# Claimed exact recursion (from g_j(2s) = g_{j-1}(s), g_j(2s+1) = g_{j-1}(3s+2), u = 3^-1 mod 2^(j+1)):
#   G_j(xi) = 1/2 [ G_{j-1}(xi mod 2^j) + e(xi (1-4u) / 2^(j+1)) G_{j-1}(u xi mod 2^j) ].
# For xi = 3^k (k >= 1) the phase is e(-3^(k-1)/2^(j+1)) ~ 1 and u xi = 3^(k-1): a coherent chain.
# Report: max recursion error; |G_j(3^k)| for k = 0..; median |G_j| over odd xi; sup over odd xi and where.
import numpy as np, sys
def gseq(j):
    a=np.arange(2**(j+1),dtype=np.int64)
    for _ in range(j): a=np.where(a&1==1,(3*a+1)>>1,a>>1)
    return (1-2*(a&1)).astype(float)
def G(j):
    g=gseq(j); M=2**(j+1); return np.fft.ifft(g)  # ifft: (1/M) sum g(r) e(+xi r/M)
J=int(sys.argv[1])
Gs={j:G(j) for j in range(1,J+1)}
for j in range(2,J+1):
    M=2**(j+1); u=pow(3,-1,M); xi=np.arange(1,M,2)
    lhs=Gs[j][xi]
    rhs=0.5*(Gs[j-1][xi%(M//2)]+np.exp(2j*np.pi*(xi*((1-4*u)%M)%M)/M)*Gs[j-1][(u*xi)%(M//2)])
    err=np.abs(lhs-rhs).max()
    if j in (2,3,8,J) or err>1e-9: print(f"j={j}: max |G_j - recursion| = {err:.2e}")
for j in (J-4,J-2,J):
    M=2**(j+1); xi=np.arange(1,M,2); A=np.abs(Gs[j][xi]); k_s=[]; 
    k=0
    while 3**k<M//2: k_s.append(k); k+=1
    pw=" ".join(f"{np.abs(Gs[j][3**k]):.4f}" for k in k_s)
    i=int(A.argmax()); x=int(xi[i]); x=min(x,M-x)
    print(f"j={j}: |G_j(3^k)| k=0..{k_s[-1]}: {pw}")
    print(f"       median |G_j| over odd xi = {np.median(A):.2e} (2^(-j/2) = {2**(-j/2):.2e});  sup = {A.max():.4f} at |xi| = {x} (3-power: {any(x==3**k for k in k_s)});  sup*j = {A.max()*j:.3f}")
    top=np.argsort(-A)[:12]; print("       top-12 |xi|: "+", ".join(str(min(int(xi[t]),M-int(xi[t]))) for t in top))
