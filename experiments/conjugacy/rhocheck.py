#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Instrument check for 10.3d: the mean square of the conditional bias of the beyond-Terras letter given the first
# j-m letters equals 2^-(j+m) sum_c (sum_{r = c mod 2^(j-m), r < 2^j} g(r))^2, and expanding the square,
# rho_j(m) := 2^m * (that) = 1 + 2 sum_{i=1}^{2^m-1} A_j(i 2^(j-m)),  A_j(d) = 2^-j sum_{r < 2^j - d} g(r) g(r+d).
# Compare the direct cylinder variance with the autocorrelation sum, and print A_j at the dyadic spacings.
import numpy as np, sys
j=int(sys.argv[1]); N=2**j
a=np.arange(N,dtype=np.int64)
for _ in range(j): a=np.where(a&1==1,(3*a+1)>>1,a>>1)
g=(1-2*(a&1)).astype(np.float64)
print(f"j={j}:  m   rho_direct   1+2*sum A   A_j(2^(j-m))   A_j(2*2^(j-m))   A_j(3*2^(j-m))")
for m in range(1,9):
    step=2**(j-m); cyl=g.reshape(2**m, step).sum(axis=0)       # row i = residues c + i*step -> sum over i per c
    rho_direct=(cyl**2).mean()/2**m
    A=lambda d: ((g[:N-d]*g[d:]).sum()/N if d<N else 0.0)
    s=sum(A(i*step) for i in range(1,2**m))
    print(f"       {m}   {rho_direct:.4f}       {1+2*s:.4f}      {A(step):+.4f}        {A(2*step):+.4f}          {A(3*step):+.4f}")
