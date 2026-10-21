#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Exact: bias_j = sum_{odd xi mod 2^(j+1)} G_j(xi) * D(xi),  D(xi) = sum_{r<2^j} e(-xi r/2^(j+1)), |D| = 1/sin(pi xi/2^(j+1)).
# So |bias_j|/2^j <= W_j := 2^-j sum_odd |G_j(xi)| / sin(pi xi / 2^(j+1)).  Compare W_j with |bias_j|/2^j, and split W_j
# into the powers-of-3 chain, the 13*3^k chain, and the rest.
import numpy as np, sys
for j in [int(x) for x in sys.argv[1:]]:
    M=2**(j+1); N=2**j
    a=np.arange(M,dtype=np.int64)
    for _ in range(j): a=np.where(a&1==1,(3*a+1)>>1,a>>1)
    g=(1-2*(a&1)).astype(float); Gh=np.fft.ifft(g)
    xi=np.arange(1,M,2); w=1/np.sin(np.pi*xi/M); A=np.abs(Gh[xi])
    D=np.exp(-2j*np.pi*np.outer([0],[0]))  # placeholder
    bias=g[:N].sum(); recon=np.real(np.sum(Gh[xi]*(1-np.exp(-1j*np.pi*xi))/(1-np.exp(-2j*np.pi*xi/M))))
    W=(A*w).sum()/N
    def chain(c):
        s=set()
        k=0
        while c*3**k<M: s.add(c*3**k%M); s.add((-c*3**k)%M); k+=1
        return np.array([x in s for x in xi])
    c3=chain(1); c13=chain(13)
    print(f"j={j:2d}: bias/2^j={bias/N:+.2e} (recon {recon/N:+.2e});  W_j={W:.4f};  3^k-chain {(A*w)[c3].sum()/N:.4f}, 13*3^k-chain {(A*w)[c13].sum()/N:.4f}, rest {(A*w)[~c3&~c13].sum()/N:.4f};  W_j*2^(j/2)/j={W*2**(j/2)/j:.3f}", flush=True)
