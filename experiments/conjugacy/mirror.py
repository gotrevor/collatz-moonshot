#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# The 2-adic mirror of Tao's Syracuse variable.
# Tao: X_n = sum_{k=1}^n 3^(k-1) 2^(-T_k) in Z/3^n, T_k partial sums of iid Geom(2).
# Ours (Digits.lean): for the j-letter word of r < 2^j with odd-step times t_1 < ... < t_a,
#   Y = sum_i 3^(-i) 2^(t_i) in Z/2^(j+1);  Terras: Y mod 2^j is uniform; bias j = 1 + sum_{u != 0} (-1)^(1+digit_j Y).
# Checks: (1) the digit form reproduces bias j;  (2) Y mod 2^j is a bijection;  (3) the mirror of Tao's Prop 1.17:
#   phi_j(xi) = 2^-j sum_r e(xi Y_r / 2^(j+1)) for odd xi.  BiasDecays follows if sup_odd |phi_j| = o(1/j)
#   (square-wave expansion of the top digit; weight sum ~ (2/pi) ln 2^(j+1)).  Report sup, sup * 2^(j/2), sup * j,
#   and the square-wave reconstruction of the bias.
import numpy as np, sys
for j in [int(x) for x in sys.argv[1:]]:
    M=2**(j+1); N=2**j; inv3=pow(3,-1,M)
    r=np.arange(N,dtype=np.int64); a=r.copy(); Y=np.zeros(N,np.int64); cnt=np.zeros(N,np.int64)
    p3=np.ones(N,np.int64)  # 3^(-i) for the next odd step
    for t in range(j):
        odd=(a&1)==1
        cnt+=odd; p3=np.where(odd,(p3*inv3)%M,p3)
        Y=np.where(odd,(Y+p3*pow(2,t,M))%M,Y)
        a=np.where(odd,(3*a+1)>>1,a>>1)
    E=int((1-2*(a&1)).sum())
    digit=(Y>>j)&1; nz=r!=0
    Edig=1+int(np.where(digit[nz]==1,1,-1).sum())   # (-1)^(1+digit)
    bij=len(np.unique(Y%N))==N
    h=np.bincount(Y,minlength=M).astype(float)/N
    phi=np.fft.fft(h)            # phi[xi] = sum_x h(x) e(-xi x / M); |.| same as e(+)
    odd=np.abs(phi[1::2]); s=odd.max(); xi=2*int(odd.argmax())+1; xi=min(xi,M-xi)
    even_max=np.abs(phi[2::2][:N//2-1]).max() if N>2 else 0.0
    # square wave (-1)^{digit_j} reconstruction: E[(-1)^{digit}] = sum_xi hat_sq(xi) phi(xi)
    sq=np.where((np.arange(M)>>j)&1==1,-1.0,1.0); sqh=np.fft.fft(sq)/M
    recon=float(np.real(np.sum(np.conj(sqh)*phi)))  # Parseval-type: sum_x sq(x) h(x)
    print(f"j={j:2d}: E_j={E} digit-form={Edig} {'OK' if E==Edig else 'MISMATCH'}; Y mod 2^j bijective={bij}; "
          f"max|phi| over even xi != 0 = {even_max:.1e}; sup_odd|phi|={s:.5f} at xi={xi}; sup*2^(j/2)={s*2**(j/2):.2f}; sup*j={s*j:.4f}; "
          f"E[(-1)^digit] direct={float((1-2*digit).mean()):+.6f} via characters={recon:+.6f}", flush=True)
