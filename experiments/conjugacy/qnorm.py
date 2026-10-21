#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Does the 3x+1 conjugacy preserve normality?  Q(x) = parity word of the T-orbit of the 2-adic
integer x; Q^{-1}(w) = 2-adic integer with parity word w.  Feed structured inputs, measure block
frequencies of the output (max relative deviation over all blocks of length L), vs iid control."""
import sys, random, math
from collections import Counter
M = int(sys.argv[1]) if len(sys.argv) > 1 else 40000
random.seed(1)

def thue_morse(M): return [bin(i).count('1') & 1 for i in range(M)]
def period_doubling(M):
    # pd_n = v2(n+1) mod 2
    out=[]
    for n in range(M):
        k=n+1; v=0
        while k%2==0: k//=2; v+=1
        out.append(v&1)
    return out
def fibonacci_word(M):
    phi=(1+5**0.5)/2
    return [int(math.floor((n+2)*phi)-math.floor((n+1)*phi))-1 for n in range(M)]
def champernowne(M):
    s=''; i=1
    while len(s)<M: s+=bin(i)[2:]; i+=1
    return [int(c) for c in s[:M]]
def golden_random(M):
    out=[]; prev=0
    while len(out)<M:
        if prev==1: out.append(0); prev=0
        else:
            b = 1 if random.random() < 1/(1+(1+5**0.5)/2) else 0  # Parry measure: P(1|0)=1/phi^2? use 1/phi: 0.618 -> P(1)=0.382
            out.append(b); prev=b
    return out[:M]
def iid(M): return [random.getrandbits(1) for _ in range(M)]
def biased(M,p=1/3): return [1 if random.random()<p else 0 for _ in range(M)]

def Q(eps):
    """parity word of the 2-adic integer with digits eps (length M), first M letters exact."""
    M=len(eps); x=0
    for i,e in enumerate(eps): x |= e<<i
    mod=(1<<M)-1  # we only need x mod 2^M; T^k mod 2^{M-k} is exact
    w=[]
    for k in range(M):
        w.append(x&1)
        x = (3*x+1)>>1 if x&1 else x>>1
    return w
def Qinv(w):
    """2-adic digits eps_j = w_j xor parity(T^j(x mod 2^j)) built incrementally: x_{j+1} = x_j + eps_j 2^j."""
    M=len(w); x=0; eps=[]
    # maintain y_j = T^j(x_j) exactly via (3^a x + N)/2^j; cheaper: recompute parity via the identity
    # T^j(x_j + 2^j) = T^j(x_j) + 3^{a_j}.  Keep y = T^j(x_j), a = #odd among w_0..w_{j-1}.
    y=0; p3=1
    for j in range(M):
        f = y & 1               # parity of T^j(x mod 2^j)
        e = w[j] ^ f; eps.append(e)
        if e: y += p3           # x_j += 2^j  =>  T^j shifts by 3^{a_j}
        # now y = T^j(x_{j+1}), parity = w_j
        assert (y&1)==w[j]
        if y&1: y=(3*y+1)>>1; p3*=3
        else: y>>=1
    return eps

def maxdev(seq, Lmax=10):
    rows=[]
    s=''.join(map(str,seq)); n=len(s)
    for L in range(1,Lmax+1):
        c=Counter(s[i:i+L] for i in range(n-L+1)); tot=n-L+1; exp=tot/2**L
        dev=max(abs(c.get(format(b,'0%db'%L),0)-exp)/exp for b in range(2**L))
        rows.append(dev)
    return rows
def report(name, seq):
    d=maxdev(seq)
    print(f"{name:28s} ones={sum(seq)/len(seq):.4f} maxreldev L=1..10: "+' '.join(f"{x:.3f}" for x in d))

inputs = {"iid":iid(M), "biased(1/3)":biased(M), "thue-morse":thue_morse(M), "period-doubling":period_doubling(M),
          "fibonacci(sturmian)":fibonacci_word(M), "champernowne":champernowne(M), "golden-random(no 11)":golden_random(M)}
print(f"M={M}\n== inputs themselves ==")
for k,v in inputs.items(): report(k, v)
print("== Q(x): parity word of x with these binary digits ==")
for k,v in inputs.items(): report("Q("+k+")", Q(v))
print("== Q^{-1}(w): binary digits of the 2-adic integer with this parity word ==")
for k,v in inputs.items(): report("Qinv("+k+")", Qinv(v))
