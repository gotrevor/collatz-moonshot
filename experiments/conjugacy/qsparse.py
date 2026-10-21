#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Sparse (Liouville-type) rung of the ladder: Q and Q^{-1} on zero-density inputs
sum 2^(n^2) (not automatic) and sum 2^(2^n) (2-automatic), plus the primes' characteristic word."""
import sys, importlib.util, math
spec=importlib.util.spec_from_file_location("qnorm", __file__.replace("qsparse.py","qnorm_lib.py"))
M = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
# reuse Q, Qinv, maxdev from qnorm.py by exec of its function defs only
src=open(__file__.replace("qsparse.py","qnorm.py")).read().split("inputs = {")[0]
ns={}; exec(src.replace("M = int(sys.argv[1]) if len(sys.argv) > 1 else 40000","M=%d"%M), ns)
Q,Qinv,maxdev=ns['Q'],ns['Qinv'],ns['maxdev']
def report(name, seq):
    d=maxdev(seq); print(f"{name:26s} ones={sum(seq)/len(seq):.4f} maxreldev L=1..10: "+' '.join(f"{x:.3f}" for x in d), flush=True)
squares=[1 if int(math.isqrt(n))**2==n else 0 for n in range(M)]
pow2=[1 if n>0 and (n&(n-1))==0 else 0 for n in range(M)]
sieve=bytearray([1])*M; sieve[0]=sieve[1]=0
for i in range(2,int(M**0.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
primes=list(sieve)
inputs={"squares 2^(n^2)":squares, "powers 2^(2^n)":pow2, "primes":primes}
print(f"M={M}")
for k,v in inputs.items(): report(k, v)
print("== Q(x) ==")
for k,v in inputs.items(): report("Q("+k+")", Q(v))
print("== Qinv(w) ==")
for k,v in inputs.items(): report("Qinv("+k+")", Qinv(v))
print("== iid control ==")
report("iid", ns['iid'](M))
