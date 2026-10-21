#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Digit-parity bias of the 3x+1 conjugacy: b_j = 2^{-j} sum_{r<2^j} (-1)^{T^j(r)}.

T(n) = n/2 (even), (3n+1)/2 (odd).  Also conditional biases with the top bit fixed,
and the full joint law of the next L feedback bits beyond the Terras range.
"""
import numpy as np, sys

def iterate(r, steps):
    r = r.astype(np.uint64).copy()
    for _ in range(steps):
        odd = (r & 1).astype(bool)
        r = np.where(odd, (3*r+1)>>1, r>>1)
    return r

def main():
    J = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    print("j  b_j  b_j*2^{j/2}  b_j^{1/j}   | cond top=1: bias of f_j given eps_{j-1}=1 | f_j given eps_{j-1}=0")
    for j in range(1, J+1):
        r = np.arange(2**j, dtype=np.uint64)
        y = iterate(r, j)
        par = (y & 1).astype(np.int64)
        s = 1 - 2*par
        b = s.mean()
        half = 2**(j-1)
        b1 = s[half:].mean(); b0 = s[:half].mean()
        print(f"{j:2d} {b:+.6f} {b*2**(j/2):+.4f} {abs(b)**(1/j):.4f} | {b1:+.6f} | {b0:+.6f}")

if __name__ == "__main__":
    main()
