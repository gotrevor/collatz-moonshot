#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Twisted characteristic function of Tao's Syracuse variable.
X_n = sum_{k=1}^n 3^{k-1} 2^{-T_k} mod 3^n, T_k partial sums of iid Geom(p) gaps (P(g) = (1-p)^{g-1} p, p = 1/2 is Tao).
phi_n(xi, th) = E e(xi X_n / 3^n + th T_n).  Exact recursion (Tao Lemma 1.12 + the twist):
   phi_n(xi, th) = sum_g P(g) e(th g) e(xi 2^{-g} / 3^n) phi_{n-1}(xi 2^{-g} mod 3^{n-1}, th).
Control: th = 0 must reproduce Tao's untwisted decay (sup over xi prime to 3 decreasing in n).
Prints, per n: sup_{xi prime to 3} |phi_n| at th = 0, and the sup over a th-grid (and the maximizing th)."""
import sys, numpy as np
nmax = int(sys.argv[1]); p = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5
G = 60; ths = np.linspace(0, 1, 97, endpoint=False)
P = np.array([(1-p)**(g-1)*p for g in range(1, G+1)])
def inv2pow(g, M): return pow(pow(2, g, M), -1, M)
phi = np.ones((len(ths), 1), dtype=complex)              # level 0: X_0 = 0, T_0 = 0
for n in range(1, nmax+1):
    M = 3**n; xi = np.arange(M); new = np.zeros((len(ths), M), dtype=complex)
    for gi, g in enumerate(range(1, G+1)):
        u = inv2pow(g, M); x2 = (xi * u) % M
        inner = phi[:, x2 % (3**(n-1))] if n > 1 else phi[:, np.zeros(M, dtype=int)]
        new += P[gi] * np.exp(2j*np.pi*ths*g)[:, None] * np.exp(2j*np.pi*x2/M)[None, :] * inner
    phi = new
    unit = (xi % 3) != 0
    s0 = np.abs(phi[0, unit]).max(); allabs = np.abs(phi[:, unit]); k = np.unravel_index(allabs.argmax(), allabs.shape)
    print(f"n={n:2d}  sup|phi| th=0: {s0:.4f}   sup over th: {allabs.max():.4f} at th={ths[k[0]]:.4f}, xi={xi[unit][k[1]]}")
