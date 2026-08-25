#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Reproduce Rhin's linear-independence measure for (1, log 2, log 3) from the
Wu (Math. Comp. 72 (2003) 901-911, Thm 2) framework.

H_n(x) = prod_i Q_i(x)^{b_i n},   I_n(a_i,a_{i+1}) = int_{a_i}^{a_{i+1}} H_n(x)/x^n dx/x
D_n = lcm(1..max(n, deg H_n - n)),  K = lim (1/n) log D_n = max(1, deg - 1)
tau_i = -max_{[a_i,a_{i+1}]} g,  tau_0 = min_rho max_{|z|=rho} g,  g = sum b_i log|Q_i| - log|z|
mu = (tau_0 + K) / (tau - K)
"""
import numpy as np
from scipy.optimize import differential_evolution

# Rhin's factors, as reported in Wu 2003 eq. (1.4)
QS = [np.array([1.0, -2.0]),              # x - 2
      np.array([1.0, -3.0]),              # x - 3
      np.array([1.0, -4.0]),              # x - 4
      np.array([5.0, -12.0]),             # 5x - 12
      np.array([17.0, -102.0, 144.0]),    # 17x^2 - 102x + 144
      np.array([19.0, -104.0, 144.0])]    # 19x^2 - 104x + 144
DEGS = np.array([len(q) - 1 for q in QS], dtype=float)

def g_real(b, x):
    s = -np.log(np.abs(x))
    for bi, q in zip(b, QS):
        if bi == 0:
            continue
        v = np.abs(np.polyval(q, x))
        s = s + bi * np.log(np.maximum(v, 1e-300))
    return s

def g_cplx(b, z):
    s = -np.log(np.abs(z))
    for bi, q in zip(b, QS):
        if bi == 0:
            continue
        s = s + bi * np.log(np.maximum(np.abs(np.polyval(q, z)), 1e-300))
    return s

XS12 = np.linspace(2.0, 3.0, 20001)[1:-1]
XS23 = np.linspace(3.0, 4.0, 20001)[1:-1]
TH   = np.linspace(0, 2*np.pi, 2001)
RHOS = np.exp(np.linspace(np.log(0.02), np.log(60.0), 900))

def mu_of(b):
    b = np.asarray(b, dtype=float)
    deg = float(np.dot(b, DEGS))
    K = max(1.0, deg - 1.0)
    t1 = -np.max(g_real(b, XS12))
    t2 = -np.max(g_real(b, XS23))
    tau = min(t1, t2)
    if not np.isfinite(tau) or tau <= K:
        return np.inf, dict(K=K, tau=tau, tau0=np.nan, deg=deg, t1=t1, t2=t2)
    Z = RHOS[:, None] * np.exp(1j * TH)[None, :]
    tau0 = float(np.min(np.max(g_cplx(b, Z), axis=1)))
    mu = (tau0 + K) / (tau - K)
    return mu, dict(K=K, tau=tau, tau0=tau0, deg=deg, t1=t1, t2=t2)

def obj(b):
    return mu_of(b)[0]

if __name__ == "__main__":
    res = differential_evolution(obj, [(0, 3)] * 6, seed=1, maxiter=400,
                                 popsize=40, tol=1e-10, polish=True)
    mu, info = mu_of(res.x)
    print("b =", np.round(res.x, 6))
    print("mu = %.6f" % mu)
    print({k: round(float(v), 6) for k, v in info.items()})
    # sanity: plain (x-2)^n (x-3)^n (x-4)^n
    print("plain (1,1,1,0,0,0):", mu_of([1, 1, 1, 0, 0, 0]))
