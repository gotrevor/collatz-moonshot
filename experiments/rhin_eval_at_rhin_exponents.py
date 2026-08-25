#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Evaluate Wu (2003) Thm 2's mu at Rhin's ACTUAL exponents (Zudilin, arXiv:math/0404523 §3.4)."""
import importlib.util
BASE = "/Users/gotrevor/src/collatz-moonshot/experiments"
spec = importlib.util.spec_from_file_location("rhinmod", BASE + "/rhin_mu_wu_framework.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

# Zudilin 3.4 (z-scale)  ->  Wu 1.4 (x = 3z) factor identification:
#   (z-1) <-> Q2 = x-3 ; (z-2/3) <-> Q1 = x-2 ; (z-4/3) <-> Q3 = x-4
#   (5z-4) <-> Q4 = 5x-12 ; (17z^2-34z+16) <-> Q5 ; (19z^2-36z+16) <-> Q6
b = [0.552418, 0.704324, 0.447582, 0.109072, 0.038934, 0.054368]
deg = sum(bi*d for bi, d in zip(b, mod.DEGS))
print("sum b_i * deg Q_i =", round(deg, 9), " (Zudilin: deg H_n <= 2n)")
mu, info = mod.mu_of(b)
print("mu  =", round(float(mu), 5))
print({k: round(float(v), 6) for k, v in info.items()})
print("\nRhin published: nu(1,log2,log3) < 7.616 ; mu(gamma) < 8.616 for gamma in Qlog2+Qlog3")
