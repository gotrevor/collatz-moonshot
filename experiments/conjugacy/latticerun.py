#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Long-range runs of the lattice DP (latticedp.py; control there, error 2.6e-16 at j <= 18).

seq: log2|G_n(xi)| / n along n for fixed xi (one DP pass gives every level); seqs: a panel of xi.
chain N: sup over |k| <= N of |G_N(3^k)|, its argmax k/N, and sup * sqrt(N).
"""
import math
import random
import sys

from latticedp import lattice_levels


def seq(xi: int, top: int, step: int) -> None:
    g0, _ = lattice_levels(xi, top + 1, top)
    row = " ".join(f"{n}:{math.log2(abs(g0[n])) / n:.4f}" for n in range(step, top + 1, step))
    print(f"seq xi={xi}  log2|G_n|/n  {row}", flush=True)


def chain(N: int) -> None:
    _, V = lattice_levels(3 ** N, 3 * N + 1, N)  # V(m) = G_N(3^{N-m}), m = 0..2N
    best = max(range(len(V)), key=lambda m: abs(V[m]))
    k = N - best
    s = abs(V[best])
    print(f"chain N={N:>5}: sup|G|={s:.4e}  k*={k:>5}  k*/N={k / N:.3f}  sup*sqrt(N)={s * N ** 0.5:.4f}  sup*N={s * N:.3f}", flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "seqs":
        top, step = int(sys.argv[2]), int(sys.argv[3])
        mod = 1 << (top + 3)
        rnd = random.Random(20261024).getrandbits(64) | 1
        for name, xi in [("1", 1), ("5", 5), ("7", 7), ("27", 27), ("1/3", pow(3, -1, mod)),
                         ("5/7", 5 * pow(7, -1, mod) % mod), ("rand64", rnd)]:
            print(name, end="  ")
            seq(xi, top, step)
    elif sys.argv[1] == "seq":
        seq(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    else:
        for N in map(int, sys.argv[2:]):
            chain(N)
