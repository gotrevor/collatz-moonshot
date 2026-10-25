#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""
Far-corner traps for PairBoundDecay (research note §12, the failed port of Tao Prop 7.3).

For fixed odd xi the field Theta(k, t) = <xi 3^{-t}>_k does not depend on the walk length n: the
pairing walk started at level n+1 runs along the line k + 2t ~ n+1 (one step of t per pair, two
levels per pair), meeting the factors |cos(pi Theta(k, t))| at odd k.  So the black set
{||Theta|| <= eps} is a fixed union of triangles (Tao Lemma 7.4, mirrored), and a trap is the
intersection of one black component with one walk line.

For each black component (4-connected, on the odd-k sublattice the walk sees) and each line
k + 2t = N: L = number of walk points of the line inside the component, entered at t_in (its
smallest t on the line).  pairTheta_far bounds a triangle whose corner sits at row t by size
t log 3 + log eps, i.e. a near-corner trap entered at t_in lasts <~ 0.79 t_in pairs.  Reported:
the largest L / max(t_in, 1) and the largest L overall, with corner (k*, t*) = (max k, max t) of
the component and its size s* = log(eps / ||Theta(k*, t*)||).
Control (known answer): xi = 3^100 must show one giant trap (L ~ 100, t_in <= 1).
The column t = 0 is excluded: the walk's factors use t >= 1.
Usage: traps.py K EPS XI...   (K = max level; t runs to K/2)
"""
import math
import sys

import numpy as np
from scipy import ndimage


def field(xi: int, K: int, T: int) -> np.ndarray:
    """dist(Theta(k, t), Z) for k = 0..K, t = 0..T (float64 via the bit recurrence, exact to 2^-53)."""
    mod = 1 << K
    u = pow(3, -1, mod)
    x = xi % mod
    nbytes = (K + 7) // 8
    B = np.zeros((T + 1, K), dtype=np.float64)
    for t in range(T + 1):
        raw = np.frombuffer(x.to_bytes(nbytes, "little"), dtype=np.uint8)
        B[t] = np.unpackbits(raw, bitorder="little")[:K]
        x = x * u % mod
    th = np.zeros((K + 1, T + 1))
    for k in range(1, K + 1):  # Theta(k) = (b_{k-1} + Theta(k-1)) / 2
        th[k] = (B[:, k - 1] + th[k - 1]) / 2
    return np.minimum(th, 1 - th)


def analyse(xi: int, K: int, eps: float, label: str) -> None:
    T = K // 2
    D = field(xi, K, T)
    odd = np.zeros_like(D, dtype=bool)
    odd[3::2, :] = True  # walk factors live at k = 2i + 3
    black = (D <= eps) & odd
    black[: 3, :] = False
    black[:, 0] = False  # the walk's factors use t >= 1 (pairCos xi (2i+3) (m+1))
    # components on the odd-k sublattice: neighbours (k +- 2, t) and (k, t +- 1)
    sub = black[3::2, :]
    lab, ncomp = ndimage.label(sub)
    best_ratio, best_len = (0.0, None), (0, None)
    for c, sl in enumerate(ndimage.find_objects(lab), start=1):
        ii, tt = np.nonzero(lab[sl] == c)
        ii, tt = ii + sl[0].start, tt + sl[1].start
        ks = 3 + 2 * ii
        N = ks + 2 * tt
        for n_line in np.unique(N):
            sel = N == n_line
            L = int(sel.sum())
            t_in = int(tt[sel].min())
            kstar, tstar = int(ks.max()), int(tt.max())
            dstar = D[kstar, tstar]
            s = math.log(eps / dstar) if dstar > 0 else math.inf
            rec = (L, t_in, int(n_line), kstar, tstar, s)
            r = L / max(t_in, 1)
            if r > best_ratio[0]:
                best_ratio = (r, rec)
            if L > best_len[0]:
                best_len = (L, rec)
    def fmt(rec):
        L, t_in, n_line, kstar, tstar, s = rec
        return f"L={L} t_in={t_in} line N={n_line} corner=(k*={kstar}, t*={tstar}) size={s:.2f}"
    print(f"{label:>10} eps={eps:<6} comps={ncomp:>6}  max L/t_in={best_ratio[0]:.2f} [{fmt(best_ratio[1])}]", flush=True)
    print(f"{'':>10} {'':<10} {'':>13}  max L={best_len[0]} [{fmt(best_len[1])}]", flush=True)


def main() -> int:
    K, eps = int(sys.argv[1]), float(sys.argv[2])
    for a in sys.argv[3:]:
        xi = 3 ** int(a[2:]) if a.startswith("3^") else int(a)
        analyse(xi, K, eps, a)
    return 0


if __name__ == "__main__":
    sys.exit(main())
