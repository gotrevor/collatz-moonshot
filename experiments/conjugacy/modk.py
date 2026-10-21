#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Distribution of nu = T^j(r) mod 2^K over r < 2^j, as deviations from uniform, for 3x+1 and 3x+5.
Prints, for each j, the deviation count(class) - 2^j/2^K for K=2,3,4 and the Walsh spectrum at K=4."""
import numpy as np, sys, itertools
J=int(sys.argv[1]); K=4
def run(q,c):
    for j in range(12, J+1):
        r = np.arange(2**j, dtype=np.int64); m = r.copy()
        for _ in range(j):
            odd = (m & 1).astype(bool); m = np.where(odd, (q*m+c)>>1, m>>1)
        low = m & (2**K-1)
        cnt = np.bincount(low, minlength=2**K).astype(np.int64)
        dev = cnt - 2**(j-K)
        # Walsh: for each mask h, sum (-1)^{popcount(h & low)}
        walsh = []
        for h in range(2**K):
            sgn = 1 - 2*(np.array([bin(h & x).count('1') & 1 for x in range(2**K)]))
            walsh.append(int((cnt*sgn).sum()))
        s2 = 2**(j/2)
        print(f"q={q} c={c:+d} j={j}: dev mod 16 /2^(j/2): " + ' '.join(f"{d/s2:+.2f}" for d in dev))
        print(f"            walsh/2^(j/2) by mask: " + ' '.join(f"{h:x}:{w/s2:+.2f}" for h,w in enumerate(walsh) if h))
run(3,1); run(3,5)
