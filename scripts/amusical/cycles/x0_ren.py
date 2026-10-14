"""Ren's independent X0(L) = max over 1<=p<L, all relevant e, of the Theorem A bound
M(p,e) = floor((k*max(2^e,3^p) + D) / (3D)), D = |2^e - 3^p|, k = e - p (number of odd steps).
Scans e in [p+1, 2p] restricted to |e - p*log2(3)| <= 3 and proves that outside it M < p."""
import math, sys
L = int(sys.argv[1])
th = math.log2(3)
best = (0, None)
for p in range(1, L):
    e0 = round(p * th)
    t3 = 3 ** p
    for e in range(max(p + 1, e0 - 3), min(2 * p, e0 + 3) + 1):
        k = e - p
        t2 = 1 << e
        D = abs(t2 - t3)
        M = (k * max(t2, t3) + D) // (3 * D)
        if M > best[0]: best = (M, (p, e))
print(f"L={L} X0={best[0]} at (p,e)={best[1]}")
