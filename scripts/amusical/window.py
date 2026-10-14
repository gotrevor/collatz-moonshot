# Exact density of L-window minima (n < U^t n and n < V^t n for 1 <= t <= L), large-n limit,
# versus the empirical count over 1..N.
from fractions import Fraction as F
import sys
sys.path.insert(0, __file__.rsplit('/',1)[0])
from minima import U, V
def walk(steps, L):
    # steps: list of (dlog3, dlog2, prob); state = (a, b) meaning value 3^a / 2^b relative to start
    dist = {(0, 0): F(1)}
    out = []
    for t in range(L):
        nd = {}
        for (a, b), p in dist.items():
            for da, db, q in steps:
                na, nb = a + da, b + db
                if F(3)**na / F(2)**nb > 1:
                    nd[(na, nb)] = nd.get((na, nb), 0) + p * q
        dist = nd
        out.append(sum(dist.values()))
    return out
fw = walk([(1, 1, F(1, 2)), (1, 2, F(1, 2))], 40)
bw = walk([(-1, -1, F(1, 3)), (-1, -2, F(2, 3))], 40)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
def wmin(n, L):
    x = y = n
    for _ in range(L):
        x = U(x); y = V(y)
        if x <= n or y <= n: return False
    return True
for L in (1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40):
    d = fw[L-1] * bw[L-1]
    emp = sum(wmin(n, L) for n in range(1, N + 1)) / N if L <= 20 else None
    print(L, float(fw[L-1]), float(bw[L-1]), 'delta_L=%.6f' % float(d), 'exact' if L <= 4 else '', d if L <= 4 else '', 'emp=%s' % (('%.6f' % emp) if emp is not None else '-'))
