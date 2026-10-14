# Do global orbit minima carry residue structure beyond long-window conditions?
# Per class r mod M: ratio (global minima) / (L-window minima) should be constant if not.
import json, sys, math
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from minima import U, V, status
N = int(sys.argv[1]); L = int(sys.argv[2])
def wmin(n):
    x = y = n
    for _ in range(L):
        x = U(x); y = V(y)
        if x < n or y < n: return False
    return True
W = [n for n in range(1, N + 1) if wmin(n)]
ST = {n: status(n) for n in W}
W = [n for n in W if ST[n] != 'cyc']          # cycle minima are window minima, never orbit minima
G = set(n for n in W if ST[n] == 'min')
print(f"N={N} L={L} window={len(W)} global={len(G)} ratio={len(G)/len(W):.4f}")
for M in (72, 864, 2**5 * 3**4):
    win = {}; glo = {}
    for n in W:
        r = n % M; win[r] = win.get(r, 0) + 1; glo[r] = glo.get(r, 0) + (n in G)
    base = len(G) / len(W)
    chi = 0.0; worst = []
    for r in win:
        e = win[r] * base; o = glo[r]
        if e > 0:
            chi += (o - e) ** 2 / (e * (1 - base))
            worst.append(((o - e) / math.sqrt(e * (1 - base)), r, o, round(e, 1)))
    worst.sort()
    print(f"M={M}: classes={len(win)} chi2={chi:.1f} (df~{len(win)-1})  most negative z={worst[0]}  most positive z={worst[-1]}")
