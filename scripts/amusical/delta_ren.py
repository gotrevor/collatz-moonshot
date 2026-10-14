"""Ren's independent check of the uniform agent's delta example (2026-10-13).
delta(6k)=6k+3, delta(6k+2)=6k+1, delta(6k+4)=4k, delta(4k+3)=4k+2, delta(4k+1)=6k+5.
Checks: (1) the five domains partition Z and images partition Z (mod 12 bookkeeping);
(2) every orbit through [-N,N] is finite; (3) residue-graph SCC counts, with U as teeth control."""
import sys
from fractions import Fraction as F

def d(x):
    if x % 6 == 0: return x + 3
    if x % 6 == 2: return x - 1
    if x % 6 == 4: return (x - 4) // 6 * 4
    if x % 4 == 3: return x - 1
    if x % 4 == 1: return (x - 1) // 4 * 6 + 5
    raise ValueError(x)

def U(x):
    if x % 2 == 0: return 3 * x // 2
    if x % 4 == 1: return 3 * (x - 1) // 4 + 1
    return 3 * (x - 3) // 4 + 2

# (1) bijectivity on a large window: images of [-B,B] injective and cover [-B/3, B/3]
B = 300000
img = {}
for x in range(-B, B + 1):
    y = d(x)
    assert y not in img, ("collision", x, img[y])
    img[y] = x
miss = [y for y in range(-B // 3, B // 3 + 1) if y not in img]
print("bijection window: collisions 0, uncovered in [-B/3,B/3]:", len(miss))

# (2) finite orbits
N = 30000
seen = set(); ncyc = 0; maxlen = 0
for x in range(-N, N + 1):
    if x in seen: continue
    y, L = d(x), 1
    orb = [x]
    while y != x:
        orb.append(y); y = d(y); L += 1
        if L > 10**6: print("LONG", x); sys.exit(1)
    seen.update(orb); ncyc += 1; maxlen = max(maxlen, L)
print("finite orbits through [-N,N]: all closed; cycles", ncyc, "max length", maxlen)

# (3) residue graph SCC count mod M: edge r -> f(x) mod M over a full set of lifts
def sccs(f, M, lifts=None):
    # cylinder modulus: lift x = r + M*t for t in range(L) with L large enough to determine f(x) mod M
    L = lifts or 72
    adj = {r: set() for r in range(M)}
    for r in range(M):
        for t in range(L):
            adj[r].add(f(r + M * t) % M)
    # Tarjan-free: count SCCs via Kosaraju
    order, vis = [], set()
    for s in range(M):
        if s in vis: continue
        stack = [(s, iter(adj[s]))]; vis.add(s)
        while stack:
            v, it = stack[-1]
            for w in it:
                if w not in vis:
                    vis.add(w); stack.append((w, iter(adj[w]))); break
            else:
                order.append(v); stack.pop()
    radj = {r: set() for r in range(M)}
    for v in adj:
        for w in adj[v]: radj[w].add(v)
    comp, c = {}, 0
    for s in reversed(order):
        if s in comp: continue
        st = [s]; comp[s] = c
        while st:
            v = st.pop()
            for w in radj[v]:
                if w not in comp: comp[w] = c; st.append(w)
        c += 1
    return c

for M in (12, 24, 36, 48, 60, 72, 96, 108, 144):
    print(f"M={M:4d}  delta SCCs={sccs(d, M):3d}   U SCCs={sccs(U, M):3d}")
