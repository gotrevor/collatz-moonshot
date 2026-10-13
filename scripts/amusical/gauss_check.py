# Independent check of the Gaussian relative H (from its written definition only).
def mul(x, y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def add(x, y): return (x[0]+y[0], x[1]+y[1])
def divexact(x, d):
    n = d[0]*d[0]+d[1]*d[1]; c = (d[0], -d[1]); t = mul(x, c)
    assert t[0] % n == 0 and t[1] % n == 0, ("not exact", x, d)
    return (t[0]//n, t[1]//n)
pi, pib = (2, 1), (2, -1)
pi2, pib2 = mul(pi, pi), mul(pib, pib)
def H(z):
    a, b = z
    r5, r25 = (a + 2*b) % 5, (a + 7*b) % 25
    if r5 == 0: return add((1, 0), divexact(mul(pi2, z), pib))
    if r25 == 1: return divexact(mul(pi, add(z, (-1, 0))), pib2)
    y = (17 * r25) % 25
    if y > 12: y -= 25
    return divexact(add(mul(pi2, z), (0, y)), pib2)
conj = lambda z: (z[0], -z[1])
R = 60
box = [(a, b) for a in range(-R, R+1) for b in range(-R, R+1)]
img = {}
for z in box:
    w = H(z)
    assert w not in img, ("not injective", z, img[w]); img[w] = z
# reversal: conj(H(conj(H(z)))) == z
bad = [z for z in box if conj(H(conj(H(z)))) != z]
print("injective on box:", True, "reversal failures:", len(bad))
# surjectivity: every point in a smaller box is hit (preimage via reversal H^-1 = conj H conj)
r = 20
miss = [w for w in [(a, b) for a in range(-r, r+1) for b in range(-r, r+1)] if H(conj(H(conj(w)))) != w or w not in img and abs(conj(H(conj(w)))[0]) <= R and abs(conj(H(conj(w)))[1]) <= R]
print("surjectivity misses (small box):", len(miss))
# orbits meeting the real integers 1..13: count distinct orbits by following up to 3000 steps
def orbit_hits(n, steps=3000):
    seen = set(); z = (n, 0); hits = {n}
    for _ in range(steps):
        z = H(z)
        if z == (n, 0): break
        if z[1] == 0 and 1 <= z[0] <= 13: hits.add(z[0])
    return hits
print({n: sorted(orbit_hits(n)) for n in range(1, 14)})
