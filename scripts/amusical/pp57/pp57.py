"""Ping-pong engine on the primes 5, 7 with phase mod 19, plus a U-like filler (agent "transitive").

p = 3.  K = <8> = {1,7,8,11,12,18} (mod 19), B = 15K = {4,6,9,10,13,15}.
Engine (linear pieces, keyed on x mod 665 = 5*7*19):
  E_A : 5|x,            x mod 19 in K  :  x -> 21x/5   (v5 -1, v7 +1, phase *8)
  E_AB: 5!|x, 7|x,      x = 1 (19)      :  x -> 15x     (v5 +1,        phase -> 15)
  E_B : 7|x,            x mod 19 in B  :  x -> 75x/7   (v5 +2, v7 -1, phase *8)
  E_BA: 7!|x, 5|x,      x mod 19 in B  :  x -> 3x      (               phase *3 -> K)
Filler: every other residue r mod 3325 (=25*7*19) is split 2-adically into leaves,
  either 4 leaves mod 13300 (slope 3/4 each) or {r mod 6650 (slope 3/2), two leaves mod 13300 (slope 3/4)};
  each leaf maps onto one residue class mod 9975 of F_img = Z minus the engine images.
All slopes have v_3 = 1; filler slopes are 3/2, 3/4 (2-expanding, isometric at 5, 7, 19).
"""
import random, sys
from fractions import Fraction as F
from math import gcd

K = {1, 7, 8, 11, 12, 18}
B = {4, 6, 9, 10, 13, 15}
DM = 13300   # domain table modulus
IM = 349125  # image table modulus (lcm of all image moduli)
FIM = 9975   # filler image modulus

def engine_slope(r):
    a = r % 5 == 0; b = r % 7 == 0; h = r % 19
    if a and h in K: return F(21, 5)
    if (not a) and b and h == 1: return F(15)
    if b and h in B: return F(75, 7)
    if (not b) and a and h in B: return F(3)
    return None

def in_engine_image(y):
    h = y % 19
    return ((y % 21 == 0 and h in K) or (y % 105 == 0 and y % 25 != 0 and h == 15)
            or (y % 75 == 0 and h in B) or (y % 15 == 0 and y % 7 != 0 and h in K))

class PP:
    """pieces: dict residue t mod DM -> (r, a, s, b) meaning x = r + a k -> s + b k (positive slope b/a)."""
    def __init__(self, seed=0):
        rng = random.Random(seed)
        self.seed = seed
        pieces = []
        # engine pieces on classes mod 665
        for r in range(665):
            s = engine_slope(r)
            if s is None: continue
            pieces.append((r, 665, int(s * r), int(s * 665)))
        dom = [r for r in range(3325) if engine_slope(r % 665) is None]
        img = [y for y in range(FIM) if not in_engine_image(y)]
        assert len(dom) == 2765 and len(img) == 9599
        rng.shuffle(dom); rng.shuffle(img)
        n4 = len(img) - 3 * len(dom)   # residues with 4 leaves
        leaves = []
        for k, r in enumerate(dom):
            if k < n4:
                leaves += [(r + 3325 * e, 13300) for e in range(4)]
            else:
                e = rng.randrange(2)
                leaves.append((r + 3325 * e, 6650))
                leaves += [(r + 3325 * (1 - e) + 6650 * f, 13300) for f in range(2)]
        assert len(leaves) == len(img)
        # repair: every domain residue must have a leaf whose image residue mod 3325 is a filler-domain residue
        def good(s): return engine_slope(s % 665) is None
        by_res = {}
        for k, (r, a) in enumerate(leaves):
            by_res.setdefault(r % 3325, []).append(k)
        for z, ks in by_res.items():
            if any(good(img[k]) for k in ks):
                continue
            for z2, ks2 in by_res.items():
                gk = [k for k in ks2 if good(img[k])]
                if len(gk) >= 2:
                    k1 = ks[0]; k2 = gk[0]
                    img[k1], img[k2] = img[k2], img[k1]
                    break
        for (r, a), s in zip(leaves, img):
            pieces.append((r, a, s, FIM))
        self.pieces = pieces
        self.tab = [None] * DM
        for idx, (r, a, s, b) in enumerate(self.pieces):
            for t in range(r % a, DM, a):
                assert self.tab[t] is None
                self.tab[t] = idx
        assert None not in self.tab
        self.itab = [None] * IM
        for idx, (r, a, s, b) in enumerate(self.pieces):
            for t in range(s % b, IM, b):
                assert self.itab[t] is None, ("image overlap", t)
                self.itab[t] = idx
        assert None not in self.itab
        self.M = DM; self.Mi = IM

    def __call__(self, x):
        r, a, s, b = self.pieces[self.tab[x % DM]]
        return s + b * ((x - r) // a)

    def inv(self, y):
        r, a, s, b = self.pieces[self.itab[y % IM]]
        return r + a * ((y - s) // b)

    def slope(self, x):
        r, a, s, b = self.pieces[self.tab[x % DM]]
        return F(b, a)

    def is_engine(self, x):
        return self.pieces[self.tab[x % DM]][1] == 665

def vp(n, p):
    n = abs(n); v = 0
    if n == 0: return 10**9
    while n % p == 0: n //= p; v += 1
    return v

if __name__ == "__main__":
    f = PP(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    print(len(f.pieces), "pieces")
    sl = set(F(b, a) for r, a, s, b in f.pieces)
    print("slopes:", sorted(sl), "v3:", set(vp(q.numerator, 3) - vp(q.denominator, 3) for q in sl))
    import itertools
    bad = sum(1 for x in range(-30000, 30000) if f.inv(f(x)) != x or f(f.inv(x)) != x)
    print("inverse mismatches on [-3e4,3e4):", bad)
