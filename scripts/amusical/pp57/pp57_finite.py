"""Finite checks (C1) base automaton strongly connected, (C2) holonomy translations, for PP(seed)."""
import sys, random
from fractions import Fraction as F
from math import gcd
from pp57 import PP, engine_slope
sys.setrecursionlimit(100000)

def base_automaton(f):
    """states: z mod 3325 with z mod 665 not engine. edges: (z, z', leaf_affine (A,B) over Q)."""
    states = [z for z in range(3325) if engine_slope(z % 665) is None]
    S = set(states)
    out = {z: [] for z in states}
    for (r, a, s, b) in f.pieces:
        if a == 665: continue
        A = F(b, a); Bc = F(s) - A * r          # leaf map x -> A x + Bc on r mod a
        z = r % 3325
        inv2 = pow(A.denominator, -1, 3325)
        z2 = (A.numerator * z * inv2 + Bc.numerator * pow(Bc.denominator, -1, 3325)) % 3325
        out[z].append((z2, A, Bc))
    return states, S, out

def scc_ok(states, S, out):
    # forward and backward reachability from states[0] within edges landing in S
    fw = {states[0]}; st = [states[0]]
    while st:
        z = st.pop()
        for z2, A, Bc in out[z]:
            if z2 in S and z2 not in fw: fw.add(z2); st.append(z2)
    rev = {z: [] for z in states}
    for z in states:
        for z2, A, Bc in out[z]:
            if z2 in S: rev[z2].append(z)
    bw = {states[0]}; st = [states[0]]
    while st:
        z = st.pop()
        for z1 in rev[z]:
            if z1 not in bw: bw.add(z1); st.append(z1)
    return len(fw) == len(S) and len(bw) == len(S), len(fw), len(bw), len(S)

def holonomy(f, states, S, out, zstar, nwalks=400, seed=1):
    rng = random.Random(seed)
    # BFS tree to get a path from any state back to zstar
    rev = {z: [] for z in states}
    for z in states:
        for z2, A, Bc in out[z]:
            if z2 in S: rev[z2].append((z, A, Bc))
    back = {zstar: None}; st = [zstar]
    while st:
        z = st.pop()
        for z1, A, Bc in rev[z]:
            if z1 not in back: back[z1] = (z, A, Bc); st.append(z1)
    walks = []
    for _ in range(nwalks):
        z = zstar; A0 = F(1); B0 = F(0)
        for _ in range(rng.randrange(1, 12)):
            choices = [e for e in out[z] if e[0] in S]
            z2, A, Bc = rng.choice(choices)
            A0, B0 = A * A0, A * B0 + Bc; z = z2
        while z != zstar:
            z2, A, Bc = back[z]
            A0, B0 = A * A0, A * B0 + Bc; z = z2
        walks.append((A0, B0))
    g = 0
    for (A1, B1) in walks[:60]:
        for (A2, B2) in walks[:60]:
            tau = (A1 - 1) * B2 - (A2 - 1) * B1
            assert (tau.numerator % 3325) == 0 or tau == 0
            rho = tau / 3325
            g = gcd(g, abs(rho.numerator))
    return g, walks[:3]

def strip23(n):
    for p in (2, 3):
        while n and n % p == 0: n //= p
    return n

if __name__ == "__main__":
    seed = int(sys.argv[1])
    f = PP(seed)
    states, S, out = base_automaton(f)
    print("C1 strongly connected:", scc_ok(states, S, out))
    g, w = holonomy(f, states, S, out, states[0])
    print("C2 gcd of translation numerators/3325:", g, " prime-to-6 part:", strip23(g))
