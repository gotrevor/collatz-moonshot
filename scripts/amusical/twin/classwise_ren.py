#!/usr/bin/env python3
"""Check twin2 §7: no class-wise constants κ_i with U²(n² + κ_{cls n}) = (Un)² + κ_{cls(Un)} for all n.

Route (mine, not the agent's): n = 0 (class E, U0 = 0) forces U²(κ_E) = κ_E; n = 1 (A, U1 = 1) forces
U²(1 + κ_A) = 1 + κ_A; n = 1+t (B, U(1+t) = t) forces κ_B = V²(t² + κ_E) + (1+t)²; n = Q (C, UQ = 1+t)
forces κ_C = V²((1+t)² + κ_B) + Q².  Points with U²x = x have degree <= 5 (D-iii), so enumerate degree <= 7
to be safe, then test the identity on all n of degree < 10.  Teeth: dropping the identity's κ_{cls(Un)}
term's class dependence is not tested; instead check the pure square κ = 0 identity HOLDS on E ∪ A and
FAILS on B (twin2 §1.1-§1.2), so the tester can both accept and reject.
"""
Q = 0b111


def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def deg(a):
    return a.bit_length() - 1


def divmod2(a, b):
    q, db = 0, deg(b)
    while a and deg(a) >= db:
        s = deg(a) - db
        q ^= 1 << s
        a ^= b << s
    return q, a


def U(n):
    if n & 1 == 0:
        return clmul(Q, n >> 1)
    if n & 2 == 0:
        return clmul(Q, n >> 2) ^ 1
    if n & 4 == 0:
        return clmul(Q, n >> 3) ^ 0b10
    return clmul(Q, n >> 3) ^ 0b11


def V(y):
    q, r = divmod2(y, Q)
    return {0: q << 1, 1: 1 ^ (q << 2), 0b10: 0b11 ^ (q << 3), 0b11: 0b111 ^ (q << 3)}[r]


def cls(n):
    return 0 if n & 1 == 0 else 1 if n & 2 == 0 else 2 if n & 4 == 0 else 3


def sq(n):
    return clmul(n, n)


def U2(n):
    return U(U(n))


assert all(V(U(n)) == n for n in range(1 << 12)) and all(U(V(n)) == n for n in range(1 << 12))
# teeth for the tester
assert all(U2(sq(n)) == sq(U(n)) for n in range(1 << 12) if cls(n) in (0, 1))
assert any(U2(sq(n)) != sq(U(n)) for n in range(1 << 12) if cls(n) == 2)

per2 = [x for x in range(1 << 8) if U2(x) == x]
print("U²x = x, deg <= 7:", [bin(x) for x in per2])
assert all(deg(x) <= 5 for x in per2)
survivors = []
for kE in per2:
    for one_kA in per2:
        kA = 1 ^ one_kA
        kB = V(V(0b100 ^ kE)) ^ sq(0b11)
        kC = V(V(sq(0b11) ^ kB)) ^ sq(Q)
        k = [kE, kA, kB, kC]
        bad = next((n for n in range(1 << 10) if U2(sq(n) ^ k[cls(n)]) != sq(U(n)) ^ k[cls(U(n))]), None)
        print(f"κ = {[bin(x) for x in k]}: first failure n = {bin(bad) if bad is not None else None}")
        if bad is None:
            survivors.append(k)
print("PASS (no class-wise constants)" if not survivors else f"FAIL: survivors {survivors}")
