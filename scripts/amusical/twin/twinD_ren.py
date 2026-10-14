#!/usr/bin/env python3
"""Independent check of twin2's Theorem D for the F2[t] twin of the amusical permutation.

Polynomials over F2 are ints (bit i = coefficient of t^i).  Checks:
  D1: deg(t^{2p} + Q^p) = 2p - 2^{v2(p)} for p <= PMAX.
  D : every cycle through a polynomial of degree < DEG0 has minimum degree <= 2^{v2(p)} + 2.
  D-iii: a periodic polynomial of degree d has period p with 3p + 4 >= 2d.
Teeth: the sharpened bound 2^{v2(p)} (no +2) must FAIL on some cycle found, else the census is too
small to test anything; and D1 with 2^{v2(p)} replaced by 1 must fail at some even p.
"""
import sys

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


def U(n):
    if n & 1 == 0:
        return clmul(Q, n >> 1)
    if n & 2 == 0:
        return clmul(Q, n >> 2) ^ 1          # n = 1 + t^2 m
    if n & 4 == 0:
        return clmul(Q, n >> 3) ^ 0b10       # n = 1 + t + t^3 m
    return clmul(Q, n >> 3) ^ 0b11           # n = 1 + t + t^2 + t^3 m


def v2(p):
    return (p & -p).bit_length() - 1


def check_D1(pmax):
    bad = 0
    sharper_fails = False
    qp = 1
    for p in range(1, pmax + 1):
        qp = clmul(qp, Q)
        d = deg((1 << (2 * p)) ^ qp)
        if d != 2 * p - (1 << v2(p)):
            bad += 1
        if d != 2 * p - 1:
            sharper_fails = True
    return bad, sharper_fails


def census(deg0, degcap, maxsteps):
    cycles = {}
    for n0 in range(1 << deg0):
        x, orbit = n0, [n0]
        for _ in range(maxsteps):
            x = U(x)
            if x == n0:
                break
            if deg(x) > degcap:
                orbit = None
                break
            orbit.append(x)
        else:
            orbit = None
        if orbit is not None:
            key = min(orbit)
            cycles.setdefault(key, orbit)
    return cycles


def main():
    deg0 = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    bad1, sharp1 = check_D1(400)
    print(f"D1: p<=400 mismatches={bad1}; teeth (2^v -> 1 fails somewhere)={sharp1}")
    cyc = census(deg0, 4 * deg0 + 40, 20000)
    exc = {0, 1, 0b11, 0b111}
    viol = viol_iii = 0
    tight = {1: False, 0: False}
    byp = {}
    for orbit in cyc.values():
        p = len(orbit)
        if set(orbit) & exc:
            continue
        m = min(deg(x) for x in orbit)
        b = (1 << v2(p)) + 2
        viol += m > b
        for s in (1, 0):
            if m > (1 << v2(p)) + s:
                tight[s] = True
        dmax = max(deg(x) for x in orbit)
        viol_iii += not (3 * p + 4 >= 2 * dmax)
        byp.setdefault(p, []).append(m)
    print(f"census deg<{deg0}: {len(cyc)} cycles incl. exceptional; periods "
          + ", ".join(f"{p}:{len(v)} (min-deg max {max(v)}, bound {(1 << v2(p)) + 2})" for p, v in sorted(byp.items())))
    print(f"Theorem D violations={viol}; D-iii violations={viol_iii}")
    print(f"teeth: bound 2^v+1 fails on some cycle={tight[1]}; 2^v+0 fails={tight[0]}")
    ok = bad1 == 0 and sharp1 and viol == 0 and viol_iii == 0 and tight[0]
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
