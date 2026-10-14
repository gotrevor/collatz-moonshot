#!/usr/bin/env python3
"""Teeth tests for cyclemin (independent pure-Python methods).

T1 (q=1): naive return test.  For n in [1,N), n is periodic with period <= 2H iff
    U^j n == n for some 1 <= j <= 2H (no dips, no meet-in-the-middle).  The minima of the
    periodic points found must equal cyclemin's CYCLE lines (skipknown=0).
T2 (q-layers): word enumeration.  For every word w of length p <= P, r_w = q*N_w/(2^e-3^p);
    keep integer r_w whose cycle has all elements > q/3.  Their cycle minima must equal
    cyclemin's output over (q/3, X0_q(P)] with H = ceil(P/2), where X0_q is Theorem A's bound.
    Also checks Theorem A itself on every such cycle (min <= M_q(p,e)).
"""
import itertools, subprocess, sys
from fractions import Fraction

def U(x, q=1):
    if x % 2 == 0: return 3 * x // 2
    if (x - q) % 4 == 0: return (3 * x + q) // 4
    return (3 * x - q) // 4

def run_c(lo, hi, H, skip, q):
    out = subprocess.run(['./cyclemin', str(lo), str(hi), str(H), str(skip), str(q)],
                         capture_output=True, text=True, check=True)
    found = set()
    for line in out.stdout.split('\n'):
        if line.startswith('CYCLE'):
            _, n, per = line.split(); found.add((int(n), int(per)))
    return found, out.stderr.strip()

def T1(N, H):
    per = {}
    for n in range(1, N):
        x = n
        for j in range(1, 2 * H + 1):
            x = U(x)
            if x == n: per[n] = j; break
    # group into cycles, take minima
    mins = set()
    for n, p in per.items():
        orb = [n]; x = n
        for _ in range(p - 1): x = U(x); orb.append(x)
        mins.add((min(orb), p))
    c, info = run_c(1, N, H, 0, 1)
    print(f"T1 N={N} H={H}: naive periodic points {sorted(per)} -> minima {sorted(mins)}; C {sorted(c)}; {'PASS' if mins == c else 'FAIL'}")
    return mins == c

def Mq(p, e, q):
    k = e - p; A, B = 1 << e, 3 ** p; D = abs(A - B)
    return (k * q * max(A, B) + q * D) // (3 * D)

def T2(q, P):
    X0 = 0
    for p in range(1, P + 1):
        for e in range(p, 2 * p + 1):
            if (1 << e) != 3 ** p: X0 = max(X0, Mq(p, e, q))
    cyc = set(); thmA_ok = True
    for p in range(1, P + 1):
        for w in itertools.product((0, 1, 2), repeat=p):
            # x -> (3x+d)/2^b with d in {0, +q, -q}: compose exactly
            a, b = Fraction(1), Fraction(0); e = 0
            for s in w:
                bits = 1 if s == 0 else 2; d = (0, q, -q)[s]; e += bits
                a, b = a * 3 / 2 ** bits, (b * 3 + d) / 2 ** bits
            if a == 1: continue
            r = b / (1 - a)
            if r.denominator != 1: continue
            r = int(r)
            orb = [r]; x = r
            for _ in range(p - 1): x = U(x, q); orb.append(x)
            assert U(x, q) == r
            if min(orb) <= q // 3: continue          # outside the all-positive (> q/3) class
            if any(U(orb[i], q) != orb[(i+1) % p] for i in range(p)): continue
            # minimal period
            pp = next(j for j in range(1, p + 1) if p % j == 0 and orb[j % p] == r)
            m = min(orb)
            cyc.add((m, pp))
            ee = sum(1 if y % 2 == 0 else 2 for y in orb[:pp])
            if m > Mq(pp, ee, q): thmA_ok = False
    H = (P + 1) // 2
    c, info = run_c(q // 3 + 1, X0 + 1, H, 0, q)
    ok = (c == cyc) and thmA_ok
    print(f"T2 q={q} P={P}: X0_q={X0}, word-enumeration cycles (min,period) {len(cyc)}, C found {len(c)}, ThmA holds={thmA_ok}: {'PASS' if ok else 'FAIL'}")
    if not ok: print('  enum-only', sorted(cyc - c)[:20], ' C-only', sorted(c - cyc)[:20])
    # truncation teeth: searching only up to X0/10 must miss something if the big cycles are large
    c2, _ = run_c(q // 3 + 1, X0 // 10 + 1, H, 0, q)
    print(f"   truncated search to X0/10: finds {len(c2)} of {len(cyc)}  (missing {sorted(cyc - c2)[:5]})")
    return ok

if __name__ == '__main__':
    ok = T1(20000, 300)
    ok &= T1(3000, 6) and T1(3000, 5)
    for q, P in [(5, 10), (7, 10), (13, 10), (139, 9), (23, 10)]:
        ok &= T2(q, P)
    print('ALL PASS' if ok else 'SOME FAIL')
