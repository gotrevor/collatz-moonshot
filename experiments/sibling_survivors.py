#!/usr/bin/env python3
"""
Sibling-map controls for first-crossing (coefficient stopping time) mechanisms.

Generalised shortcut map  T_{a,s}(n) = n/2 (n even),  (a*n + s)/2 (n odd),  a odd, s = +1/-1.
A *first crossing* of n is the least m with a^K < 2^m, K = odd steps among the first m;
n *survives* it when T^m(n) >= n (a coefficient-stopping-time failure), with overshoot
E = T^m(n) - n.  Exact identity (any a, s):  2^m T^m(n) = a^K n + N(v),  N(v) = s * numer(v),
so a survivor satisfies  D*n + 2^m*E = N(v)  with  D = 2^m - a^K > 0,  hence
    a^K * E ≡ N(v)  (mod D).

Why this exists (2026-09-22 mechanism search).  For a = 3, s = +1 no survivor is known
(CST is verified to 2.8e19).  For a = 5, s = +1 survivors EXIST: the subcritical cycles at
13 and 17 (E = 0), and the start 5, whose orbit enters the 13-cycle from below and crosses
after 39 laps (m = 274, K = 118, 39 odd runs, E = 8).  Any proposed mechanism excluding
many-run first-crossing survivors must therefore consume something specific to a = 3 (the
verified range, or the ballot entropy deficit log_2 3 > 1 ... i.e. odd-density threshold
above 1/2); an argument valid for every odd a is refuted by these rows.  For s = -1 there are
no survivors at all: N < 0 makes D*n + 2^m*E = N impossible, so the sign control for CST is
vacuous and the real control is the multiplier a.

Usage:
    sibling_survivors.py survivors A S NMAX [CAP]   one row per survivor n <= NMAX:
                                                    n m K runs E residue_ok
    sibling_survivors.py words M                    for each first-crossing length m <= M
                                                    (a = 3): m K u=2^m/3^K words primitive
                                                    maxN/2^m  K/(3u)   [asserts bound + primitivity]
No claim about Collatz is drawn from finite data.
"""
import sys
from fractions import Fraction


def make_step(a, s):
    return lambda n: n // 2 if n % 2 == 0 else (a * n + s) // 2


def first_crossing(step, a, n, cap):
    x, K, v = n, 0, []
    for j in range(1, cap + 1):
        v.append(x % 2)
        K += x % 2
        x = step(x)
        if a ** K < 2 ** j:
            return j, K, v, x
    return None


def odd_runs(v):
    return sum(1 for i, b in enumerate(v) if b == 1 and (i == 0 or v[i - 1] == 0))


def numer(v, a):
    """Mirror of FrontB.Words.numer with multiplier a:  numer(1::t) = 2 numer t + a^ones t."""
    N, K = 0, 0
    for b in reversed(v):
        if b:
            N = 2 * N + a ** K
            K += 1
        else:
            N = 2 * N
    return N


def survivors(a, s, nmax, cap):
    step = make_step(a, s)
    out = []
    for n in range(2, nmax + 1):
        fc = first_crossing(step, a, n, cap)
        if fc is None:
            continue
        m, K, v, y = fc
        if y >= n:
            N = s * numer(v, a)
            D = 2 ** m - a ** K
            E = y - n
            assert D * n + 2 ** m * E == N, (a, s, n)
            ok = (pow(a, K, D) * E - N) % D == 0
            out.append((n, m, K, odd_runs(v), E, ok))
    return out


def ballot_words(m):
    """First-crossing words of length m for a = 3: every proper prefix supercritical
    (2^j <= 3^K_j), the whole word subcritical (3^K < 2^m)."""
    out = []

    def rec(v, K, j):
        if j == m:
            if 3 ** K < 2 ** m:
                out.append(tuple(v))
            return
        if j > 0 and 2 ** j > 3 ** K:
            return
        for b in (1, 0):
            v.append(b)
            rec(v, K + b, j + 1)
            v.pop()

    rec([], 0, 0)
    return out


def is_power(v):
    m = len(v)
    for d in range(1, m):
        if m % d == 0 and v == v[:d] * (m // d):
            return True
    return False


def words(M):
    for m in range(1, M + 1):
        W = ballot_words(m)
        if not W:
            continue
        K = sum(W[0])
        assert all(sum(v) == K for v in W)
        u = Fraction(2 ** m, 3 ** K)
        bound = Fraction(K, 3) / u
        mx = max(Fraction(numer(list(v), 3), 2 ** m) for v in W)
        prim = all(not is_power(v) for v in W)
        assert mx <= bound and prim, m
        print(f"{m} {K} {float(u):.4f} {len(W)} {int(prim)} {mx} {bound}")


if __name__ == "__main__":
    if len(sys.argv) >= 5 and sys.argv[1] == "survivors":
        a, s, nmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        cap = int(sys.argv[5]) if len(sys.argv) > 5 else 2000
        rows = survivors(a, s, nmax, cap)
        for r in rows:
            print(*r)
        print(f"# a={a} s={s} nmax={nmax} cap={cap} survivors={len(rows)}")
    elif len(sys.argv) == 3 and sys.argv[1] == "words":
        words(int(sys.argv[2]))
    else:
        print(__doc__)
        sys.exit(2)
