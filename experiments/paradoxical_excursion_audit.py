#!/usr/bin/env python3
"""Exact A2 controls; no randomness, floating-point decisions, or external dependencies.

The table audit scans odd starts <= 5000 (containing every start reported in A1).
It checks every reported row and trunk, NOT the much larger completeness bound X(m).
The existing orbit census is the separate source of that completeness claim.
"""
from collections import Counter
from fractions import Fraction as F
from math import comb

from paradoxical import numer_fast, tstep, trace_word
from paradoxical_random_model import (
    binomial_form, closed_form_Nmax, closed_form_SN, dp_aggregates, words,
)


def orbit(n, m):
    xs = [n]
    for _ in range(m):
        xs.append(tstep(xs[-1]))
    return xs


def split_check(xs, k):
    n, y, t = xs[0], xs[-1], xs[k]
    v = [bool(x % 2) for x in xs[:-1]]
    m, j, b = len(v), sum(v[:k]), sum(v[k:])
    l = m - k
    nd, nc = numer_fast(v[:k]), numer_fast(v[k:])
    D = 2**m - 3**(j+b)
    slack = 3**j * nc + 2**l * nd - D*t
    assert 2**k*t == 3**j*n + nd
    assert 2**l*y == 3**b*t + nc
    assert numer_fast(v) == 3**b*nd + 2**k*nc
    assert slack == 3**j * 2**l * (y-n)
    assert (slack > 0) == (y > n)
    assert (slack == 0) == (y == n)
    assert (slack >= 0) == (y >= n)
    return D*t - 3**j*nc, 2**l*nd


def split_controls():
    count = 0
    for n in range(1, 101):
        for m in range(17):
            xs = orbit(n, m)
            for k in range(m+1):
                split_check(xs, k)
                count += 1
    x, z = orbit(2305, 46), orbit(2313, 46)
    assert min(x) == min(z) == x[14] == z[14] == 103
    assert x[14:] == z[14:]
    assert sum(q % 2 for q in x[:14]) == sum(q % 2 for q in z[:14]) == 6
    assert x[-1] == z[-1] == 2308
    assert split_check(x, 14) == (21560735825920, 30953829302272)
    assert split_check(z, 14) == (21560735825920, 5905580032000)
    assert x[-1] > x[0] and z[-1] < z[0]
    print(f"split controls: {count} exact identities, including equality and negative slack")
    print("depth-only refutation: 2305/2313 -> 103 at (k,j)=(14,6), same 32-step climb -> 2308")


TABLE = {
    8: (5, 4, 7, 25, {11: 2, 5: 1, 7: 1}),
    27: (17, 19, 165, 885, {31: 13, 47: 6}),
    46: (29, 101, 91, 4611, {91: 39, 47: 26, 31: 22, 71: 7, 103: 6, 61: 1}),
    54: (34, 0, None, None, {}),
    65: (41, 155, 73, 4547, {31: 56, 47: 48, 91: 40, 103: 6, 71: 4, 23: 1}),
    73: (46, 41, 487, 4613, {31: 26, 47: 15}),
}


def table_controls():
    for m, (a_expected, count, lo, hi, trunks) in TABLE.items():
        hits, minima, climbs, endpoints, hitting_times = [], Counter(), [], [], []
        missing_remainder = 0
        for n in range(3, 5001, 2):
            xs = orbit(n, m)
            a = sum(x % 2 for x in xs[:-1])
            if 3**a >= 2**m or xs[-1] <= n:
                continue
            assert a == a_expected
            k = min(range(m+1), key=xs.__getitem__)
            t = xs[k]
            lhs, rhs = split_check(xs, k)
            missing_remainder += lhs >= 0
            hits.append(n)
            minima[t] += 1
            climbs.append(F(max(xs[k:]), t))  # suffix peak, not the pre-trunk peak
            endpoints.append(F(xs[-1], t))
            z = n
            for tau in range(10001):
                if z <= 2:
                    hitting_times.append(tau)
                    break
                z = tstep(z)
            else:
                raise AssertionError((n, "hitting time exceeds control horizon"))
            assert m < tau
            # E = (1/2) sum of odd-position suffix multipliers; each <= y/t.
            E = F(numer_fast([bool(x % 2) for x in xs[:-1]]), 2**m)
            delta = F(2**m - 3**a, 2**m)
            assert delta*n < E <= F(a, 2)*F(xs[-1], t)
        assert len(hits) == count and dict(minima) == trunks, (m, hits, minima)
        assert (min(hits, default=None), max(hits, default=None)) == (lo, hi)
        print(f"m={m}: {count} starts; trunks={dict(sorted(minima.items()))}; "
              f"descent remainder needed by {missing_remainder}/{count}")
        if hits:
            print(f"  endpoint/t range [{min(endpoints)}, {max(endpoints)}]; "
                  f"suffix peak/t range [{min(climbs)}, {max(climbs)}]; "
                  f"hitting times {min(hitting_times)}..{max(hitting_times)}")
    print("table evidence: all reported rows reproduced within odd starts <= 5000; no new completeness claim")


def model_controls():
    # Check every word, including supercritical words, for the adjacent-swap proof of Nmax.
    for m in range(2, 11):
        for a in range(1, m+1):
            ns = []
            for v in words(m, a):
                N = numer_fast(v)
                ns.append(N)
                for r in range(1, m-1):
                    if v[r:r+2] == [True, False]:
                        w = v[:r] + [False, True] + v[r+2:]
                        assert numer_fast(w)-N == 2**r * 3**sum(v[r+2:])
            assert sum(ns) == closed_form_SN(m, a)
            assert max(ns) == closed_form_Nmax(m, a)
            assert min(ns) == 3**a-2**a
    # Validate the rounding bound even with saturation (the old strict lower bound was false).
    for M in [4, 8, 16, 32]:
        for D in range(1, M):
            for N in range(1, D*(M+4)):
                p = min(F(1), F(N, D*M))
                count = sum(D*n < N for n in range(3, M+2, 2))
                q = F(2*count, M)
                assert count == min(max((N-1-D)//(2*D), 0), M//2)
                assert 0 <= p-q < F(3*D+1, D*M)
    for m in [100, 200, 400, 800]:
        a = 0
        while 3**(a+1) < 2**m:
            a += 1
        n, r = m-1, a-1
        _, S, mx, _ = dp_aggregates(m, a)
        D, M = 2**m-3**a, 2**m
        assert S == closed_form_SN(m, a)
        assert F(S, M*M) == binomial_form(m, a)
        assert mx < D*M
        u_gap, v_gap = F(r)-F(n, 2), F(3*n, 4)-r
        assert u_gap > 0 and v_gap > 0
        bound = F(n, 4)/u_gap**2 + F(3*n, 16)/v_gap**2
        error = abs(1-2*F(S, M*M))
        assert error <= bound
        print(f"model m={m}, a={a}: 2*delta*R={float(2*F(S,M*M)):.15f}; "
              f"error={float(error):.3g} <= Chebyshev bound {float(bound):.3g}")
    print("model controls: sum/max/min/swap identities; exact rounding including clipping; exact asymptotic error bounds")


if __name__ == '__main__':
    split_controls()
    table_controls()
    model_controls()
