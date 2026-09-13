#!/usr/bin/env python3
"""Campaign B lap 1: exact cascade and cyclic-potential composition controls.

No floating-point decisions. Census bounds are explicit finite probe ranges, not
uniform finiteness certificates. The rational fixed point is an affine-word
construction; it is NOT asserted to be an integer Collatz cycle.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import comb, prod

from paradoxical import numer_fast, realizing_residue_fast, trace_word, tstep


def compositions(n, k):
    if n < k:
        return
    for cuts in combinations(range(1, n), k - 1):
        ends = (0,) + cuts + (n,)
        yield tuple(ends[i + 1] - ends[i] for i in range(k))


def tuples_at(m, a, b):
    for q in compositions(a, b):
        # All gaps positive except the last; shift that last gap by one.
        for ep in compositions(m - a + 1, b):
            yield q, ep[:-1] + (ep[-1] - 1,)


def word(q, e):
    return [v for qi, ei in zip(q, e) for v in [True]*qi + [False]*ei]


def runs(v):
    assert v and v[0]
    q, e, i = [], [], 0
    while i < len(v):
        j = i
        while i < len(v) and v[i]:
            i += 1
        q.append(i-j)
        j = i
        while i < len(v) and not v[i]:
            i += 1
        e.append(i-j)
    return tuple(q), tuple(e)


def cascade(q, e):
    """P_i*w_0 = H_i*w_i - T_i, without discarding any prefix term."""
    b, a, m = len(q), sum(q), sum(q) + sum(e)
    P, H, T = [1], [1], [0]
    for i in range(b-1):
        P.append(P[-1] * 3**q[i])
        T.append(3**q[i] * T[-1] + H[-1] * (2**e[i]-1))
        H.append(H[-1] * 2**(e[i]+q[i+1]))
    U = 3**q[-1] * T[-1] - H[-1]
    return a, m, 2**m - 3**a, P, H, T, U


def bounds(q, e, data):
    a, m, D, P, H, T, U = data
    assert D > 0
    leaves = all(D*(h-t) <= p*U for p, h, t in zip(P, H, T))
    lo = 1
    for i in reversed(range(len(q)-1)):
        v = 2**(e[i]+q[i+1])*lo - 2**e[i]+1
        lo = max(1, -(-v // 3**q[i]))
    ceiling = D*lo <= U
    assert not ceiling or leaves
    # The fixed point's head scale, times D, is U + 2^(m-q_0).
    fixed = all(D*(h-t) <= p*(U+2**(m-q[0])) for p, h, t in zip(P, H, T))
    assert not leaves or fixed
    return fixed, leaves, ceiling


def potential_check(q, e, data):
    """Test the proposed inequality on the larger rational positivity relaxation."""
    a, m, D, P, H, T, U = data
    b = len(q)
    delta = F(D, 2**m)
    r = [F(3**qi, 2**(qi+ei)) for qi, ei in zip(q, e)]
    s = [1-F(1, 2**ei) for ei in e]
    fixed_w0 = F(U+2**(m-q[0]), D)
    z = [2**qi * (p*fixed_w0+t)/h for qi, p, h, t in zip(q, P, H, T)]
    assert all(zi >= 2**qi for zi, qi in zip(z, q))
    maxima = []
    for i in range(b):
        products = [F(1)]
        for j in range(1, b):
            products.append(products[-1]*r[(i-j) % b])
        maxima.append(max(products))
        cyclic_sum = sum(s[(i-j-1) % b]*products[j] for j in range(b))
        assert delta*z[i] == cyclic_sum < b*maxima[-1]
        assert z[(i+1) % b] == r[i]*z[i]+s[i]
        assert 2**q[i] < F(b, 1)/delta*maxima[i]
    assert prod(r) == 1-delta
    assert all(maxima[(i+1) % b] == max(1, r[i]*maxima[i]) for i in range(b))
    assert min(maxima) == 1
    pivot = maxima.index(1)
    K = F(b, 1)/delta
    # Architecture lap 2: independently check the Bernoulli/squaring proof.
    # This cut depends on the rational fixed values, not the multiplier maxima.
    small = min(range(b), key=lambda i: z[i])
    assert z[small] < K
    for j in range(b):
        i = (small+j) % b
        assert r[i] + F(1, 2) <= 2**q[i]
        assert z[(i+1) % b] < z[i]**2
        assert power_compare(K, 2**j, z[i], strict=True)
    for j in range(b):
        i = (pivot+j) % b
        assert power_compare(K, 2**j-1, maxima[i], strict=False)
        assert power_compare(K, 2**j, 2**q[i], strict=True)
    C = 2**b-1
    assert power_compare(K, C, 2**a, strict=True)
    assert 2**m < 2**b*3**a  # All fixed values >= 2, all s_i < 1.
    return pivot


def power_compare(base, exponent, target, strict):
    """Exact early exit for base>1; avoid gigantic unnecessary b=21 powers."""
    assert base > 1
    value = F(1)
    for _ in range(exponent):
        if value > target or (not strict and value == target):
            return True
        value *= base
    return value > target if strict else value >= target


def actual_check(n, m):
    v = trace_word(n, m)
    q, e = runs(v)
    data = cascade(q, e)
    a, _, D, P, H, T, U = data
    x, ws = n, []
    for qi, ei in zip(q, e):
        assert (x+1) % 2**qi == 0
        wi = (x+1)//2**qi
        assert wi >= 1
        ws.append(wi)
        old = x
        for _ in range(qi+ei):
            x = tstep(x)
        assert 2**(qi+ei)*x + 2**qi == 3**qi*(old+1)
    for i in range(len(q)-1):
        assert 3**q[i]*ws[i]+2**e[i] == 2**(e[i]+q[i+1])*ws[i+1]+1
    assert 3**q[-1]*ws[-1] == 2**e[-1]*x+1
    assert all(p*ws[0] == h*w-t for p, h, t, w in zip(P, H, T, ws))
    assert 2**(m-q[0])*x == 3**a*ws[0]+U
    assert numer_fast(v) == 2**q[0]*U+3**a
    assert (n < x) == (D*ws[0] <= U)
    if D > 0 and n < x:
        assert all(bounds(q, e, data))
        potential_check(q, e, data)
    return q, e, data, x


def controls():
    for n in range(3, 202, 2):
        for m in range(1, 41):
            actual_check(n, m)
    # The original three-block formulas, including both relaxations.
    from rung3_census import rhs, w1_ceiling, w1_positivity
    for m in range(5, 19):
        for a in range(3, m-1):
            if 3**a >= 2**m:
                continue
            for q, e in tuples_at(m, a, 3):
                t = tuple(x for pair in zip(q, e) for x in pair)
                data = cascade(q, e)
                assert data[-1] == rhs(*t)
                fixed, leaves, ceiling = bounds(q, e, data)
                assert leaves == (data[2]*w1_positivity(*t) <= 3**sum(q[:2])*rhs(*t))
                assert ceiling == (data[2]*w1_ceiling(*t) <= rhs(*t))
                if fixed:
                    potential_check(q, e, data)
    # Omit just one joint's positivity: the proposed bound is then FALSE.
    # These are rational affine controls, not admitting integer segments.
    for b in (2, 3, 4, 5):
        Q = 32*b
        q, e = (1,)*(b-1)+(Q,), (1,)*(b-2)+(2*Q, 0)
        a, m, D, P, H, T, U = cascade(q, e)
        wstar = F(U+2**(m-q[0]), D)
        z = [2**qi*(p*wstar+t)/h for qi, p, h, t in zip(q, P, H, T)]
        assert all(z[i] >= 2**q[i] for i in range(b-1))
        assert z[-1] < 2**q[-1]
        assert not power_compare(F(b*2**m, D), 2**b-1, 2**a, strict=True)
    print("negative controls: dropping one joint's positivity breaks C1 at b=2,3,4,5")
    for n in (2305, 2313):
        q, e, data, y = actual_check(n, 46)
        v = trace_word(n, 46)
        nd, nc = numer_fast(v[:14]), numer_fast(v[14:])
        threshold = data[2]*103 - 3**6*nc
        correction = 2**32*nd
        assert threshold == 21560735825920
        assert (correction > threshold) == (n < y) == (n == 2305)
        print(f"shared trunk n={n}: b={len(q)}, q={q}, e={e}, N_d={nd}, "
              f"threshold={threshold}, correction={correction}, admits={n < y}")
    for m, expected in ((8, 4), (27, 19), (46, 101), (54, 0), (65, 155), (73, 41)):
        count = 0
        for n in range(3, 5001, 2):
            v = trace_word(n, m)
            if 3**sum(v) < 2**m:
                x = n
                for _ in range(m):
                    x = tstep(x)
                if x > n:
                    actual_check(n, m)
                    count += 1
        assert count == expected
    print("controls: 4000 actual cascades; rung-3 formula equivalence through m=18; "
          "all 320 reported admitting starts checked (scan n<=5000)")


def census(b, m, a):
    counts = Counter()
    examples = {}
    for q, e in tuples_at(m, a, b):
        counts['tuples'] += 1
        data = cascade(q, e)
        fixed, leaves, ceiling = bounds(q, e, data)
        for name, passed in zip(('fixed', 'leaves', 'ceiling'), (fixed, leaves, ceiling)):
            counts[name] += passed
            if passed:
                examples.setdefault(name, (q, e))
        if fixed:
            potential_check(q, e, data)
        if ceiling:
            v = word(q, e)
            n = realizing_residue_fast(v)
            while n <= 2:
                n += 2**m
            if data[2]*n < numer_fast(v):
                actual_check(n, m)
                counts['admitting'] += 1
    assert counts['tuples'] == comb(a-1, b-1)*comb(m-a, b-1)
    if b <= 2 or b in (4, 5):
        assert counts['admitting'] == 0
    if b == 3:
        assert counts['admitting'] == (4 if m == 8 else 0)
    print(f"b={b} m={m} a={a}: " + ', '.join(f'{k}={counts[k]}' for k in
          ('tuples', 'fixed', 'leaves', 'ceiling', 'admitting')), flush=True)
    if counts['leaves']:
        print(f"  first positivity-leaf survivor: {examples['leaves']}", flush=True)


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--controls', action='store_true')
    p.add_argument('--census', nargs=3, type=int, metavar=('B', 'M', 'A'))
    args = p.parse_args()
    if args.controls or not args.census:
        controls()
    if args.census:
        b, m, a = args.census
        assert b >= 1 and 3**a < 2**m
        census(b, m, a)
