#!/usr/bin/env python3
"""Exact certificate for the Q=2 primitive rational-positivity obstruction.

The all-k proof is in SHORT-RUN-OBSTRUCTION-2026-09-13.md. The finite interval
certificate supports that proof; the sampled cycles alone are not its proof.
Use --json PATH to retain every q, e, z, slack, N, D, and canonical n0.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
import json
from math import gcd
from pathlib import Path

from block_composition import cascade, word
from paradoxical import (iterate, numer_fast, realizing_residue_affine,
                         realizing_residue_fast, trace_word)

X, Y = (1, 1), (2, 1)
A, B = (X, Y), (X, Y, Y)
LOW, HIGH, SLACK = F(34, 5), F(434, 13), F(8, 5)


def affine(pattern):
    r, s = F(1), F(0)
    for q, e in pattern:
        t = F(3**q, 2**(q+e))
        r, s = t*r, t*s + 1-F(1, 2**e)
    return r, s


def interval_certificate():
    """Positive slopes reduce interval and internal-slack claims to endpoints."""
    assert affine(A) == (F(27, 32), F(17, 16))
    assert affine(B) == (F(243, 256), F(217, 128))
    certificates = []
    for pattern in (A, B):
        r, s = affine(pattern)
        assert 0 < r < 1
        assert LOW <= r*LOW+s <= r*HIGH+s <= HIGH
        lo, hi, slacks = LOW, HIGH, []
        for q, e in pattern:
            assert 1 <= q <= 2 and 1 <= e <= 2
            slacks.append(lo-2**q)
            assert lo-2**q >= SLACK > 0
            t = F(3**q, 2**(q+e))
            assert t > 0
            lo, hi = t*lo+1-F(1, 2**e), t*hi+1-F(1, 2**e)
        certificates.append(dict(pattern=pattern, r=r, s=s,
                                 image=(lo, hi), lower_slacks=slacks))
    # This common prefix alone excludes integer admission for every k >= 0.
    prefix = word(*zip(*A)) + [True]
    assert prefix == [True, False, True, True, False, True]
    assert numer_fast(prefix) == 119
    assert realizing_residue_fast(prefix) == 57
    assert realizing_residue_affine(prefix) == 57
    assert [n for n in range(64) if trace_word(n, 6) == prefix] == [57]
    assert HIGH-1 == F(421, 13) < 57
    return certificates


def primitive(v):
    """Literal nonempty/not-a-proper-power meaning of FrontB.Primitive."""
    return bool(v) and all(v != v[:d]*(len(v)//d)
                           for d in range(1, len(v)) if len(v) % d == 0)


def probe(k):
    pattern = A*k+B
    q, e = zip(*pattern)
    v = word(q, e)
    a, m, D, P, H, T, U = cascade(q, e)
    b = len(q)
    assert (b, a, m) == (2*k+3, 3*k+5, 5*k+8)
    # For any proper power, its exponent divides both a and m, hence 1.
    assert 5*a-3*m == 1 and gcd(a, m) == 1 and primitive(v)
    R = F(3**a, 2**m)
    assert R == F(243, 256)*F(27, 32)**k <= F(243, 256) < 1
    N = numer_fast(v)
    assert D == 256*32**k-243*27**k > 0
    assert 5*N == 9152*32**k-7047*27**k
    assert N == 2**q[0]*U+3**a
    # Closed recurrence formula checked independently of the cascade.
    t = F(27, 32)**k
    z0 = (F(163, 20)-F(4131, 640)*t)/(1-F(243, 256)*t)
    assert z0 == F(N, D)+1
    w0 = F(U+2**(m-q[0]), D)
    zs = [2**qi*(p*w0+ti)/h for qi, p, h, ti in zip(q, P, H, T)]
    assert zs[0] == z0
    for i, (qi, ei) in enumerate(pattern):
        assert zs[(i+1) % b] == F(3**qi, 2**(qi+ei))*zs[i]+1-F(1, 2**ei)
    slacks = [z-2**qi for z, qi in zip(zs, q)]
    assert min(slacks) >= SLACK
    assert all(LOW <= zs[i] <= HIGH for i in range(0, 2*k+1, 2))
    n0 = realizing_residue_affine(v)
    if n0 <= 2:
        n0 += 2**m
    assert 2 < n0 < 2**m and n0 % 64 == 57
    if k <= 8:
        assert n0 == realizing_residue_fast(v)
    if k == 0:
        assert n0 == 249
    else:
        prev = word(*zip(*(A*(k-1)+B)))
        nprev = realizing_residue_affine(prev)
        assert n0 == ((32*nprev-29)*pow(27, -1, 2**m)) % 2**m
    assert trace_word(n0, m) == v
    margin = N-D*n0
    assert F(N, D) <= HIGH-1 < n0
    assert margin == 2**m*(iterate(n0, m)-n0) < 0
    assert margin <= -F(320, 13)*D
    return dict(k=k, q=q, e=e, b=b, a=a, m=m, R=R, z=zs,
                joint_slacks=slacks, min_slack=min(slacks), N=N, D=D,
                n0=n0, admission_margin=margin, primitive=True, admits=False)


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path, help='write all exact finite probe data')
    args = parser.parse_args()
    certificate = interval_certificate()
    parameters = list(range(33))+[64, 128, 256]
    rows = [probe(k) for k in parameters]
    print('PASS: exact common interval [34/5,434/13]; joint slack >= 8/5; Q=2')
    print('PASS: all-k certificate: m=5k+8, a=3k+5, 5a-3m=1, R<=243/256')
    print('PASS: prefix TFTTFT forces n0=57 mod 64 > N/D; no family member admits')
    for row in rows[:4]:
        print(f"k={row['k']} m={row['m']} z0={row['z'][0]} "
              f"min_slack={row['min_slack']} n0={row['n0']} "
              f"N-D*n0={row['admission_margin']}")
    print(f'PASS: {len(rows)} exact finite cycles, k=0..32,64,128,256; '
          'all vertices, literal primitivity, cascade, residue, and admission checked')
    if args.json:
        args.json.write_text(json.dumps(dict(interval_certificate=certificate,
                                            probes=rows), default=encode, indent=2)+'\n')


if __name__ == '__main__':
    main()
