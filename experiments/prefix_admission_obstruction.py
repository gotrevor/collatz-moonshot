#!/usr/bin/env python3
"""All-parameter Q=2, L=6 counterfamily certificate, plus finite controls.

Proof: PREFIX-ADMISSION-OBSTRUCTION-2026-09-13.md. This pads the existing
short-run family; only the all-parameter prefix margin is new mathematics.
Full admission is computed separately, with no universal claim about its sign.
"""
from argparse import ArgumentParser
from itertools import product
import json
from math import gcd
from pathlib import Path

from short_run_obstruction import (
    A, B, X, Y, F, affine, cascade, encode, interval_certificate,
    iterate, numer_fast, primitive, realizing_residue_affine,
    realizing_residue_fast, trace_word, word,
)

DEFECT = (X,) + (Y,)*17
REPEAT, END = A*2, A*12+DEFECT
LOW, HIGH, SLACK = F(34, 5), F(225), F(8, 5)
DEFECT_NUMER = 305184819419292989
NUMER_COEFF = 2976838904967456448
MARGIN_COEFF = 409787117366273728


def canonical(v):
    r = realizing_residue_affine(v)
    return r if r > 2 else r+2**len(v)


def prefix_certificate():
    """Finite endpoint facts used by the all-j induction in the proof note."""
    interval_certificate()  # Preserve the original certificate unchanged.
    assert numer_fast(word(*zip(*DEFECT))) == DEFECT_NUMER
    assert affine(DEFECT) == (
        F(3**35, 2**53), F(DEFECT_NUMER+2**53-3**35, 2**53))
    assert NUMER_COEFF == 29*3**35+5*DEFECT_NUMER
    assert MARGIN_COEFF == NUMER_COEFF-285*2**53 > 0
    assert affine(REPEAT) == (F(729, 1024), F(1003, 512))
    assert affine(REPEAT)[0]*HIGH+affine(REPEAT)[1] == F(166031, 1024)
    certificates = []
    for pattern in (REPEAT, END):
        r, s = affine(pattern)
        assert 0 < r < 1
        assert LOW <= r*LOW+s <= r*HIGH+s <= HIGH
        lo, hi, slacks = LOW, HIGH, []
        for q, e in pattern:
            assert 1 <= q <= 2 and 1 <= e <= 2
            slacks.append(lo-2**q)
            assert slacks[-1] >= SLACK > 0
            t = F(3**q, 2**(q+e))
            assert t > 0
            lo, hi = t*lo+1-F(1, 2**e), t*hi+1-F(1, 2**e)
        certificates.append(dict(pattern=pattern, r=r, s=s,
                                 image=(lo, hi), lower_slacks=slacks))
    r, s = affine(END)
    assert r == F(3**71, 2**113)
    assert HIGH-(r*HIGH+s) == F(1171081197571096040226910222706003, 2**113)
    assert r*LOW+s == F(47216795331893147, 703687441776640)
    assert r*LOW+s-58 == F(6402923708848027, 703687441776640) > 0
    prefix = word(*zip(*END))[:6]
    assert prefix == [True, False, True, True, False, True]
    assert word(*zip(*(REPEAT+REPEAT)))[:6] == prefix
    assert sum(prefix) == 4 and numer_fast(prefix) == 119
    assert canonical(prefix) == realizing_residue_fast(prefix) == 57
    assert [n for n in range(64) if trace_word(n, 6) == prefix] == [57]
    return certificates


def baseline_controls():
    """Finite rotations and the initial <=4-block common-interval search.

    Failure here only concerns these probes / this sufficient certificate.
    It is not a bound on S2 or an exhaustive search of possible constructions.
    """
    rotations = []
    for k in range(9):
        pattern = A*k+B
        for cut in range(len(pattern)):
            rotated = pattern[cut:]+pattern[:cut]
            v = word(*zip(*rotated))
            r, s = affine(rotated)
            N, D = numer_fast(v), 2**len(v)-3**sum(v)
            assert F(N, D) == s/(1-r)-1
            c6, cm = canonical(v[:6]), canonical(v)
            assert N-D*c6 < 0 and N-D*cm < 0
            rotations.append(dict(k=k, cut=cut, N=N, D=D, c6=c6, cm=cm,
                                  prefix_margin=N-D*c6, full_margin=N-D*cm))
    macros = []
    for size in range(1, 5):
        for pattern in product(((1, 1), (1, 2), (2, 1), (2, 2)), repeat=size):
            r, s = affine(pattern)
            if r >= 1:
                continue
            h = s/(1-r)
            z, slacks = h, []
            for q, e in pattern:
                slacks.append(z-2**q)
                z = F(3**q, 2**(q+e))*z+1-F(1, 2**e)
            if min(slacks) > 0:
                macros.append((pattern, r, s, h))
    passing = 0
    for p, r, s, h in macros:
        c6 = canonical(word(*zip(*(p*3)))[:6])
        for d, rd, sd, hd in macros:
            low = min(h, hd)
            if rd*low+sd <= c6+1:
                continue
            slacks = []
            for pattern in (p, d):
                z = low
                for q, e in pattern:
                    slacks.append(z-2**q)
                    z = F(3**q, 2**(q+e))*z+1-F(1, 2**e)
            passing += min(slacks) > 0
    assert len(rotations) == 99 and len(macros) == 18 and passing == 0
    return dict(rotations=rotations, positive_macros=len(macros),
                passing_common_interval_pairs=passing)


def probe(j):
    k = 2*j+12
    pattern = REPEAT*j+END
    assert pattern == A*k+DEFECT
    q, e = zip(*pattern)
    v = word(q, e)
    a, m, D, P, H, T, U = cascade(q, e)
    b = len(q)
    assert (b, a, m) == (4*j+42, 6*j+71, 10*j+113)
    assert 5*a-3*m == 16 and a % 2 == m % 2 == 1
    assert gcd(a, m) == 1 and primitive(v)
    R = F(3**a, 2**m)
    assert R == affine(END)[0]*F(27, 32)**(2*j) < 1
    N = numer_fast(v)
    assert D == 2**53*32**k-3**35*27**k > 0
    assert 5*N == NUMER_COEFF*32**k-29*3**35*27**k
    assert N == 2**q[0]*U+3**a
    w0 = F(U+2**(m-q[0]), D)
    zs = [2**qi*(p*w0+t)/h for qi, p, h, t in zip(q, P, H, T)]
    assert zs[0] == 1+F(N, D)
    for i, (qi, ei) in enumerate(pattern):
        assert zs[(i+1) % b] == F(3**qi, 2**(qi+ei))*zs[i]+1-F(1, 2**ei)
    slacks = [z-2**qi for z, qi in zip(zs, q)]
    assert min(slacks) >= SLACK
    assert all(LOW <= zs[i] <= HIGH for i in range(0, 4*j+1, 4))
    rend, send = affine(END)
    assert rend*LOW+send <= zs[0] <= HIGH
    c6, cm = canonical(v[:6]), canonical(v)
    assert c6 == 57 and cm % 64 == c6
    if j <= 2:
        assert cm == realizing_residue_fast(v)
    assert trace_word(cm, m) == v
    prefix_margin, full_margin = N-D*c6, N-D*cm
    assert 5*prefix_margin == MARGIN_COEFF*32**k+256*3**35*27**k > 0
    assert prefix_margin >= (rend*LOW+send-58)*D > 0
    assert full_margin == 2**m*(iterate(cm, m)-cm)
    # Full rejection here is a FINITE regression observation, not an all-j proof.
    assert full_margin < 0
    return dict(j=j, k=k, q=q, e=e, b=b, a=a, m=m, R=R, z=zs,
                joint_slacks=slacks, N=N, D=D, c6=c6, cm=cm,
                prefix_margin=prefix_margin, full_margin=full_margin,
                primitive_witness=dict(five_a_minus_three_m=16, a_odd=True,
                                       m_odd=True, gcd=1),
                prefix_admits=True, fully_admits=False)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path, help='retain all exact certificate/probe data')
    args = parser.parse_args()
    certificate = prefix_certificate()
    baseline = baseline_controls()
    rows = [probe(j) for j in list(range(33))+[64, 128, 256]]
    print('PASS: 99 finite old-family rotations reject; initial 18 positive short '
          'macros yield no passing common-interval pair')
    print('PASS: interval [34/5,225], internal slack >=8/5, Q=2; '
          '(XY)^(2j+12) X Y^17, j>=0')
    print('PASS: all-j certificate m=10j+113, a=6j+71; '
          '5a-3m=16 and odd counts certify primitivity')
    print('PASS: c6=57; 5*(N-57D)=409787117366273728*32^k '
          '+256*3^35*27^k>0, k=2j+12')
    for row in rows[:2]:
        print(' '.join(f'{key}={row[key]}' for key in
                      ('j', 'b', 'a', 'm', 'N', 'D', 'c6', 'cm',
                       'prefix_margin', 'full_margin')))
    print(f'PASS: {len(rows)} exact finite probes j=0..32,64,128,256; '
          'all full margins negative in these probes only')
    if args.json:
        args.json.write_text(json.dumps(dict(interval_certificate=certificate,
                                            baseline=baseline, probes=rows),
                                        default=encode, indent=2)+'\n')


if __name__ == '__main__':
    main()
