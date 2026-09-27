#!/usr/bin/env -S uv run --quiet python3
"""Exact controls for three Collatz research proposals, not a convergence test."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import json
import subprocess
import sys


def step(n):
    return (3*n+1)//2 if n%2 else n//2


def certificate(twos, odd_sources):
    """Check both commutative value and exact backward-path realization.

    A factor 2 is usable at any positive state.  A factor u/T(u) is usable
    only at T(u), where its backward edge leads to u.  Every factor is used.
    """
    if twos < 0 or any(u < 1 or u%2 == 0 for u in odd_sources):
        raise ValueError('need nonnegative twos and positive odd sources')
    value=Fraction(2**twos)*prod((Fraction(u,step(u)) for u in odd_sources),start=Fraction(1))
    counts=Counter(odd_sources)
    sources=tuple(sorted(counts))

    @lru_cache(None)
    def visit(current, left_twos, remaining):
        if not left_twos and not any(remaining):
            return (current,)
        if left_twos:
            tail=visit(2*current,left_twos-1,remaining)
            if tail is not None:
                return (current,)+tail
        for i,u in enumerate(sources):
            if remaining[i] and step(u)==current:
                next_counts=list(remaining)
                next_counts[i]-=1
                tail=visit(u,left_twos,tuple(next_counts))
                if tail is not None:
                    return (current,)+tail
        return None

    path=visit(1,twos,tuple(counts[u] for u in sources))
    return {'value':str(value),'realizable':path is not None,
            'backward_path':list(path) if path is not None else None,
            'states_examined':visit.cache_info().currsize}


def pair_energy(word, multiplier=3, offset=1):
    """Vandermonde transport on the exact rational cycle of a parity word."""
    if not word or any(c not in '01' for c in word):
        raise ValueError('nonempty binary word required')
    if multiplier < 3 or multiplier%2 == 0 or offset not in (-1,1):
        raise ValueError('positive odd multiplier >=3, offset +/-1 required')
    numer=0
    for i,c in enumerate(word):
        if c=='1':
            numer=multiplier*numer+offset*2**i
    denominator=2**len(word)-multiplier**word.count('1')
    if denominator==0:
        raise ValueError('zero cycle denominator')
    start=Fraction(numer,denominator)
    states=[]
    n=start
    for c in word:
        if n.denominator%2==0 or n.numerator%2!=int(c):
            raise AssertionError('rational parity mismatch')
        states.append(n)
        n=(multiplier*n+offset)/2 if c=='1' else n/2
    if n!=start:
        raise AssertionError('cycle did not close')
    if len(set(states))!=len(states):
        raise ValueError('primitive cycle required: repeated state')
    evens=[x for x,c in zip(states,word) if c=='0']
    odds=[x for x,c in zip(states,word) if c=='1']
    ratio=prod((abs((multiplier*o+offset-e)/(o-e)) for e in evens for o in odds),start=Fraction(1))
    m,k=len(states),len(odds)
    expected=Fraction(2**(m*(m-1)//2),multiplier**(k*(k-1)//2))
    gaps=[abs(x-y) for x,y in combinations(states,2)]
    return {'word':word,'states':list(map(str,states)),
            'mixed_ratio':str(ratio),'required_ratio':str(expected),
            'identity_holds':ratio==expected,
            'integral':all(x.denominator==1 for x in states),
            'minimum_gap':str(min(gaps)) if gaps else None}


def dyadic_ray_coefficient(n, base):
    if n < base or n%base:
        return 0
    q=n//base
    return int(q & (q-1) == 0)


def signed_fixed(odd_source, cutoff):
    """The known signed fixed series D_(3u+1)-D_u, using exact coefficients.

    Values beyond cutoff are evaluated by formula, not discarded.  Thus the
    residual check is not corrupted by a truncation boundary.
    """
    if odd_source < 1 or odd_source%2==0 or cutoff < 1:
        raise ValueError('positive odd source and positive cutoff required')
    def coefficient(n):
        return dyadic_ray_coefficient(n,3*odd_source+1)-dyadic_ray_coefficient(n,odd_source)
    negative=[]
    positive=[]
    residuals=[]
    for n in range(1,cutoff+1):
        a=coefficient(n)
        if a<0: negative.append(n)
        if a>0: positive.append(n)
        pushed=coefficient(2*n)
        if n%3==2:
            pushed+=coefficient((2*n-1)//3)
        if pushed!=a:
            residuals.append([n,pushed-a])
    return {'odd_source':odd_source,'cutoff':cutoff,'positive':positive,
            'negative':negative,'residuals':residuals}


def multiplicative_fixed(cutoff):
    """Positive sparse fixed series for G(n)=n/2 even, 3n odd.

    This is a control for arguments that forget the actual +1 map.
    The support is {2^k:k>=0} union {3^j:j>=1}.
    """
    if cutoff < 1:
        raise ValueError('positive cutoff required')
    def coefficient(n):
        if dyadic_ray_coefficient(n,1):
            return 1
        if n < 3:
            return 0
        while n%3==0:
            n//=3
        return int(n==1)
    support=[]
    residuals=[]
    for n in range(1,cutoff+1):
        a=coefficient(n)
        if a:
            support.append(n)
        pushed=coefficient(2*n)
        if n%6==3:
            pushed+=coefficient(n//3)
        if pushed!=a:
            residuals.append([n,pushed-a])
    return {'cutoff':cutoff,'support':support,'residuals':residuals}


def main():
    if sys.argv[1:]==['test']:
        raise SystemExit(subprocess.call(['uv','run','--quiet','--with','pytest','python3','-m',
            'pytest',str(Path(__file__).with_name('test_research_lifts.py')),'-q']))
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('certificate')
    p.add_argument('--twos',type=int,required=True)
    p.add_argument('--odd-sources',type=int,nargs='*',default=[])
    p=sub.add_parser('pair-energy')
    p.add_argument('word')
    p.add_argument('--multiplier',type=int,default=3)
    p.add_argument('--offset',type=int,default=1)
    p=sub.add_parser('signed-fixed')
    p.add_argument('--odd-source',type=int,default=3)
    p.add_argument('--cutoff',type=int,default=64)
    p=sub.add_parser('multiplicative-fixed')
    p.add_argument('--cutoff',type=int,default=64)
    sub.add_parser('controls')
    a=parser.parse_args()
    if a.command=='certificate': result=certificate(a.twos,a.odd_sources)
    elif a.command=='pair-energy': result=pair_energy(a.word,a.multiplier,a.offset)
    elif a.command=='signed-fixed': result=signed_fixed(a.odd_source,a.cutoff)
    elif a.command=='multiplicative-fixed': result=multiplicative_fixed(a.cutoff)
    else:
        result={
            'three_path':certificate(3,[3,5]),
            'nine_product_only':certificate(6,[3,3,5,5]),
            'nine_repaired':certificate(7,[9,7,11,17,13,5]),
            'positive_cycle':pair_energy('10'),
            'negative_cycle':pair_energy('110'),
            'rational_large_gaps':pair_energy('11111000'),
            'five_n_plus_one':pair_energy('1110000',5),
            'signed_fixed_control':signed_fixed(3,64),
            'multiplicative_map_control':multiplicative_fixed(64),
        }
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
