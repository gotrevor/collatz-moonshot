#!/usr/bin/env -S uv run --quiet python3
"""Exact sampled affine quadratic scan for the lower five-head family.

``./affine_scan.py scan`` checks complete fixed-label neighbor tables at
h=0,1,2,3.  A zero match rules out only affine rows passing through the
specified two sampled heights, with both opposite inputs below n there,
nonnegative slopes, and labels coprime to 3 at both samples.  It is not a
classification of all affine families or congruence classes.
In particular, h=2 mod 95 and h=1 mod 79 each meet the sampled set
{0,1,2,3} only once, so their positive symbolic rows are outside this scan.
"""

from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
import argparse
import json
import subprocess
import sys


LIFTS = Path(__file__).with_name('research_lifts.py')
spec = spec_from_file_location('research_lifts', LIFTS)
assert spec and spec.loader
research = module_from_spec(spec)
spec.loader.exec_module(research)


def mul(a,b):
    result = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            result[i+j] += x*y
    return result


def product(*polynomials):
    result = [1]
    for polynomial in polynomials:
        result = mul(result,polynomial)
    return result


def affine_at_samples(first,second):
    return [first,second-first]


def denominator(polynomial):
    return [3*polynomial[0]+1,3*polynomial[1]]


def identity(u,b,c,d):
    """Polynomial form of r_u*r_b=r_c*r_d; factors of 2 cancel."""
    return product(u,b,denominator(c),denominator(d)) == product(
        c,d,denominator(u),denominator(b))


def five_head_control():
    """Hand-derived r_(5n) r_(17s)=r_n r_(25s), n=(85s+1)/2."""
    s = [217,384]
    n = [(85*s[0]+1)//2,85*s[1]//2]
    return identity([5*x for x in n],[17*x for x in s],n,[25*x for x in s])


def scan():
    tables = {}
    for h in range(4):
        s = 217+384*h
        c = 17*s
        n = (85*s+1)//2
        rows = research.quadratic_neighbors(c)['nontrivial_exchanges']
        tables[h] = [row for row in rows if
                     all(u%3 for u in row['before']+row['after']) and
                     max(row['after']) < n]
    comparisons = []
    for h0,h1 in ((0,2),(1,3),(0,3)):
        s0,s1 = 217+384*h0,217+384*h1
        u0,u1 = 17*s0,17*s1
        n0,n1 = (85*s0+1)//2,(85*s1+1)//2
        u = affine_at_samples(u0,u1)
        n = affine_at_samples(n0,n1)
        candidates = 0
        polynomial_matches = []
        for first in tables[h0]:
            b0 = next(x for x in first['before'] if x != u0)
            c0,d0 = first['after']
            for second in tables[h1]:
                b1 = next(x for x in second['before'] if x != u1)
                # Both pairings are required: the two affine input lines
                # could cross between the sampled heights.
                for c1,d1 in (second['after'],second['after'][::-1]):
                    b = affine_at_samples(b0,b1)
                    c = affine_at_samples(c0,c1)
                    d = affine_at_samples(d0,d1)
                    if min(b[1],c[1],d[1]) < 0:
                        continue
                    if (c[1] > n[1] or d[1] > n[1] or
                            c0 >= n0 or d0 >= n0):
                        continue
                    candidates += 1
                    if identity(u,b,c,d):
                        polynomial_matches.append({'b':b,'c':c,'d':d})
        comparisons.append({'sample_heights':[h0,h1],
                            'nonnegative_below_n_affine_candidates':candidates,
                            'exact_polynomial_matches':polynomial_matches})
    return {'status':'sampled-affine-scan',
            'scope':'Q rows at listed sampled heights with 3-free labels; '
                    'both opposite inputs below n; nonnegative affine slopes',
            'positive_subclasses_outside_sample_pairs':[
                'h=2 mod 95','h=1 mod 79'],
            'below_n_row_counts':{str(h):len(rows) for h,rows in tables.items()},
            'comparisons':comparisons,
            'five_head_symbolic_control':five_head_control()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('scan','control','test'))
    args = parser.parse_args()
    if args.command == 'test':
        return subprocess.call(['uv','run','--quiet','--with','pytest',
                                'python3','-m','pytest',
                                str(Path(__file__).with_name('test_affine_scan.py')),'-q'])
    result = scan() if args.command == 'scan' else {
        'five_head_symbolic_control':five_head_control()}
    print(json.dumps(result,indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
