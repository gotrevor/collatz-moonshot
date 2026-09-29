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
from fractions import Fraction
from math import gcd, lcm
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


SUPPLY_INPUTS = {
    'x64':[3349,124032], 'z64':[785,29070],
    'x79':[3005,151680], 'z79':[5635,284400],
}
SUPPLIED_HEADS = {'c64':[16745,620160], 'c79':[10217,515712]}


def direct_closure():
    """Solve all 4-by-2 affine progression intersections over the integers."""
    rows = []
    for source,(source_base,source_step) in SUPPLY_INPUTS.items():
        for head,(head_base,head_step) in SUPPLIED_HEADS.items():
            divisor = gcd(source_step,head_step)
            delta = head_base-source_base
            rows.append({'input':source,'head':head,
                         'slope_gcd':divisor,'base_difference':delta,
                         'difference_mod_gcd':delta%divisor,
                         'integer_parameter_solution_possible':delta%divisor==0})
    return {'status':'direct-two-class-closure-obstructed',
            'scope':'exact equality of one input progression and one supplied-head '
                    'progression; rules using other labels are not excluded',
            'comparisons':rows,
            'all_eight_impossible':all(not row['integer_parameter_solution_possible']
                                       for row in rows)}


def generic_root_dilation():
    """Mechanically lift four complete-neighbor rows by root-matched paths.

    This yields smaller-input rules on sparse subprogressions of the two
    supply classes.  It does not construct units for the new inputs.
    """
    outputs = []
    for name,(u,target_step) in SUPPLY_INPUTS.items():
        strict = [row for row in research.quadratic_neighbors(u)['nontrivial_exchanges']
                  if max(row['after']) < u and
                  all(label%3 for label in row['before']+row['after'])]
        strict.sort(key=lambda row:(max(row['after']),sum(row['after']),
                                    max(row['before'])))
        if not strict:
            outputs.append({'input':name,'status':'no-base-strict-row'})
            continue
        row = strict[0]
        b = next(label for label in row['before'] if label != u)
        x,z = row['after']
        # q is the deformation parameter.  Replacing t by 3q in the
        # connected-root construction preserves each label modulo 6.
        U = [u,3*u*(3*x+1)*(3*u+1)]
        B = [b,9*u*b*(3*x+1)]
        X = [x,3*x*(3*x+1)*(3*u+1)]
        Z = [z,9*x*z*(3*u+1)]
        zero = lambda L:Fraction(-L[0],L[1])
        pole = lambda L:Fraction(-(3*L[0]+1),3*L[1])
        roots = (zero(U)==zero(X) and pole(U)==zero(B) and
                 pole(X)==zero(Z) and pole(B)==pole(Z))
        valid = (identity(U,B,X,Z) and roots and
                 all(base%2 and base%3 and step%6==0
                     for base,step in (U,B,X,Z)) and
                 all(L[0]<u and L[1]<U[1] for L in (B,X,Z)))
        if not valid:
            raise ValueError(f'generic root dilation failed for {name}')
        divisor = gcd(U[1],target_step)
        outputs.append({'input':name,'status':'strict-affine-subprogression',
                        'base_rule':row,
                        'coefficients':{'u':U,'b':B,'x':X,'z':Z},
                        'root_matching_exact':roots,
                        'polynomial_identity_exact':True,
                        'target_parameter_period':U[1]//divisor,
                        'deformation_parameter_step':target_step//divisor,
                        'borrowing_prerequisites_constructed':False})
    by_name = {row['input']:row for row in outputs}
    return {'status':'two-level-supply-rules-only',
            'scope':'generic dilation of one complete-neighbor base row per input; '
                    'new smaller labels still require legal borrowing',
            'rules':outputs,
            'simultaneous_target_parameter_periods':{
                '64':lcm(by_name['x64']['target_parameter_period'],
                         by_name['z64']['target_parameter_period']),
                '79':lcm(by_name['x79']['target_parameter_period'],
                         by_name['z79']['target_parameter_period'])}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('scan','control','closure','dilate','test'))
    args = parser.parse_args()
    if args.command == 'test':
        return subprocess.call(['uv','run','--quiet','--with','pytest',
                                'python3','-m','pytest',
                                str(Path(__file__).with_name('test_affine_scan.py')),'-q'])
    if args.command == 'scan':
        result = scan()
    elif args.command == 'closure':
        result = direct_closure()
    elif args.command == 'dilate':
        result = generic_root_dilation()
    else:
        result = {'five_head_symbolic_control':five_head_control()}
    print(json.dumps(result,indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
