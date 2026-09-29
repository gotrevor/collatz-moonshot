#!/usr/bin/env -S uv run --quiet python3
"""Exact one-step quadratic height-descent control, separate from closure.

Run ``./borrowability_descent.py test`` for the external CLI regression suite.
"""

from fractions import Fraction
from pathlib import Path
import argparse
import json
import subprocess
import sys


import research_lifts as research


def direct_pair_descent(a):
    """Independently solve for the unbounded companion b for c,d<a.

    r_a r_b=r_c r_d implies
      [a(3(c+d)+1)-3cd] b = (3a+1)cd.
    Thus a finite list of c,d checks all positive b without cutting b off.
    """
    if a < 3 or a % 2 == 0:
        raise ValueError('odd a >= 3 required')
    rows = []
    candidates = 0
    for c in range(1,a,2):
        for d in range(c,a,2):
            candidates += 1
            denominator = a*(3*(c+d)+1)-3*c*d
            numerator = (3*a+1)*c*d
            if denominator <= 0:
                continue
            b = Fraction(numerator,denominator)
            if b.denominator == 1 and b.numerator > 0 and b.numerator % 2:
                if sorted((a,b.numerator)) == [c,d]:
                    continue
                assert (Fraction(a,research.step(a)) *
                        Fraction(b.numerator,research.step(b.numerator)) ==
                        Fraction(c,research.step(c)) *
                        Fraction(d,research.step(d)))
                rows.append({'remove':[c,d], 'insert':sorted([a,b.numerator])})
    neighbors = research.quadratic_neighbors(a)['nontrivial_exchanges']
    three_free = [row for row in neighbors
                  if all(u%3 for u in row['before']+row['after'])]
    best = min(three_free,key=lambda row:max(row['after'])) if three_free else None
    return {'label':a,'candidate_input_pairs':candidates,
            'strict_descent_rules':rows,
            'complete_neighbor_count':len(neighbors),
            'three_free_neighbor_count':len(three_free),
            'least_height_three_free_opposite':best,
            'sample_13_17_companion':str(Fraction((3*a+1)*13*17,
                             a*(3*(13+17)+1)-3*13*17)) if a>17 else None}


def formula_scan(lower, upper):
    """Scan odd 3-free labels using only the exact c,d<a formula.

    Require c,d to be 3-free too, as every label in a value-one word must be.
    No complete-neighbor enumeration and no companion bound is used.
    """
    results = []
    for a in range(lower | 1, upper, 2):
        if a % 3 == 0:
            continue
        inputs = [c for c in range(1, a, 2) if c % 3]
        rules = []
        dyadic = []
        power = 3*a+1
        shift = (power & -power).bit_length()-1
        for i,c in enumerate(inputs):
            for d in inputs[i:]:
                denominator = a*(3*(c+d)+1)-3*c*d
                numerator = power*c*d
                if denominator > 0 and numerator % denominator == 0:
                    b = numerator // denominator
                    if b > 0 and b % 2 and sorted((a,b)) != [c,d]:
                        rules.append({'remove':[c,d], 'insert':sorted([a,b])})
                if power == 1 << shift and denominator % (1 << shift) == 0 \
                        and denominator % (1 << (shift+1)) != 0:
                    reduced = denominator >> shift
                    dyadic.append([c,d,reduced,(c*d) % reduced])
        results.append({'label':a, 'rules':rules, 'dyadic_candidates':dyadic})
    return {'lower':lower, 'upper_exclusive':upper,
            'labels_checked':len(results),
            'failures':[row['label'] for row in results if not row['rules']],
            'results':results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('label', nargs='?', type=int)
    args = parser.parse_args()
    if args.label is None:
        parser.error('label required')
    print(json.dumps(direct_pair_descent(args.label),indent=2))


if __name__ == '__main__':
    if sys.argv[1:] == ['test']:
        raise SystemExit(subprocess.call(['uv','run','--quiet','--with','pytest',
            'python3','-m','pytest',str(Path(__file__).with_name(
                'test_borrowability_descent.py')),'-q']))
    if len(sys.argv) == 4 and sys.argv[1] == 'scan':
        print(json.dumps(formula_scan(int(sys.argv[2]),int(sys.argv[3])),indent=2))
        raise SystemExit(0)
    main()
