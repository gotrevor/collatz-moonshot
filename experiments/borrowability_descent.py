#!/usr/bin/env -S uv run --quiet python3
"""Exact one-step quadratic height-descent control, separate from closure.

Run ``./borrowability_descent.py test`` for the external CLI regression suite.
"""

from fractions import Fraction
from pathlib import Path
import argparse
import json
import math
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


def dyadic_intro(j, input_ceiling):
    """Exact bounded-input search for u_j=(4^j-1)/3, unbounded companion.

    The 2-adic sieve is necessary for an odd companion b, and is exact at
    the relevant denominator valuation.  Once c,d pass it, b is solved by
    the cross-multiplied identity, with no upper bound on b.
    """
    if j < 2 or input_ceiling < 1:
        raise ValueError('j>=2 and positive input ceiling required')
    u = (4**j-1)//3
    if u % 3 == 0:
        raise ValueError('u_j is 3-divisible when j is divisible by 3')
    M = 4**j
    labels = [(c, ((3*c+1) & -(3*c+1)).bit_length()-1)
              for c in range(1, input_ceiling+1, 2) if c % 3]
    labels.sort(key=lambda item:item[1], reverse=True)
    candidates = 0
    rules = []
    for i, (c, vc) in enumerate(labels):
        if vc + labels[0][1] <= 2*j:
            break
        for d, vd in labels[i:]:
            if vc + vd <= 2*j:
                break
            candidates += 1
            D = u*(3*(c+d)+1)-3*c*d
            numerator = M*c*d
            if D <= 0 or numerator % D:
                continue
            b = numerator//D
            if b <= 0 or b % 2 == 0 or sorted((u,b)) == sorted((c,d)):
                continue
            assert (Fraction(u,research.step(u))*Fraction(b,research.step(b)) ==
                    Fraction(c,research.step(c))*Fraction(d,research.step(d)))
            rules.append({'remove':sorted([c,d]), 'insert':sorted([u,b]),
                          'companion':b, 'max_input':max(c,d)})
    rules.sort(key=lambda row:(row['max_input'],row['remove']))
    return {'j':j, 'label':u, 'three_free':True,
            'input_ceiling':input_ceiling,
            'two_adic_candidate_pairs':candidates,
            'solutions':len(rules),
            'least_max_input':rules[0]['max_input'] if rules else None,
            'least_rule':rules[0] if rules else None}


def complementary_split(j, i):
    """Natural factorization 4^j=4^i*4^(j-i) has no odd companion."""
    if j < 2 or not 0 < i < j:
        raise ValueError('need j>=2 and 0<i<j')
    u = (4**j-1)//3
    c = (4**i-1)//3
    d = (4**(j-i)-1)//3
    D = u*(3*(c+d)+1)-3*c*d
    assert D == 4**j*(c+d)
    b = Fraction(c*d,c+d)
    assert b.denominator % 2 == 0
    return {'j':j,'i':i,'label':u,'inputs':[c,d],
            'cross_denominator':D,
            'companion':str(b),'companion_integral':False}


def _small_factors(n):
    """Prime factorization for the small cross denominators in this control."""
    factors = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            n //= p
            factors[p] = factors.get(p,0)+1
        p += 1 if p == 2 else 2
    if n > 1:
        factors[n] = factors.get(n,0)+1
    return factors


def local_global_23():
    """Finite modulus certifying the existing two-smaller-input obstruction.

    L is the lcm of all cross denominators.  If D*b=70*c*d modulo L for
    any candidate pair, then D divides 70*c*d, hence the rational companion
    is actually integral.  The incumbent 23 certificate says none is.
    """
    u = 23
    rows = []
    prime_powers = {}
    for c in range(1,u,2):
        for d in range(c,u,2):
            D = u*(3*(c+d)+1)-3*c*d
            K = (3*u+1)*c*d
            assert D > 0
            q = D//math.gcd(D,K)
            assert q > 1
            rows.append((c,d,D,K,q))
            for p,e in _small_factors(D).items():
                prime_powers[p] = max(prime_powers.get(p,0),e)
    modulus = math.lcm(*(row[2] for row in rows))
    assert modulus == math.prod(p**e for p,e in prime_powers.items())
    # A smaller, non-optimal prime-power cover: p blocks a pair when p is
    # present in its reduced denominator, at exponent v_p(K)+1.
    coverage = {}
    exponent = {}
    for i,(_,_,_,K,q) in enumerate(rows):
        for p in _small_factors(q):
            coverage.setdefault(p,set()).add(i)
            n = K
            val = 0
            while n % p == 0:
                n //= p
                val += 1
            exponent[p] = max(exponent.get(p,0),val+1)
    remaining = set(range(len(rows)))
    selected = []
    while remaining:
        p = max(coverage,key=lambda p:(len(coverage[p] & remaining),-p))
        assert coverage[p] & remaining
        selected.append(p)
        remaining -= coverage[p]
    cover = math.prod(p**exponent[p] for p in selected)
    for _,_,D,K,_ in rows:
        # Linear congruence D*b=K (mod cover) is solvable iff gcd(D,cover)|K.
        assert K % math.gcd(D,cover) != 0
    witnesses = []
    for c,d in [(1,1),(13,17)]:
        row = next(row for row in rows if row[:2] == (c,d))
        witnesses.append({'inputs':[c,d], 'D':row[2], 'K':row[3],
                          'rational_companion':str(Fraction(row[3],row[2])),
                          'reduced_denominator':row[4]})
    assert math.gcd(*(row['reduced_denominator'] for row in witnesses)) == 1
    return {'target':u, 'input_pairs':len(rows),
            'separate_local_witnesses':witnesses,
            'universal_modulus':modulus,
            'universal_modulus_factors':{str(p):e for p,e in sorted(prime_powers.items())},
            'greedy_cover_modulus':cover,
            'greedy_cover_factors':{str(p):exponent[p] for p in sorted(selected)},
            'raw_modulus_has_solution':False}


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
    if len(sys.argv) == 4 and sys.argv[1] == 'dyadic':
        print(json.dumps(dyadic_intro(int(sys.argv[2]),int(sys.argv[3])),indent=2))
        raise SystemExit(0)
    if len(sys.argv) == 4 and sys.argv[1] == 'split':
        print(json.dumps(complementary_split(int(sys.argv[2]),int(sys.argv[3])),indent=2))
        raise SystemExit(0)
    if sys.argv[1:] == ['local-global-23']:
        print(json.dumps(local_global_23(),indent=2))
        raise SystemExit(0)
    main()
