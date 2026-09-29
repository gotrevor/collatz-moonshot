#!/usr/bin/env -S uv run --quiet python3
"""Exact odd-prime denominator ledger for primitive shortcut cycles."""

import argparse
import json
import subprocess
import sys
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import gcd
from pathlib import Path

from research_lifts import pair_energy


def factor(n):
    factors = []
    p = 3
    while p * p <= n:
        if n % p == 0:
            r = 0
            while n % p == 0:
                n //= p
                r += 1
            factors.append((p, r))
        p += 2
    if n > 1:
        factors.append((n, 1))
    return factors


def valuation(n, p):
    if n == 0:
        raise ValueError('valuation of zero is undefined')
    n = abs(n)
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def cycle(word, multiplier=3, offset=1):
    if len(word) < 2 or '0' not in word or '1' not in word:
        raise ValueError('word must contain both parities and have length at least two')
    # Reuse the established exact constructor and closure/parity checks.
    states = list(map(Fraction, pair_energy(word, multiplier, offset)['states']))
    d = states[0].denominator
    if gcd(d, 2 * multiplier) != 1:
        raise AssertionError('unexpected cycle denominator prime')
    numerators = [int(x * d) for x in states]
    if not all(gcd(a, d) == 1 for a in numerators):
        raise AssertionError('states lack common reduced denominator')
    return d, numerators


def ledger(word, multiplier=3, offset=1, include_pairs=True):
    d, aa = cycle(word, multiplier, offset)
    m = len(aa)
    c = m * (m - 1) // 2
    primes = {}
    for p, r in factor(d):
        deficit = excess = 0
        counts = Counter()
        rows = []
        for i, j in combinations(range(m), 2):
            h = j - i
            a = word[i:j].count('1')
            collision = valuation(multiplier**a - 2**h, p)
            actual = valuation(aa[j] - aa[i], p)
            predicted = min(collision, r)
            if min(actual, r) != predicted:
                raise AssertionError('truncated multiplier-collision identity failed')
            deficit += r - predicted
            excess += max(actual - r, 0)
            counts[actual] += 1
            if include_pairs:
                rows.append({'indices': [i, j], 'odd_steps': a,
                             'multiplier_collision_valuation': collision,
                             'numerator_gap_valuation': actual,
                             'gap_valuation': actual - r})
        # Each even edge has collision valuation zero.  An odd edge has
        # multiplier collision valuation v_p(multiplier-2), which need not be
        # zero for generalized maps (e.g. 5n+1 at p=3).
        edge_lower_bound = sum(r - min(valuation((multiplier if c == '1' else 1)-2, p), r)
                               for c in word) if m > 2 else min(
                                   r - min(valuation((multiplier if c == '1' else 1)-2, p), r)
                                   for c in word)
        assert deficit >= edge_lower_bound
        primes[str(p)] = {'denominator_exponent': r,
                          'pair_count': c,
                          'deficit_through_denominator': deficit,
                          'excess_beyond_denominator': excess,
                          'vandermonde_valuation': excess - deficit,
                          'adjacent_edge_deficit_lower_bound': edge_lower_bound,
                          'numerator_gap_valuation_counts': dict(sorted(counts.items())),
                          **({'pairs': rows} if include_pairs else {})}
    return {'word': word, 'multiplier': multiplier, 'offset': offset,
            'states': [str(Fraction(a, d)) for a in aa],
            'common_reduced_denominator': d,
            'integral_states': d == 1,
            'prime_ledgers': primes}


def scan(depth):
    if depth < 3 or depth > 20:
        raise ValueError('depth must be in 3..20')
    examined = 0
    positive_nonintegral = 0
    nonnegative_prime_examples = []
    integral_vandermonde_examples = []
    for m in range(2, depth + 1):
        for bits in product('01', repeat=m):
            word = ''.join(bits)
            if '1' not in word or '0' not in word or 2**m <= 3**word.count('1'):
                continue
            rotations = [word[i:] + word[:i] for i in range(m)]
            if word != min(rotations) or len(set(rotations)) != m:
                continue
            examined += 1
            data = ledger(word, include_pairs=False)
            if data['integral_states']:
                continue
            positive_nonintegral += 1
            scores = {p: row['vandermonde_valuation']
                      for p, row in data['prime_ledgers'].items()}
            for p, v in scores.items():
                if v >= 0:
                    nonnegative_prime_examples.append([word, p, v])
            if all(v >= 0 for v in scores.values()):
                integral_vandermonde_examples.append([word, data['common_reduced_denominator']])
    return {'max_length': depth, 'positive_primitive_cycles_examined': examined,
            'positive_nonintegral_cycles_examined': positive_nonintegral,
            'nonnegative_prime_examples': nonnegative_prime_examples,
            'nonintegral_cycles_with_integral_vandermonde': integral_vandermonde_examples}


def main():
    if sys.argv[1:] == ['test']:
        raise SystemExit(subprocess.call(['uv', 'run', '--quiet', '--with', 'pytest',
                                          'python3', '-m', 'pytest',
                                          str(Path(__file__).with_name('test_pair_denominators.py')), '-q']))
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    one = sub.add_parser('ledger')
    one.add_argument('word')
    one.add_argument('--multiplier', type=int, default=3)
    one.add_argument('--offset', type=int, default=1)
    census = sub.add_parser('scan')
    census.add_argument('--depth', type=int, default=18)
    args = parser.parse_args()
    result = (ledger(args.word, args.multiplier, args.offset)
              if args.command == 'ledger' else scan(args.depth))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
