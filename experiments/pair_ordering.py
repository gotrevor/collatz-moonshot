#!/usr/bin/env -S uv run --quiet python3
"""Exact mixed-order inversions for primitive rational shortcut cycles."""

import argparse
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

from research_lifts import pair_energy


def ordering(word, multiplier=3, offset=1):
    if offset != 1:
        raise ValueError('pair-ordering spacing control supports offset +1 only')
    if len(word) < 2 or '0' not in word or '1' not in word:
        raise ValueError('primitive mixed-parity word of length at least two required')
    data = pair_energy(word, multiplier, offset)
    xs = list(map(Fraction, data['states']))
    odds = [x for x, bit in zip(xs, word) if bit == '1']
    evens = [x for x, bit in zip(xs, word) if bit == '0']
    pairs = []
    mixed_signed = Fraction(1)
    for o in odds:
        for e in evens:
            image_gap = multiplier * o + offset - e
            before_gap = o - e
            reversed_order = before_gap * image_gap < 0
            mixed_signed *= image_gap / before_gap
            if reversed_order:
                pairs.append([str(o), str(e)])
    m, k = len(xs), len(odds)
    c = m * (m - 1) // 2
    signed_expected = Fraction((-1)**(m - 1) * 2**c,
                               multiplier**(k * (k - 1) // 2))
    if mixed_signed != signed_expected:
        raise AssertionError('signed Vandermonde transport failed')
    if len(pairs) < m - 1 or len(pairs) % 2 != (m - 1) % 2:
        raise AssertionError('cycle permutation inversion check failed')
    positive_integral = all(x > 0 and x.denominator == 1 for x in xs)
    spacing_cap = ((multiplier - 1) // 2) * sum(map(int, odds)) if positive_integral else None
    if spacing_cap is not None and len(pairs) > spacing_cap:
        raise AssertionError('integer even-spacing bound failed')
    return {'word': word, 'multiplier': multiplier, 'offset': offset,
            'states': data['states'], 'positive_integral': positive_integral,
            'mixed_inversion_count': len(pairs), 'mixed_inversion_pairs': pairs,
            'permutation_lower_bound': m - 1,
            'mixed_pair_capacity': len(odds) * len(evens),
            'integer_spacing_upper_bound': spacing_cap,
            'mixed_signed_ratio': str(mixed_signed),
            'signed_expected_ratio': str(signed_expected)}


def main():
    if sys.argv[1:] == ['test']:
        raise SystemExit(subprocess.call(['uv', 'run', '--quiet', '--with', 'pytest',
                                          'python3', '-m', 'pytest',
                                          str(Path(__file__).with_name('test_pair_ordering.py')), '-q']))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('word')
    parser.add_argument('--multiplier', type=int, default=3)
    parser.add_argument('--offset', type=int, default=1)
    args = parser.parse_args()
    print(json.dumps(ordering(args.word, args.multiplier, args.offset), indent=2))


if __name__ == '__main__':
    main()
