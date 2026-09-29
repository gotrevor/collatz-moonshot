#!/usr/bin/env -S uv run --quiet python3
"""Exact, finite controls for the catalytic certificate palette.

``./catalytic_palette.py test`` delegates to the external pytest suite.
The relation ledger is a necessary condition for a repair, not a path finder.
The closure uses quadratic exchanges after unit seeding; it does not claim
completeness for all uses of the essential cubic.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path
import argparse
import importlib.util
import json
import subprocess
import sys

LIFTS = Path(__file__).with_name('research_lifts.py')
spec = importlib.util.spec_from_file_location('research_lifts', LIFTS)
assert spec and spec.loader
research = importlib.util.module_from_spec(spec)
spec.loader.exec_module(research)

UNIT8 = Counter([19, 25, 29, 55, 83])
UNIT13 = Counter([5, 7, 7, 11, 17, 55, 65, 83])
CUBIC_LEFT = Counter([5, 55, 83])
CUBIC_RIGHT = Counter([11, 13, 17])


def counts(path):
    twos, odds = research.factor_counts(path)
    return twos, odds


def unit_value(twos, odds):
    value = Fraction(2**twos)
    for label, multiplicity in odds.items():
        value *= Fraction(label, research.step(label))**multiplicity
    return value


def palette_ledger(n):
    """Solve the complete rank-4 count system for known n=7 mod 64 paths.

Variables are signed net insertions of U2, U8, U13, and forward cubics.
Positive cubic means {5,55,83} -> {11,13,17}.  Quadratic exchanges
preserve all four recorded counts.  This never assumes arbitrary units.
"""
    data = research.wild_five_repair(n)
    actual_twos, actual_odds = counts(data['actual_path'])
    virtual = data['virtual_prefix'] + data['smaller_path'][1:]
    virtual_twos, virtual_odds = counts(virtual)
    virtual_twos += 2
    virtual_odds.update([7, 7, 11, 17, 55, 65, 83])
    assert actual_twos == data['actual_twos']
    assert virtual_twos == data['virtual_twos']
    assert unit_value(actual_twos, actual_odds) == n
    assert unit_value(virtual_twos, virtual_odds) == n

    dt = actual_twos - virtual_twos
    dk = sum(actual_odds.values()) - sum(virtual_odds.values())
    dm1 = actual_odds[1] - virtual_odds[1]
    dm5 = actual_odds[5] - virtual_odds[5]
    u2 = dm1
    u8 = 5*(dk-u2) - 8*(dt-u2)
    u13 = 5*(dt-u2) - 3*(dk-u2)
    cubic = u13-dm5
    assert (dt, dk, dm1, dm5) == (
        u2+3*u8+5*u13, u2+5*u8+8*u13,
        u2, u13-cubic)
    return {
        'n': n,
        'source': {'twos': virtual_twos,
                   'odd_count': sum(virtual_odds.values()),
                   'm1': virtual_odds[1], 'm5': virtual_odds[5]},
        'target': {'twos': actual_twos,
                   'odd_count': sum(actual_odds.values()),
                   'm1': actual_odds[1], 'm5': actual_odds[5]},
        'delta': {'twos': dt, 'odd_count': dk, 'm1': dm1, 'm5': dm5},
        'forced_net_moves': {'U2': u2, 'U8': u8, 'U13': u13,
                             'cubic_forward': cubic},
        'known_target_steps': len(data['actual_path'])-1,
        'certificate_value': str(unit_value(actual_twos, actual_odds)),
    }


def borrowable_closure(max_label=3077, max_rounds=2, target=71):
    """Bounded quadratic support closure via *complete* pair fibers.

    If a,b each occur in borrowable unit words, take their product, replace
    a,b by any equal-value c,d, and obtain a unit containing c,d.  Returned
    witnesses are actual quadratic edges; exhaustion is only within the
    specified rounds and label ceiling.
    """
    if max_label < 1 or max_rounds < 0:
        raise ValueError('nonnegative rounds and positive label ceiling required')
    seed = {1, *UNIT8, *UNIT13}
    known = {u for u in seed if u <= max_label}
    first_seen = {u: 0 for u in known}
    witness = {}
    evaluated = set()
    pruned_labels = set()
    target_path = research.orbit_to_one(target)
    target_labels = set(u for u in target_path[:-1] if u % 2)
    round_complete = False
    for round_no in range(1, max_rounds+1):
        before = sorted(known)
        added = set()
        for a, b in combinations_with_replacement(before, 2):
            if (a, b) in evaluated:
                continue
            evaluated.add((a, b))
            ratio = Fraction(a, research.step(a))*Fraction(b, research.step(b))
            for c, d in research.two_odd_fiber(ratio)['unordered_odd_pairs']:
                for u in (c,d):
                    if u > max_label:
                        pruned_labels.add(u)
                        continue
                    if u not in known and u not in added:
                        witness[u] = {'round': round_no, 'remove': [a,b],
                                      'insert': [c,d]}
                        first_seen[u] = round_no
                        added.add(u)
        known.update(added)
        if not added:
            round_complete = True
            break
    return {'seed': sorted(seed), 'max_label': max_label,
            'max_rounds': max_rounds, 'known_labels': sorted(known),
            'target': target, 'target_odd_labels': sorted(target_labels),
            'target_labels_missing': sorted(target_labels-known),
            'first_seen': {str(k):v for k,v in sorted(first_seen.items())},
            'witness': {str(k):v for k,v in sorted(witness.items())},
            'pairs_evaluated': len(evaluated),
            'pruned_label_count': len(pruned_labels),
            'round_complete': round_complete}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest='command', required=True)
    ledger = subs.add_parser('ledger')
    ledger.add_argument('n', type=int)
    closure = subs.add_parser('closure')
    closure.add_argument('--max-label', type=int, default=3077)
    closure.add_argument('--max-rounds', type=int, default=2)
    closure.add_argument('--target', type=int, default=71)
    subs.add_parser('test')
    args = parser.parse_args()
    if args.command == 'test':
        return subprocess.call(['uv', 'run', '--quiet', '--with', 'pytest',
                                'python3', '-m', 'pytest',
                                str(Path(__file__).with_name('test_catalytic_palette.py')),
                                '-q'])
    if args.command == 'ledger':
        result = palette_ledger(args.n)
    else:
        result = borrowable_closure(args.max_label, args.max_rounds, args.target)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
