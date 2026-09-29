#!/usr/bin/env -S uv run --quiet python3
"""Exact known-path profiles for the fixed inverse-five Collatz certificate."""

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

import catalytic_palette
import research_lifts


INVERSE_FIVE_ODDS = [7, 7, 11, 17, 55, 65, 83]


def odd_counts(path):
    return Counter(u for u in path[:-1] if u % 2)


def sorted_counts(counts):
    return [[u, counts[u]] for u in sorted(counts) if counts[u]]


def profile(n):
    data = research_lifts.wild_five_repair(n)
    ledger = catalytic_palette.palette_ledger(n)
    actual = data['actual_path']
    smaller = data['smaller_path']
    virtual = data['virtual_prefix'] + smaller[1:]
    actual_odds = odd_counts(actual)
    virtual_odds = odd_counts(virtual)
    virtual_odds.update(INVERSE_FIVE_ODDS)
    actual_only = actual_odds - virtual_odds
    virtual_only = virtual_odds - actual_odds
    ai, si = data['meeting_steps']
    assert actual[ai:] == smaller[si:]
    mismatch = {u: actual_odds[u]-virtual_odds[u]
                for u in actual_odds.keys() | virtual_odds.keys()
                if u % 3 == 0 and actual_odds[u] != virtual_odds[u]}
    assert actual_odds[3] == virtual_odds[3] == 0
    actual_three = {u: c for u, c in actual_odds.items() if u % 3 == 0}
    virtual_three = {u: c for u, c in virtual_odds.items() if u % 3 == 0}
    assert actual_three == ({n: 1} if n % 3 == 0 else {})
    assert virtual_three == ({5*n: 1} if n % 3 == 0 else {})
    assert data['smaller_endpoint'] == 45*((n-7)//64)+5
    return {
        'n': n, 'k': (n-7)//64, 'smaller_endpoint': data['smaller_endpoint'],
        'virtual_six_step_prefix': data['virtual_prefix'],
        'actual_steps': len(actual)-1,
        'smaller_steps': len(smaller)-1,
        'meeting_value': data['meeting'],
        'meeting_steps_actual_smaller': [ai, si],
        'shared_tail_steps': len(actual)-1-ai,
        'actual_prefix_parity_to_meeting': ''.join(str(u%2) for u in actual[:ai]),
        'actual_prefix_to_meeting': actual[:ai+1],
        'smaller_prefix_to_meeting': smaller[:si+1],
        'actual_only_odd_labels': sorted_counts(actual_only),
        'virtual_only_odd_labels': sorted_counts(virtual_only),
        'common_odd_factor_count': sum((actual_odds & virtual_odds).values()),
        'forced_net_moves': ledger['forced_net_moves'],
        'r3_multiplicity_actual_virtual': [actual_odds[3], virtual_odds[3]],
        'three_divisible_label_difference': sorted_counts(mismatch),
        'has_three_divisible_label_mismatch': bool(mismatch),
    }


def fixed_offset_descent(family, j):
    if family == 'plus':
        if j < 11:
            raise ValueError('plus formula requires j>=11')
        c, length, odds, base_endpoint = 7, 11, 5, 1
    elif family == 'minus':
        if j < 8:
            raise ValueError('minus formula requires j>=8')
        c, length, odds, base_endpoint = -57, 8, 5, -53
    else:
        raise ValueError('family must be plus or minus')
    n = 2**j + c
    predicted = 3**odds * 2**(j-length) + base_endpoint
    actual = n
    bits = []
    for _ in range(length):
        bits.append(str(actual % 2))
        actual = research_lifts.step(actual)
    assert actual == predicted and 0 < actual < n
    return {'family': family, 'j': j, 'n': n, 'steps': length,
            'parity_prefix': ''.join(bits), 'endpoint': actual,
            'formula': f'243*2^({j}-{length}){base_endpoint:+d}',
            'strict_descent': actual < n}


def long_growth(j):
    """A 7 mod 64 family forced to climb for six steps plus j odd steps."""
    if j < 2:
        raise ValueError('long-growth construction requires j>=2')
    modulus = 2**j
    k = (-11 * pow(81, -1, modulus)) % modulus
    if k % 3 == 2:
        k += modulus
    n = 64*k+7
    p = 81*k+10
    assert (p+1) % modulus == 0 and n % 3 != 0
    six = [n]
    for _ in range(6):
        six.append(research_lifts.step(six[-1]))
    assert six[-1] == p and all(x > n for x in six[1:])
    x = p
    for _ in range(j):
        assert x % 2 == 1 and x > n
        x = research_lifts.step(x)
    s = (p+1)//modulus
    endpoint = 3**j*s-1
    assert x == endpoint and endpoint > n
    return {'j': j, 'k': k, 'n': n, 'initial_six': six,
            'post_six': p, 'odd_run_length': j, 's': s,
            'endpoint_after_six_plus_j': endpoint,
            'no_descent_through_six_plus_j': True}


def lower_prefix(h):
    """The fixed six-step word and ensuing odd run in the lower five-head family."""
    if h < 0:
        raise ValueError('lower-prefix requires h>=0')
    k = 144 + 255*h
    n, c, d = 9223 + 16320*h, 3689 + 6528*h, 5425 + 9600*h
    six = [64*k+7, 96*k+11, 144*k+17, 216*k+26,
           108*k+13, 162*k+20, 81*k+10]
    p = six[-1]
    assert six[0] == n and p+1 == 11675+20655*h
    assert all(x > n for x in six[1:]) and 0 < c < n and 0 < d < n
    # For p odd, the next v_2(p+1) shortcut steps are odd.  For p even,
    # this run is empty; the immediate halving is reported separately.
    run = 0
    s = p+1
    while s % 2 == 0:
        run += 1
        s //= 2
    odd_run = [3**i * 2**(run-i) * s - 1 for i in range(1, run+1)]
    endpoint = odd_run[-1] if odd_run else p
    assert endpoint > n and all(x > n for x in odd_run)
    if h % 2 == 0:
        descent_step, descent_endpoint = 7, p//2
    elif h % 4 == 1:
        descent_step, descent_endpoint = 8, (3*p+1)//4
    else:
        descent_step, descent_endpoint = None, None
    if descent_step is not None:
        assert descent_endpoint < n
    return {'h': h, 'k': k, 'n': n, 'c': c, 'd': d,
            'initial_six': six, 'post_six': p,
            'odd_run_length': run, 's': s, 'odd_run_prefix': odd_run,
            'rising_prefix_steps': 6+run,
            'endpoint_after_six_plus_odd_run': endpoint,
            'no_descent_through_six_plus_odd_run': True,
            'first_obvious_descent_step': descent_step,
            'first_obvious_descent_endpoint': descent_endpoint}


def lower_growth(j):
    """Least nonnegative h forcing at least j odd steps after the fixed six."""
    if j < 2:
        raise ValueError('lower-growth construction requires j>=2')
    modulus = 2**j
    h = (-11675 * pow(20655, -1, modulus)) % modulus
    result = lower_prefix(h)
    assert (result['post_six']+1) % modulus == 0
    assert result['odd_run_length'] >= j
    return {'requested_min_odd_run': j, 'residue_modulus': modulus,
            **result}


def oriented_rules(witness_path):
    data = json.loads(Path(witness_path).read_text())
    if not isinstance(data.get('witness'), list):
        raise ValueError('witness file must contain a signed quadratic witness list')
    rules = Counter()
    for row in data['witness']:
        left, right = tuple(row['remove']), tuple(row['insert'])
        coefficient = row['coefficient']
        if not coefficient:
            raise ValueError('zero-coefficient witness row')
        if coefficient < 0:
            left, right = right, left
        rules[(left, right)] += abs(coefficient)
    return rules


def target_tail(base_n, other_n):
    base_orbit = research_lifts.orbit_to_one(base_n)
    other_orbit = research_lifts.orbit_to_one(other_n)
    base_index = {u: i for i, u in enumerate(base_orbit)}
    other_i = next(i for i, u in enumerate(other_orbit) if u in base_index)
    join = other_orbit[other_i]
    base_i = base_index[join]
    assert other_orbit[other_i:] == base_orbit[base_i:]
    return {'base_n': base_n, 'other_n': other_n,
            'target_tail_join': join,
            'target_tail_join_steps_other_base': [other_i, base_i],
            'shared_target_tail_steps': len(other_orbit)-1-other_i}


def compare_witnesses(base_n, base_path, other_n, other_path):
    base, other = oriented_rules(base_path), oriented_rules(other_path)
    shared = base.keys() & other.keys()
    tail = target_tail(base_n, other_n)
    distinguished = {
        'virtual_first_5n': 5*other_n,
        'virtual_second': (15*other_n+1)//2,
        'actual_first_n': other_n,
    }
    touches = {}
    for name, label in distinguished.items():
        rows = [(left, right, coefficient) for (left, right), coefficient in other.items()
                if label in left+right]
        touches[name] = {'label': label, 'unique_oriented_rules': len(rows),
                         'weighted_applications': sum(row[2] for row in rows)}
    return {**tail,
            'base_unique_oriented_Q_rules': len(base),
            'other_unique_oriented_Q_rules': len(other),
            'shared_unique_oriented_Q_rules': len(shared),
            'shared_weighted_applications': sum(min(base[r], other[r]) for r in shared),
            'distinguished_label_rule_touches': touches}


def family_table():
    rows = []
    seen = {}
    for family, cases in (
        ('plus', [(j, 2**j+7) for j in range(6,17)]),
        ('minus', [(j, 2**j-57) for j in range(6,17)]),
        ('holdout', [(k, 64*k+7) for k in (2,3,5,9,17)]),
        ('growth', [(j, long_growth(j)['n']) for j in (2,4,6,8,10,12,16,20)]),
    ):
        for parameter, n in cases:
            if n in seen:
                rows[seen[n]]['aliases'].append([family, parameter])
                continue
            row = profile(n)
            seen[n] = len(rows)
            rows.append({'family': family, 'parameter': parameter, 'aliases': [], 'n': n,
                         'actual_steps': row['actual_steps'],
                         'meeting_steps_actual_smaller': row['meeting_steps_actual_smaller'],
                         'meeting_value': row['meeting_value'],
                         'shared_tail_steps': row['shared_tail_steps'],
                         'initial_parity_16': row['actual_prefix_parity_to_meeting'][:16],
                         'residual_actual_labels': len(row['actual_only_odd_labels']),
                         'residual_virtual_labels': len(row['virtual_only_odd_labels']),
                         'forced_net_moves': row['forced_net_moves'],
                         'three_divisible_label_difference': row['three_divisible_label_difference']})
    return {'rows': rows,
            'symbolic_controls': [fixed_offset_descent('plus', j) for j in (11,12,16)] +
                                 [fixed_offset_descent('minus', j) for j in (8,9,16)],
            'long_growth_controls': [long_growth(j) for j in (2,4,6,8,10,12,16,20)]}


def main():
    if sys.argv[1:] == ['test']:
        raise SystemExit(subprocess.call(['uv', 'run', '--quiet', '--with', 'pytest',
                                          'python3', '-m', 'pytest',
                                          str(Path(__file__).with_name('test_repair_family.py')), '-q']))
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    one = sub.add_parser('profile')
    one.add_argument('n', type=int)
    formula = sub.add_parser('descent')
    formula.add_argument('family', choices=['plus', 'minus'])
    formula.add_argument('j', type=int)
    growth = sub.add_parser('growth')
    growth.add_argument('j', type=int)
    lower = sub.add_parser('lower-prefix')
    lower.add_argument('h', type=int)
    lower_growing = sub.add_parser('lower-growth')
    lower_growing.add_argument('j', type=int)
    comparison = sub.add_parser('compare')
    comparison.add_argument('base_n', type=int)
    comparison.add_argument('base_witness')
    comparison.add_argument('other_n', type=int)
    comparison.add_argument('other_witness')
    tail = sub.add_parser('target-tail')
    tail.add_argument('base_n', type=int)
    tail.add_argument('other_n', type=int)
    sub.add_parser('family')
    args = parser.parse_args()
    result = (profile(args.n) if args.command == 'profile' else
              fixed_offset_descent(args.family, args.j) if args.command == 'descent' else
              long_growth(args.j) if args.command == 'growth' else
              lower_prefix(args.h) if args.command == 'lower-prefix' else
              lower_growth(args.j) if args.command == 'lower-growth' else
              compare_witnesses(args.base_n, args.base_witness, args.other_n,
                                args.other_witness) if args.command == 'compare' else
              target_tail(args.base_n, args.other_n) if args.command == 'target-tail' else
              family_table())
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
