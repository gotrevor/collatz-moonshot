"""Hand-computed controls through the shipped pair-denominator CLI."""

import json
import subprocess
import sys
from pathlib import Path


CLI = Path(__file__).with_name('pair_denominators.py')


def run(*args):
    return json.loads(subprocess.check_output([sys.executable, str(CLI), *args], text=True))


def test_small_nonintegral_cycle_has_three_denominator_gaps():
    # 001 visits 4/5, 2/5, 1/5.  All three numerator differences are 1, 2, or 3.
    got = run('ledger', '001')
    assert got['states'] == ['4/5', '2/5', '1/5']
    assert got['common_reduced_denominator'] == 5
    assert got['prime_ledgers']['5']['deficit_through_denominator'] == 3
    assert got['prime_ledgers']['5']['excess_beyond_denominator'] == 0
    assert got['prime_ledgers']['5']['vandermonde_valuation'] == -3


def test_genuine_closed_cycle_has_a_supercollision():
    # 00001111 visits numerators 208,104,52,26,13,37,73,127 over 35.
    # The pair 52 and 127 differs by 75=3*5^2: its rational gap is 15/7.
    got = run('ledger', '00001111')
    assert got['states'] == ['208/35', '104/35', '52/35', '26/35',
                             '13/35', '37/35', '73/35', '127/35']
    assert got['common_reduced_denominator'] == 35
    five = got['prime_ledgers']['5']
    assert (five['deficit_through_denominator'],
            five['excess_beyond_denominator'], five['vandermonde_valuation']) == (22, 1, -21)
    assert five['adjacent_edge_deficit_lower_bound'] == 8
    pair = next(row for row in five['pairs'] if row['indices'] == [2, 7])
    assert (pair['multiplier_collision_valuation'],
            pair['numerator_gap_valuation'], pair['gap_valuation']) == (1, 2, 1)
    seven = got['prime_ledgers']['7']
    assert (seven['deficit_through_denominator'],
            seven['excess_beyond_denominator'], seven['vandermonde_valuation']) == (25, 0, -25)


def test_large_real_gap_rational_cycle_still_has_denominator_deficit():
    # 11111000 has denominator 13 and 28 pairs; two gaps have a factor 13.
    got = run('ledger', '11111000')
    assert got['common_reduced_denominator'] == 13
    assert got['prime_ledgers']['13']['numerator_gap_valuation_counts'] == {'0': 26, '1': 2}
    assert got['prime_ledgers']['13']['vandermonde_valuation'] == -26


def test_sign_and_other_map_controls_are_distinct():
    assert run('ledger', '110')['states'] == ['-5', '-7', '-10']
    five = run('ledger', '1110000', '--multiplier', '5')
    assert five['states'] == ['13', '33', '83', '208', '104', '52', '26']
    assert five['common_reduced_denominator'] == 1
    assert five['prime_ledgers'] == {}


def test_generalized_odd_edge_need_not_have_full_deficit():
    # This is a negative 5x+1 cycle, not a positive 3x+1 candidate.
    # Numerator gaps are 14,21,15,7,1,6, hence three v3=0 and three v3=1.
    got = run('ledger', '0011', '--multiplier', '5')
    assert got['states'] == ['-28/9', '-14/9', '-7/9', '-13/9']
    row = got['prime_ledgers']['3']
    assert row['denominator_exponent'] == 2
    assert row['numerator_gap_valuation_counts'] == {'0': 3, '1': 3}
    assert row['adjacent_edge_deficit_lower_bound'] == 6
    assert (row['deficit_through_denominator'],
            row['excess_beyond_denominator'], row['vandermonde_valuation']) == (9, 0, -9)


def test_small_census_and_primitive_guard():
    # Through length 3: 01 is the integral 1,2 cycle; 001 is nonintegral.
    got = run('scan', '--depth', '3')
    assert got['positive_primitive_cycles_examined'] == 2
    assert got['positive_nonintegral_cycles_examined'] == 1
    assert got['nonnegative_prime_examples'] == []
    bad = subprocess.run([sys.executable, str(CLI), 'ledger', '1010'],
                         capture_output=True, text=True)
    assert bad.returncode != 0
    assert 'primitive cycle required' in bad.stderr
