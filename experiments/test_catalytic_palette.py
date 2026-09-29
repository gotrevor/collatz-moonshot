"""Persistent controls through the real catalytic_palette command line."""

from fractions import Fraction
from pathlib import Path
import json
import subprocess
import sys


CLI = Path(__file__).with_name('catalytic_palette.py')


def run(*args):
    return json.loads(subprocess.check_output(
        [sys.executable, str(CLI), *map(str, args)], text=True))


def test_seventy_one_count_lattice():
    # Six virtual prefix edges include four even edges, the 17-step path
    # from 50 contributes ten even and seven odd edges, and the inverse-5
    # certificate adds two even and seven odd factors: (16,16).
    # The known 71 path has 28 even and 37 odd edges.  The source and
    # target each contain one r5 and no r1.  Solve the 2x2 system:
    # 3a+5b=12, 5a+8b=21, giving a=9, b=-3.  Then c=b=-3.
    got = run('ledger', 71)
    assert got['source'] == {'twos': 16, 'odd_count': 16, 'm1': 0, 'm5': 1}
    assert got['target'] == {'twos': 28, 'odd_count': 37, 'm1': 0, 'm5': 1}
    assert got['forced_net_moves'] == {
        'U2': 0, 'U8': 9, 'U13': -3, 'cubic_forward': -3}
    assert got['known_target_steps'] == 65
    assert got['certificate_value'] == '71'


def test_seven_control_has_the_opposite_unit_flow():
    # The virtual certificate for 7 has 9 even, 10 odd factors.  The
    # familiar path 7,11,17,26,13,20,10,5,8,4,2,1 has 6 even and 5 odd.
    got = run('ledger', 7)
    assert got['delta'] == {'twos': -3, 'odd_count': -5, 'm1': 0, 'm5': 0}
    assert got['forced_net_moves'] == {
        'U2': 0, 'U8': -1, 'U13': 0, 'cubic_forward': 0}


def test_first_round_borrows_121_and_13_with_exact_pairs():
    # r11*r17 = (11/17)*(17/26) = 11/26
    #          = (7/11)*(121/182) = r7*r121.
    # r19*r29 = (19/29)*(29/44) = 19/44
    #          = (13/20)*(95/143) = r13*r95.
    got = run('closure', '--max-label', 3077, '--max-rounds', 1)
    assert got['witness']['121']['remove'] == [11, 17]
    assert got['witness']['121']['insert'] == [7, 121]
    assert got['witness']['13']['remove'] == [19, 29]
    assert got['witness']['13']['insert'] == [13, 95]
    assert Fraction(11, 26) == Fraction(7, 11)*Fraction(121, 182)
    assert Fraction(19, 44) == Fraction(13, 20)*Fraction(95, 143)
    assert 121 in got['known_labels']
    assert 71 in got['target_labels_missing']
    assert got['round_complete'] is False


def test_bounded_rounds_do_not_claim_failure_as_obstruction():
    got = run('closure', '--max-label', 3077, '--max-rounds', 2)
    # r35*r65 = (35/53)*(65/98) = r23*r1625 = (23/35)*(1625/2438)
    #         = r25*r247 = (25/38)*(247/371).
    assert Fraction(35, 53)*Fraction(65, 98) == Fraction(23, 35)*Fraction(1625, 2438)
    assert Fraction(35, 53)*Fraction(65, 98) == Fraction(25, 38)*Fraction(247, 371)
    assert got['witness']['23']['remove'] == [35, 65]
    assert got['witness']['23']['insert'] == [23, 1625]
    assert got['witness']['247']['remove'] == [35, 65]
    assert got['witness']['247']['insert'] == [25, 247]
    assert got['first_seen']['23'] == 2
    assert got['first_seen']['247'] == 2
    assert got['target_labels_missing']
    assert got['round_complete'] is False


def test_zero_rounds_is_a_valid_partial_snapshot():
    got = run('closure', '--max-label', 3077, '--max-rounds', 0)
    assert got['known_labels'] == got['seed']
    assert got['round_complete'] is False
