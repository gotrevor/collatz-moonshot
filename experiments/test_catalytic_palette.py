"""Persistent controls through the real catalytic_palette command line."""

from fractions import Fraction
from pathlib import Path
import json
import subprocess
import sys


CLI = Path(__file__).with_name('catalytic_palette.py')
WITNESS = Path(__file__).with_name('catalytic_palette_71_witness.json')


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


def test_integer_basis_uses_Z_span_not_Q_span():
    # 1 lies in the rational span of {2}, but not 2Z.  It lies in
    # 2Z+3Z since 3-2=1.
    got = run('basis-controls')
    assert got['two_Z_target_one']['remainder'] == {'7': 1}
    assert got['two_three_Z_target_one']['remainder'] == {}
    assert got['two_three_Z_target_one']['replay'] == 1


def test_targeted_integer_search_regenerates_a_witness():
    got = run('lattice71', '--max-aux-label', 100000,
              '--neighbor-waves', 1, '--wave-width', 10)
    assert got['unresolved_remainder'] == []
    assert got['witness']
    assert got['partial_combination'] is None
    assert all(all(label%3 for label in row['remove']+row['insert'])
               for row in got['witness'])


def test_seventy_one_legal_repair_replays_through_cli():
    got = run('replay71', WITNESS)
    source, target = dict(got['source']), dict(got['target'])
    assert source[0] == 16 and sum(source.values()) == 32
    assert target[0] == 28 and sum(target.values()) == 65
    assert got['forced_net_moves'] == {
        'U2':0,'U8':9,'U13':-3,'cubic_forward':-3}
    assert got['vector_replay_exact'] is True
    assert got['borrowed_word_value_one'] is True
    assert got['full_repair_replay_exact'] is True
    assert got['catalyst_missing_borrowability'] == []
    word, catalyst = dict(got['borrow_unit']), dict(got['catalyst'])
    assert all(word[label] >= count for label,count in catalyst.items())
    # Direct arithmetic: T(55)=83, T(95)=143, T(35)=53,
    # T(5035)=7553; T(1079)=1619, T(1007)=1511, T(7555)=11333.
    assert Fraction(55,83)*Fraction(95,143) == Fraction(35,53)*Fraction(5035,7553)
    assert Fraction(1079,1619)*Fraction(5035,7553) == Fraction(1007,1511)*Fraction(7555,11333)
    assert got['borrowability_extra_rule'] == {
        'remove':[1079,5035],'insert':[1007,7555]}


def test_replay_rejects_corrupted_integer_coefficient(tmp_path):
    corrupted = json.loads(WITNESS.read_text())
    corrupted['witness'][0]['coefficient'] += 1
    path = tmp_path/'bad-witness.json'
    path.write_text(json.dumps(corrupted))
    result = subprocess.run([sys.executable,str(CLI),'replay71',str(path)],
                            capture_output=True,text=True)
    assert result.returncode != 0
    assert 'does not reproduce target-source' in result.stderr


def test_replay_rejects_nonquadratic_or_even_rules(tmp_path):
    for replacement in ([2, 3], [5, 55, 83]):
        corrupted=json.loads(WITNESS.read_text())
        corrupted['witness'][0]['remove']=replacement
        path=tmp_path/'invalid-rule.json'
        path.write_text(json.dumps(corrupted))
        result=subprocess.run([sys.executable,str(CLI),'replay71',str(path)],capture_output=True,text=True)
        assert result.returncode != 0
        assert 'positive odd pairs required' in result.stderr
