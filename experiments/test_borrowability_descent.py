"""External controls for the exact quadratic height-descent CLI."""

from fractions import Fraction
from pathlib import Path
import json
import subprocess
import sys


CLI = Path(__file__).with_name('borrowability_descent.py')


def run(label):
    return json.loads(subprocess.check_output(
        [sys.executable,str(CLI),str(label)],text=True))


def run_args(*args):
    return json.loads(subprocess.check_output(
        [sys.executable,str(CLI),*(str(arg) for arg in args)],text=True))


def test_twenty_three_has_no_two_smaller_input_pair():
    got = run(23)
    # There are eleven positive odd labels below 23 and 11*12/2=66
    # unordered input pairs.  For c=13,d=17, the companion equation gives
    # b=(70*13*17)/(23*91-3*13*17)=15470/1430=119/11.
    assert got['candidate_input_pairs'] == 66
    assert got['sample_13_17_companion'] == '119/11'
    assert got['strict_descent_rules'] == []
    assert got['least_height_three_free_opposite'] == {
        'before':[23,245],'after':[37,49]}


def test_fifty_three_positive_control():
    got = run(53)
    # (35/53)*(53/80)=(37/56)*(49/74)=35/80=7/16.
    assert Fraction(35,53)*Fraction(53,80) == Fraction(37,56)*Fraction(49,74)
    assert {'remove':[37,49],'insert':[35,53]} in got['strict_descent_rules']


def test_finite_base_through_eighty_three_still_fails_at_eighty_five():
    scan = json.loads(subprocess.check_output(
        [sys.executable,str(CLI),'scan','85','300'],text=True))
    # There are 108 odd labels in [85,300), of which 36 are multiples of 3.
    assert scan['labels_checked'] == 72
    row85 = next(row for row in scan['results'] if row['label'] == 85)
    assert row85['rules'] == []
    # 3*85+1=256.  For odd b, D must have exactly eight factors of 2.
    # These are the only 3-free c<=d<85 surviving that filter.  The last
    # column is cd modulo D/256, so none permits an integral companion b.
    assert row85['dyadic_candidates'] == [
        [5,53,55,45], [37,53,67,18], [53,53,73,35]]
    assert 85 in scan['failures']
    # Positive control with all labels 3-free:
    # r19*r29=(19/29)*(29/44)=19/44=r13*r95.
    row95 = next(row for row in scan['results'] if row['label'] == 95)
    assert Fraction(19,29)*Fraction(29,44) == Fraction(13,20)*Fraction(95,143)
    assert {'remove':[19,29], 'insert':[13,95]} in row95['rules']


def test_dyadic_split_has_even_companion_denominator():
    row = run_args('split',4,2)
    # u_4=85, u_2=5, M=256, D=M(5+5)=2560.
    assert row['label'] == 85
    assert row['inputs'] == [5,5]
    assert row['cross_denominator'] == 2560
    assert row['companion'] == '5/2'
    assert not row['companion_integral']


def test_dyadic_85_needs_an_input_above_itself():
    below = run_args('dyadic',4,84)
    assert below['two_adic_candidate_pairs'] == 3
    assert below['least_rule'] is None
    extended = run_args('dyadic',4,212)
    # Direct hand check: 3*85+1=256, 3*29353+1=88060,
    # 3*149+1=448, 3*197+1=592.
    assert Fraction(85,256)*Fraction(29353,88060) == (
        Fraction(149,448)*Fraction(197,592))
    assert extended['least_rule'] == {
        'remove':[149,197], 'insert':[85,29353],
        'companion':29353, 'max_input':197}


def test_dyadic_family_does_not_give_a_uniform_obstruction():
    before = run_args('dyadic',5,340)
    assert before['label'] == 341
    assert before['least_rule'] is None
    after = run_args('dyadic',8,21844)
    # 3*21845+1=65536, 3*3683+1=11050,
    # 3*5461+1=16384, 3*7453+1=22360.
    assert Fraction(21845,65536)*Fraction(3683,11050) == (
        Fraction(5461,16384)*Fraction(7453,22360))
    assert after['least_rule'] == {
        'remove':[5461,7453], 'insert':[3683,21845],
        'companion':3683, 'max_input':7453}
