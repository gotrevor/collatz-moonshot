"""External controls for the exact quadratic height-descent CLI."""

from fractions import Fraction
from pathlib import Path
import json
import math
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


def test_separate_prime_adic_witnesses_at_fixed_target_23():
    row = run_args('local-global-23')
    assert row['target'] == 23
    assert row['input_pairs'] == 66
    assert row['separate_local_witnesses'] == [
        {'inputs':[1,1], 'D':158, 'K':70,
         'rational_companion':'35/79', 'reduced_denominator':79},
        {'inputs':[13,17], 'D':1430, 'K':15470,
         'rational_companion':'119/11', 'reduced_denominator':11}]
    # Both rational companions are positive and odd/3-free locally;
    # coprime reduced denominators let one witness work at every prime.
    assert math.gcd(79,11) == 1
    for b in (Fraction(35,79), Fraction(119,11)):
        assert b > 0
        assert math.gcd(b.numerator,6) == math.gcd(b.denominator,6) == 1
    assert Fraction(23,70)*Fraction(35,184) == Fraction(1,4)**2
    assert Fraction(23,70)*Fraction(119,368) == (
        Fraction(13,40)*Fraction(17,52))


def test_finite_joint_modulus_blocks_every_smaller_input_pair():
    row = run_args('local-global-23')
    M = row['universal_modulus']
    cover = row['greedy_cover_modulus']
    assert M % 158 == 0 and M % 1430 == 0
    # D is always 2 mod4.  D(11,13)=1250=2*5^4 and
    # D(1,9)=686=2*7^3; monotonicity gives D<=D(21,21)=1598,
    # below 5^5 and 7^4, so these are the maximal exponents.
    assert row['universal_modulus_factors']['2'] == 1
    assert row['universal_modulus_factors']['5'] == 4
    assert row['universal_modulus_factors']['7'] == 3
    assert math.prod(int(p)**e for p,e in
                     row['universal_modulus_factors'].items()) == M
    assert math.prod(int(p)**e for p,e in
                     row['greedy_cover_factors'].items()) == cover
    assert cover < M
    # The linear congruence D*b=K mod N has an integer solution iff
    # gcd(D,N) divides K.  This checks all 66 pairs without searching b.
    for c in range(1,23,2):
        for d in range(c,23,2):
            D = 23*(3*(c+d)+1)-3*c*d
            K = 70*c*d
            assert D > 0 and M % D == 0
            assert K % math.gcd(D,M) != 0
            assert K % math.gcd(D,cover) != 0
