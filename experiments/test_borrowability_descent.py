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
