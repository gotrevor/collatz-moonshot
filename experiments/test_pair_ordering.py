"""Hand-computed ordering anchors through the real pair-ordering CLI."""

import json
import subprocess
import sys
from pathlib import Path


CLI = Path(__file__).with_name('pair_ordering.py')


def run(*args):
    return json.loads(subprocess.check_output([sys.executable, str(CLI), *args], text=True))


def test_trivial_positive_cycle():
    # 1<2<3*1+1, so the only mixed pair reverses order.
    got = run('10')
    assert got['states'] == ['1', '2']
    assert got['mixed_inversion_pairs'] == [['1', '2']]
    assert got['mixed_inversion_count'] == got['permutation_lower_bound'] == 1
    assert got['integer_spacing_upper_bound'] == 1
    assert got['mixed_signed_ratio'] == '-2'


def test_positive_primitive_rational_cycle_saturates_mixed_capacity():
    # 00101 visits (28,14,7,22,11)/23.  Both odd states 7,11 lie below
    # all three even states 14,22,28; both images lie above all three.
    got = run('00101')
    assert got['states'] == ['28/23', '14/23', '7/23', '22/23', '11/23']
    assert got['mixed_inversion_count'] == got['mixed_pair_capacity'] == 6
    assert got['permutation_lower_bound'] == 4
    assert got['mixed_signed_ratio'] == '1024/3'
    assert got['integer_spacing_upper_bound'] is None


def test_large_real_gap_rational_cycle_attains_lower_bound():
    # Existing closed 3x+1 control, with all real gaps >1.
    got = run('11111000')
    assert got['mixed_inversion_count'] == got['permutation_lower_bound'] == 7
    assert got['mixed_signed_ratio'] == '-268435456/59049'


def test_negative_3x_plus_1_cycle_uses_reversed_interval():
    # -5 and -7 are odd, -10 is even; -14<-10<-5 and -20<-10<-7.
    got = run('110')
    assert got['states'] == ['-5', '-7', '-10']
    assert got['mixed_inversion_pairs'] == [['-5', '-10'], ['-7', '-10']]
    assert got['mixed_inversion_count'] == 2
    assert got['mixed_signed_ratio'] == '8/3'
    assert got['integer_spacing_upper_bound'] is None


def test_positive_integer_5x_plus_1_control():
    got = run('1110000', '--multiplier', '5')
    assert got['states'] == ['13', '33', '83', '208', '104', '52', '26']
    assert got['mixed_inversion_count'] == got['permutation_lower_bound'] == 6
    assert got['mixed_signed_ratio'] == '2097152/125'
    assert got['integer_spacing_upper_bound'] == 258


def test_nonprimitive_word_rejected_by_cycle_constructor():
    bad = subprocess.run([sys.executable, str(CLI), '1010'],
                         capture_output=True, text=True)
    assert bad.returncode != 0
    assert 'primitive cycle required' in bad.stderr


def test_offset_outside_plus_one_scope_rejected():
    bad = subprocess.run([sys.executable, str(CLI), '110', '--offset', '-1'],
                         capture_output=True, text=True)
    assert bad.returncode != 0
    assert 'offset +1 only' in bad.stderr
