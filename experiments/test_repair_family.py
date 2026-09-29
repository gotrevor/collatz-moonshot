"""Hand-computed family anchors through the shipped repair-family CLI."""

import json
import subprocess
import sys
from pathlib import Path


CLI = Path(__file__).with_name('repair_family.py')


def run(*args):
    return json.loads(subprocess.check_output([sys.executable, str(CLI),
                                               *map(str, args)], text=True))


def test_seven_preserves_the_inverse_five_construction_history():
    # 5*7=35 -> 53 -> 80 -> 40 -> 20 -> 10 -> 5, then the smaller path.
    got = run('profile', 7)
    assert got['smaller_endpoint'] == 5
    assert got['virtual_six_step_prefix'] == [35, 53, 80, 40, 20, 10, 5]
    assert got['meeting_value'] == 5
    assert got['meeting_steps_actual_smaller'] == [7, 0]
    assert got['actual_only_odd_labels'] == [[13, 1]]
    assert got['r3_multiplicity_actual_virtual'] == [0, 0]


def test_three_divisible_source_is_a_search_scope_control():
    # n=135, 5n=675.  Each contributes the full 3-adic charge in its own
    # certificate.  The 71 search excluded these labels, but legal Q rules do not.
    got = run('profile', 135)
    assert got['smaller_endpoint'] == 95
    assert got['virtual_six_step_prefix'] == [675, 1013, 1520, 760, 380, 190, 95]
    assert got['three_divisible_label_difference'] == [[135, 1], [675, -1]]
    assert got['r3_multiplicity_actual_virtual'] == [0, 0]
    assert got['has_three_divisible_label_mismatch'] is True


def test_fixed_offset_templates_are_strict_descent_controls():
    # 7's 11-step word has five odds and ends at 1; -57's first eight steps
    # have five odds and end at -53.  The added 2^j term tracks the slope.
    plus = run('descent', 'plus', 11)
    assert plus['n'] == 2055
    assert plus['endpoint'] == 244
    assert plus['steps'] == 11
    minus = run('descent', 'minus', 8)
    assert minus['n'] == 199
    assert minus['endpoint'] == 190
    assert minus['steps'] == 8


def test_deliberate_long_growth_congruence():
    # j=2: 81*1+11=92=4*23; j=6: 81*37+11=3008=64*47.
    # After six steps p=81k+10=2^j*s-1, then j increasing odd steps.
    a = run('growth', 2)
    assert (a['k'], a['n'], a['post_six'], a['s'],
            a['endpoint_after_six_plus_j']) == (1, 71, 91, 23, 206)
    b = run('growth', 6)
    assert (b['k'], b['n'], b['post_six'], b['s'],
            b['endpoint_after_six_plus_j']) == (37, 2375, 3007, 47, 34262)
    assert b['no_descent_through_six_plus_j'] is True


def test_family_table_deduplicates_overlapping_examples():
    # 35 requested slots; 71 appears thrice, 135 twice, 199 twice: 31 starts.
    got = run('family')
    assert len(got['rows']) == 31
    assert sum(len(row['aliases']) for row in got['rows']) == 4
    assert len(got['long_growth_controls']) == 8
    assert all(row['n'] % 64 == 7 for row in got['rows'])


def test_actual_target_tail_overlap_is_not_a_repair_rule():
    # 199 reaches 182 at step 16; 71 reaches 182 at step 5.
    got = run('target-tail', 71, 199)
    assert got['target_tail_join'] == 182
    assert got['target_tail_join_steps_other_base'] == [16, 5]
    assert got['shared_target_tail_steps'] == 60
    # 263 occurs at index 14 on the 71 trajectory, so its entire path is a suffix.
    suffix = run('target-tail', 71, 263)
    assert suffix['target_tail_join_steps_other_base'] == [0, 14]
    assert suffix['shared_target_tail_steps'] == 51


def test_out_of_domain_input_rejected():
    bad = subprocess.run([sys.executable, str(CLI), 'profile', '8'],
                         capture_output=True, text=True)
    assert bad.returncode != 0
    assert 'n=7 mod64' in bad.stderr
