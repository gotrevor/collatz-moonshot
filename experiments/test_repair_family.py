"""Hand-computed family anchors through the shipped repair-family CLI."""

import json
import subprocess
import sys
from fractions import Fraction
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


def test_lower_family_prefix_has_adversarial_and_descent_controls():
    # h=43: p+1=899840=2^8*3515, so the first 14 steps rise.
    rising = run('lower-prefix', 43)
    assert (rising['n'], rising['c'], rising['d']) == (710983, 284393, 418225)
    assert (rising['post_six'], rising['odd_run_length'], rising['s']) == (899839, 8, 3515)
    assert rising['initial_six'][0] == 710983
    assert rising['initial_six'][-1] == 899839
    assert len(rising['odd_run_prefix']) == 8
    assert rising['rising_prefix_steps'] == 14
    assert rising['endpoint_after_six_plus_odd_run'] == 23061914
    assert rising['no_descent_through_six_plus_odd_run'] is True
    assert rising['first_obvious_descent_step'] is None

    # h=44: p is even, and its step-7 half lies below the start.
    short = run('lower-prefix', 44)
    assert (short['n'], short['c'], short['d']) == (727303, 290921, 427825)
    assert (short['post_six'], short['odd_run_length']) == (920494, 0)
    assert (short['first_obvious_descent_step'],
            short['first_obvious_descent_endpoint']) == (7, 460247)


def test_lower_growth_selects_least_residue_and_reports_actual_run():
    # Modulo 4: 11675+20655*h = 3+3h, whose first zero is h=3.
    first = run('lower-growth', 2)
    assert (first['h'], first['n'], first['c'], first['d']) == (3, 58183, 23273, 34225)
    assert (first['post_six'], first['odd_run_length'], first['s']) == (73639, 3, 9205)
    assert first['endpoint_after_six_plus_odd_run'] == 248534
    assert first['requested_min_odd_run'] == 2
    # The same least residue h=43 survives modulo 2^8.
    eighth = run('lower-growth', 8)
    assert (eighth['h'], eighth['odd_run_length'],
            eighth['endpoint_after_six_plus_odd_run']) == (43, 8, 23061914)


def test_lower_prefix_one_odd_step_then_step_eight_descent():
    # h=1: p=32329, T^7=48494, T^8=24247 < n=25543.
    got = run('lower-prefix', 1)
    assert (got['n'], got['post_six'], got['odd_run_prefix']) == (25543, 32329, [48494])
    assert (got['first_obvious_descent_step'],
            got['first_obvious_descent_endpoint']) == (8, 24247)


def test_two_supply_rows_compose_but_leave_a_high_virtual_frontier():
    first = run('lower-composite','class95',0)
    assert (first['h'],first['n'],first['m'],first['c'],first['d']) == (
        2,41863,29435,16745,24625)
    assert (first['x'],first['z'],first['b']) == (3349,785,661)
    assert (first['actual_successor'],first['virtual_successor']) == (62795,313973)
    assert first['actual_successor_mod64'] == 11
    assert (first['virtual_successor_mod5'],first['odd_run_mod5']) == (3,4)
    assert first['central_boundary_after_initial_defect'][-1] == [313973,1]
    assert [62795,-1] in first['central_boundary_after_initial_defect']

    second = run('lower-composite','class79',0)
    assert (second['h'],second['n'],second['m'],second['c'],second['d']) == (
        1,25543,17960,10217,15025)
    assert (second['x'],second['z'],second['b']) == (3005,5635,2425)
    assert (second['actual_successor'],second['virtual_successor']) == (38315,191573)
    assert second['actual_successor_mod64'] == 43
    assert second['central_boundary_after_initial_defect'][-1] == [191573,1]
    assert [38315,-1] in second['central_boundary_after_initial_defect']


def test_direct_second_frontier_pair_has_no_below_n_base_rule():
    # The exact denominator formula scans all positive odd c<n and d<n.
    for family in ('class95','class79'):
        got = run('second-frontier-pairs',family,0,'--ceiling','n')
        assert got['scope'] == 'positive odd c,d<n'
        assert got['pairs'] == []
        assert got['three_free_pairs'] == []


def test_cubic_second_frontier_crt_family_has_legal_labels():
    # CRT: t=16475 solves 3 mod116, 4 mod7, 14 mod31, with h=3 mod4.
    got = run('second-frontier-cubic',0)
    assert got['variant'] == 'hard64'
    assert (got['t'],got['h'],got['n'],got['m']) == (
        16475,1565127,25542881863,17959838810)
    assert (got['actual_frontier_before'],got['virtual_frontier_before']) == (
        38314322795,191571613973)
    assert got['borrowed_inputs'] == [1795983881,4119819655]
    assert got['output_companions'] == [1981775317,3648983123]
    assert (got['actual_frontier_after'],got['virtual_frontier_after']) == (
        57471484193,287357420960)
    assert got['virtual_frontier_after'] == 16*got['m']
    assert (got['post_six_plus_one'],got['odd_run_length']) == (32327709860,2)
    assert got['old_restricted_palette_rule'] is False
    # q1=1,795,983,881 has T(q1)=2,693,975,822; multiplying by 32 gives
    # 86,207,226,304.  T(57,471,484,193)=86,207,226,290, fourteen less.
    # Three more fixed prefix steps end at 18*q1+1=32,327,709,859.
    assert (got['known_basin_neighbor'],got['actual_third'],
            got['neighbor_gap'],got['actual_sixth']) == (
                86207226304,86207226290,14,32327709859)
    # n rises by 39,026,668,800 per s.  Dividing this slope by each label's
    # affine slope gives these reduced ratios; only 128/9 is 2,3-smooth.
    expected_ratios = {
        'm':[64,45], 'c':[5,2], 'd':[17,10], 'b':[190,3],
        'x':[25,2], 'z':[160,3], 'q1':[128,9], 'q2':[31,5],
        'e1':[116,9], 'e2':[7,1],
    }
    expected_outside = {
        'm':[1,5], 'c':[5,1], 'd':[17,5], 'b':[95,1],
        'x':[25,1], 'z':[5,1], 'q1':[1,1], 'q2':[31,5],
        'e1':[29,1], 'e2':[7,1],
    }
    assert got['coalescence_n_slope'] == 39026668800
    assert {label:row['n_to_label_ratio'] for label,row in
            got['coalescence_slope_audit'].items()} == expected_ratios
    assert {label:row['outside_2_3'] for label,row in
            got['coalescence_slope_audit'].items()} == expected_outside
    assert got['bounded_depth_slope_candidates'] == ['q1']

    # One CRT period raises the odd run to three steps while preserving labels.
    next_row = run('second-frontier-cubic',1)
    assert next_row['t'] == 41647
    assert next_row['borrowed_inputs'] == [4540046531,10414443655]
    assert next_row['output_companions'] == [5009706517,9224221523]
    assert (next_row['m'],next_row['odd_run_length']) == (45400465310,3)
    assert next_row['known_basin_neighbor']-next_row['actual_third'] == 14
    assert next_row['actual_sixth'] == 18*4540046531+1
    assert {label:row['n_to_label_ratio'] for label,row in
            next_row['coalescence_slope_audit'].items()} == expected_ratios

    # The old K32 CRT branch is an easy-prefix control, not the default.
    easy = run('second-frontier-cubic',0,'--variant','easy32')
    assert (easy['t'],easy['h'],easy['odd_run_length']) == (4540,431302,0)
    assert easy['borrowed_inputs'] == [989839387,1135299655]
    assert 'known_basin_neighbor' not in easy
    assert 'coalescence_slope_audit' not in easy


def test_q1_symbolic_pair_has_one_depth_eleven_affine_connection():
    # Initially q(s)=1,795,983,881+2,744,062,650s and v=27q+2.
    # Both are odd.  Their first affine images are T(q) and 27T(q)-10.
    first = run('q1-pair-branch','--max-depth',1,'--max-branches',2)
    assert (first['status'],first['completed_depth'],first['frontier_count']) == (
        'depth_limit',1,1)
    row = first['frontier'][0]
    assert row['q_affine'] == [4116093975,2693975822]
    assert row['v_affine'] == [111134537325,72737347184]
    assert (row['q_parity_word'],row['v_parity_word']) == ('1','1')

    # With q≡105 mod 2048, the independent parity-word calculation gives
    # T^11(q)=T^11(27q+2)=(729q+1279)/2048.  q(s) hits this class exactly
    # when s≡240 mod1024; the endpoint is affine for *every* t in that class.
    got = run('q1-pair-branch')
    assert got['q_family'] == {'slope':2744062650,'constant':1795983881}
    assert got['v_from_q'] == {'multiplier':27,'offset':2}
    assert (got['completed_depth'],got['first_connection_depth'],
            got['connection_count']) == (11,11,1)
    connection = got['connections'][0]
    assert (connection['residue'],connection['exponent'],connection['depth']) == (
        240,10,11)
    assert (connection['q_parity_word'],connection['v_parity_word']) == (
        '10111100100','10000010001')
    q_base = 1795983881+2744062650*240
    assert q_base%2048 == 105
    expected_affine = [729*(2744062650*1024)//2048,
                       (729*q_base+1279)//2048]
    assert connection['q_affine'] == connection['v_affine'] == expected_affine
    # This joined endpoint is below q throughout the progression, so the
    # resulting n-to-q splice is an 18-step descent subclass.
    assert expected_affine[0] < 2744062650*1024
    assert expected_affine[1] < q_base
    assert connection['q_odd_steps']-connection['v_odd_steps'] == 3
    assert got['frontier_count'] == len(got['frontier'])
    assert sum((Fraction(1,2**row['exponent']) for row in
                got['frontier']+got['connections']),Fraction()) == 1

    # Tight branch budgets return the whole current frontier, not a partial
    # subset of the next depth's residue classes.
    capped = run('q1-pair-branch','--max-depth',3,'--max-branches',1)
    assert (capped['status'],capped['completed_depth'],
            capped['frontier_count']) == ('branch_limit',1,1)


def test_q1_hard_2adic_shadow_separates_bounded_prefixes():
    # (9q(s)+1)/2=8,081,927,465+12,348,281,925s.  Modulo 8 its zero
    # class is s=3.  Here T^2(q)=1+4u, while T^6(n)+1=2(9q+1).
    got = run('q1-pair-shadow',2)
    assert (got['variant'],got['s_residue'],got['s_modulus']) == (
        'hard9',3,8)
    assert (got['q'],got['n'],got['n_post_six']) == (
        10028171831,142622888263,180507092959)
    assert (got['q_after_two'],got['q_prefix_upper_bound']) == (
        22563386621,33845079932)
    assert got['nine_q_plus_one']%16 == 0
    assert got['q_after_two'] == 1+4*got['cycle_shadow_u']
    assert got['q_prefix_upper_bound'] < got['n'] < got['n_post_six']
    assert (got['n_above_start_steps_at_least'],got['q_below_n_through'],
            got['no_lagged_meeting_depths_through']) == (11,2,2)
    # Independent first-two-step anchors show the height separation.
    assert [got['n'],(3*got['n']+1)//2,(9*got['n']+5)//4] == [
        142622888263,213934332395,320901498593]
    assert [got['q'],(3*got['q']+1)//2,(9*got['q']+5)//4] == [
        10028171831,15042257747,22563386621]
    farther = run('q1-pair-shadow',16)
    assert farther['variant'] == 'hard9'
    assert farther['nine_q_plus_one']%(2**18) == 0
    assert farther['q_after_two'] == 1+2**16*farther['cycle_shadow_u']
    assert farther['q_prefix_upper_bound'] < farther['n'] < farther['n_post_six']


def test_q1_carry_2adic_shadow_blocks_splices_but_descends():
    # Solving 93s≡25 mod128 gives s=109.  Then q=300,898,812,731≡59
    # mod256, its 27q+2 companion is congruent, and n=(128q-1)/9.
    got = run('q1-pair-shadow',2,'--variant','carry13')
    assert got['variant'] == 'carry13'
    assert (got['shadow_exponent'],got['s_residue'],got['s_modulus'],
            got['s_shift'],got['s_witness']) == (8,109,128,0,109)
    assert (got['n'],got['q'],got['v']) == (
        4279449781063,300898812731,27*300898812731+2)
    assert got['fixed_point_numerator']%256 == 0
    assert got['difference']%512 == 0
    assert (got['same_parity_steps_at_least'],
            got['no_lagged_meeting_depths_through']) == (2,2)
    # Two hand-computed odd steps on each side have no common value.
    n, q = got['n'],got['q']
    assert {n,(3*n+1)//2,(9*n+5)//4}.isdisjoint(
        {q,(3*q+1)//2,(9*q+5)//4})
    assert got['fifteen_step_parity_word'] == '111010111011000'
    assert got['fifteen_step_endpoint'] == 2570569154074 < n

    # At K=16 the least fixed-point residue alone is too small for the
    # nonresonant bound; the constructor shifts along the same progression.
    farther = run('q1-pair-shadow',16,'--variant','carry13')
    assert farther['s_shift'] > 0
    assert farther['s_witness']%farther['s_modulus'] == farther['s_residue']
    assert farther['q'] > 19*6**16
    assert farther['fixed_point_numerator']%(2**16) == 0
    assert farther['fifteen_step_endpoint'] < farther['n']


def test_q1_phase_exit_small_odd_and_even_controls():
    # L=5,u=1: (63,9) -> (143,7) after one regular two-step block,
    # then (323,17).  R=(A+1)(B-1)^3 is 32768,31104,1327104.
    odd = run('q1-phase-exit',5,1)
    assert (odd['regular_two_step_blocks'],odd['M']) == (1,24)
    assert [(odd[stage]['A'],odd[stage]['B'],odd[stage]['R'])
            for stage in ('initial','phase_exit','final')] == [
                (63,9,32768),(143,7,31104),(323,17,1327104)]
    assert odd['rank_ratios'] == {
        'exit_over_initial':[243,256],
        'final_over_exit':[128,3],
        'final_over_initial':[81,2]}
    assert odd['odd_L_affine_identity'] == {'lhs':648,'rhs':648,'holds':True}
    assert odd['initial']['reentry_8_times_power3']['j'] == 0
    assert odd['phase_exit']['reentry_8_times_power3']['j'] == 1
    assert odd['final']['reentry_8_times_power3']['holds'] is False
    assert odd['raw_parity_words'] == {'A':'1111','B':'1011'}
    assert odd['family_membership']['q_integral'] is False

    # L=4,u=1: the even exit carries B=4 -> 2 -> 1.  Rank vanishes even
    # though the A frontier is 161, so zero rank is not a convergence claim.
    even = run('q1-phase-exit',4,1)
    assert [(even[stage]['A'],even[stage]['B'],even[stage]['R'])
            for stage in ('initial','phase_exit','final')] == [
                (31,5,2048),(71,4,1944),(161,1,0)]
    assert even['rank_ratios']['final_over_initial'] == [0,1]
    assert even['odd_L_affine_identity'] is None
    assert even['final']['reentry_8_times_power3']['holds'] is False
    assert even['raw_parity_words'] == {'A':'1111','B':'1000'}
    assert even['family_membership']['in_hard_q1_family'] is False


def test_q1_phase_exit_actual_domain_and_exact_long_threshold():
    # The small controls above are generic.  At s=3, q=10,028,171,831
    # and 9q+1=16*5,640,846,655, so L=4 gives actual hard-q frontiers.
    actual = run('q1-phase-exit',4,5640846655)
    assert actual['family_membership'] == {
        'q_integral':True, 'q':10028171831,
        'in_hard_q1_family':True, 's':3, 'n':142622888263}
    assert (actual['initial']['A'],actual['initial']['B']) == (
        180507092959,22563386621)
    integral_other = run('q1-phase-exit',2,7)
    assert integral_other['family_membership']['q'] == 3
    assert integral_other['family_membership']['in_hard_q1_family'] is False

    # For odd L=2r+3 the total rank ratio is
    # (243/256)^r * (9/256) * (9+5/(3^r*u))^3.
    # Exact lower/upper inequalities prove the sharp universal boundary:
    # every u>=1 grows through r<=62; every u>=1 shrinks through r>=63.
    assert Fraction(243,256)**62 * Fraction(6561,256) > 1
    w63 = 3**63
    assert Fraction(243,256)**63 * Fraction(9,256) * (
        Fraction(9*w63+5,w63)**3) < 1
    before = run('q1-phase-exit',127,1)
    after = run('q1-phase-exit',129,1)
    assert before['regular_two_step_blocks'] == 62
    assert after['regular_two_step_blocks'] == 63
    assert Fraction(*before['rank_ratios']['final_over_initial']) > 1
    assert Fraction(*after['rank_ratios']['final_over_initial']) < 1
    assert after['family_membership']['in_hard_q1_family'] is False
    assert before['final']['reentry_8_times_power3']['holds'] is False
    assert after['final']['reentry_8_times_power3']['holds'] is False


def test_q1_phase_exit_rejects_invalid_parameters():
    for length,u in ((1,1),(1025,1),(4,0),(4,2)):
        bad = subprocess.run([sys.executable,str(CLI),'q1-phase-exit',
                              str(length),str(u)],capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'positive odd u' in bad.stderr


def test_q1_run_exit_exact_forced_steps_and_a_contraction():
    # L=3 gives H=9 and an even post-prefix value 81u-1.
    for u,prefix,k,x in (
        (3,[107,161,242],1,121),
        (1,[35,53,80],4,5),
        (19,[683,1025,1538],1,769),
    ):
        got = run('q1-run-exit',3,u)
        assert got['H'] == 9
        assert got['forced_odd_prefix'] == prefix
        assert (got['k_even_steps'],got['X'],got['X_vs_u']) == (
            k,x,'grow')
        assert got['raw_iteration_checked'] is True
        assert got['family_membership']['in_hard_q1_family'] is False

    # 81*49=3969≡1 mod128, so 81*49-1=3968=128*31.
    shrink = run('q1-run-exit',3,49)
    assert shrink['forced_odd_prefix'] == [1763,2645,3968]
    assert (shrink['k_even_steps'],shrink['X'],shrink['X_vs_u']) == (
        7,31,'shrink')


def test_q1_run_exit_actual_family_expands_and_reset_rank_tracks_q():
    # s=27 gives q=75,885,675,431 and 9q+1=32*21,342,846,215.
    u = 21342846215
    got = run('q1-run-exit',5,u)
    assert got['family_membership'] == {
        'q_integral':True, 'q':75885675431,
        'in_hard_q1_family':True, 's':27, 'n':1079262939463}
    assert got['H'] == 27
    assert got['forced_odd_prefix'] == [
        6915082173659,10372623260489,15558934890734]
    assert 729*u == 15558934890735
    assert (got['k_even_steps'],got['X'],got['X_vs_u'],got['X_vs_n']) == (
        1,7779467445367,'grow','grow')

    # At a normalized phase start R0=(9q+1)^4/32.  Its ordering is
    # exactly q's ordering, so a smaller reset rank requires q_new<q_old.
    earlier = run('q1-phase-exit',4,5640846655)  # s=3
    later = run('q1-phase-exit',5,u)               # s=27
    q_earlier = earlier['family_membership']['q']
    q_later = later['family_membership']['q']
    assert earlier['initial']['R'] == (9*q_earlier+1)**4//32
    assert later['initial']['R'] == (9*q_later+1)**4//32
    assert (earlier['initial']['R'] < later['initial']['R']) == (
        q_earlier < q_later)


def test_q1_run_exit_rejects_invalid_parameters():
    for length,u in ((1,1),(2,1),(4,1),(1025,1),(3,0),(3,2)):
        bad = subprocess.run([sys.executable,str(CLI),'q1-run-exit',
                              str(length),str(u)],capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'odd 3<=L<=1023 and positive odd u' in bad.stderr


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
