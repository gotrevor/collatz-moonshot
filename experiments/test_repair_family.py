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


def test_q1_offset_trace_primitive_update_and_three_step_table():
    got = run('q1-offset-trace',0,1,'--steps',3)
    assert [(row['A'],row['B'],row['b'],row['h'],row['k'],row['c'])
            for row in got['history']] == [
                (35,8,0,1,8,-29),
                (53,4,1,1,24,-43),
                (80,2,2,1,72,-64),
                (40,1,2,1,72,-32)]
    assert [(row['word'],row['h'],row['k'],row['c'])
            for row in got['terminal_three_step_table']] == [
                ('000',1,8,0),('001',3,8,-4),('010',3,8,-2),
                ('011',9,8,-10),('100',3,8,-1),('101',9,8,-7),
                ('110',9,8,-5),('111',27,8,-19)]
    assert all(row['h']*row['A']-row['k']*row['B'] == row['c']
               and row['c']%2 == row['A_parity'] for row in got['history'])
    assert got['positive_A_equals_B_steps'] == []
    assert got['positive_T3A_equals_B_steps'] == []


def test_q1_offset_trace_actual_sign_cross_and_positive_macro():
    # This is the actual hard-family s=7 instance, not an arbitrary pair.
    got = run('q1-offset-trace',0,23629975235,'--steps',40)
    assert got['family_membership']['in_hard_q1_family'] is True
    assert got['family_membership']['s'] == 7
    at28,at29 = got['history'][28:30]
    assert (at28['b'],at28['c']) == (-4,-23)
    assert (at29['A'],at29['B'],at29['b'],at29['h'],at29['k'],at29['c']) == (
        842075342,2842004279,-3,27,8,2)
    assert 29 in got['c_crossings_nonpositive_to_positive']

    # Five admitted steps later the inherited relation returns unchanged:
    # A-word 11100 has (27A+19)/32; B-word 11001 has (27B+31)/32.
    start,end = got['history'][35],got['history'][40]
    assert (start['A'],start['B'],start['b'],start['c']) == (
        1065751607,3596911667,-3,53)
    assert (end['A'],end['B'],end['b'],end['c']) == (
        899227919,3034894220,-3,53)
    assert ''.join(str(row['A_parity']) for row in got['history'][35:40]) == '11100'
    assert ''.join(str(row['B_parity']) for row in got['history'][35:40]) == '11001'
    assert end['A'] == (27*start['A']+19)//32
    assert end['B'] == (27*start['B']+31)//32


def test_q1_offset_negative_cycle_is_only_an_algebraic_control():
    got = run('q1-offset-trace',0,-5,'--steps',16)
    assert got['positive_start'] is False
    assert got['family_membership']['in_hard_q1_family'] is False
    assert [(row['A'],row['B'],row['b'],row['c'])
            for row in got['history'][13:17]] == [
                (-5,-10,-3,-55),(-7,-5,-2,-23),
                (-10,-7,-2,-34),(-5,-10,-3,-55)]
    assert got['positive_A_equals_B_steps'] == []
    assert got['positive_T3A_equals_B_steps'] == []

    # The same three-word pattern has positive affine solutions, but it
    # preserves 27A-8B=-55 without yielding either endpoint connection.
    z = 1
    a,b = 64*z-5,216*z-10
    a_next,b_next = 72*z-5,243*z-10
    assert (a,b,a_next,b_next) == (59,206,67,233)
    assert [a,(3*a+1)//2,(9*a+5)//4,a_next] == [59,89,134,67]
    assert [b,b//2,(3*(b//2)+1)//2,b_next] == [206,103,155,233]
    assert (27*64-8*216,27*(-5)-8*(-10)) == (0,-55)
    assert (27*72-8*243,27*(-5)-8*(-10)) == (0,-55)
    assert 27*a-8*b == 27*a_next-8*b_next == -55
    assert a != b and a_next != b
    assert '111' not in [row['word'] for row in got['terminal_three_step_table']
                         if (row['h'],row['k'],row['c']) == (27,8,-55)]


def test_q1_offset_trace_rejects_invalid_parameters():
    for r,u,steps in ((-1,1,0),(129,1,0),(0,0,0),(0,2,0),
                      (0,1,-1),(0,1,1025)):
        bad = subprocess.run([sys.executable,str(CLI),'q1-offset-trace',
                              str(r),str(u),'--steps',str(steps)],
                             capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'offset-trace needs' in bad.stderr


def test_q1_offset_ray_exact_modulus_and_checkpoints():
    u0,e = 23629975235,12348281925
    for depth in (0,2):
        got = run('q1-offset-ray',depth)
        p = 12+6*depth
        modulus = 2**(p-1)
        t,u = got['t_residue'],got['u']
        assert (got['K'],got['P'],got['t_modulus']) == (
            depth,p,modulus)
        # This congruence and 0<=t<modulus uniquely specify the inverse.
        assert 0 <= t < modulus
        assert ((9*u0+1)//2+9*e*t)%modulus == 0
        assert u == u0+2*e*t and (9*u+1)%2**p == 0
        assert got['s'] == 7+8*t
        assert got['trace_horizon'] == 9+6*depth
        assert got['six_step_words'] == {'A':'110110','B':'101010'}
        assert got['verified_six_step_blocks'] == depth
        assert got['postexit_bounds']['A_min'] >= 36*u-1 > got['n']
        assert got['postexit_bounds']['B_max'] < got['n']
        assert got['original_prefix_bounds']['n_min'] == got['n']
        assert got['original_prefix_bounds']['q_max'] < got['n']
        assert len(got['checkpoints']) == depth+1
        for index,row in enumerate(got['checkpoints']):
            multiplier = 72*3**index
            assert (row['block'],row['step'],row['b'],row['h'],row['k'],
                    row['c'],row['m'],row['d']) == (
                index,9+6*index,2+index,1,multiplier,-multiplier-5,
                multiplier,-4)
            assert row['A']+1 == multiplier*(row['B']-1)-4


def test_q1_offset_ray_six_step_macro_hand_anchor():
    # Admitted A-word 110110 and B-word 101010 carry the primitive form
    # A+5=72(B-1) to A'+5=216(B'-1) on a positive local pair.
    a_path = [4603,6905,10358,5179,7769,11654,5827]
    b_path = [65,98,49,74,37,56,28]
    def shortcut(value):
        return (3*value+1)//2 if value%2 else value//2
    assert all(shortcut(a_path[i]) == a_path[i+1] for i in range(6))
    assert all(shortcut(b_path[i]) == b_path[i+1] for i in range(6))
    assert ''.join(str(value%2) for value in a_path[:-1]) == '110110'
    assert ''.join(str(value%2) for value in b_path[:-1]) == '101010'
    assert a_path[0]+5 == 72*(b_path[0]-1)
    assert a_path[-1]+5 == 216*(b_path[-1]-1)


def test_q1_offset_ray_rejects_invalid_depths():
    for depth in (-1,129):
        bad = subprocess.run([sys.executable,str(CLI),'q1-offset-ray',
                              str(depth)],capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'offset-ray requires' in bad.stderr


def test_q1_ray_exit_two_hand_stepped_anchors():
    # A: 67 -> 101 -> 152 -> 76 -> 38.  B: 2 -> 1 -> 2 -> 1 -> 2.
    zero = run('q1-ray-exit',0,0,1)
    assert zero['initial'] == {'A':67,'B':2,'m':72,'d':-4}
    assert zero['first_parity_mismatch'] == {'A':3,'B':0}
    assert [(zero['checkpoints'][name]['A'],zero['checkpoints'][name]['B'])
            for name in ('initial','B_after_mismatch','A_first_mismatch','final')] == [
                (67,2),(101,1),(76,1),(38,2)]
    assert zero['A_parity_word'] == '1100'
    assert zero['B_parity_word'] == '0101'
    assert zero['checkpoints']['initial']['A_offset']['v2'] == 3
    assert zero['checkpoints']['final']['A_offset']['v2'] == 0
    assert zero['final_vs_initial'] == {'A':'shrink','B':'equal'}

    # With j=1,e=1,v=3, the two paths are obtained by ordinary T steps:
    # A: 1291,1937,2906,1453,2180,1090; B: 7,11,17,26,13,20.
    one = run('q1-ray-exit',1,1,3)
    assert one['initial'] == {'A':1291,'B':7,'m':216,'d':-4}
    assert one['first_parity_mismatch'] == {'A':4,'B':1}
    assert [(one['checkpoints'][name]['A'],one['checkpoints'][name]['B'])
            for name in ('B_first_mismatch','B_after_mismatch',
                         'A_first_mismatch','final')] == [
                (1937,11),(2906,17),(2180,13),(1090,20)]
    assert one['A_parity_word'] == '11010'
    assert one['B_parity_word'] == '11101'
    assert one['final_vs_initial'] == {'A':'shrink','B':'grow'}


def test_q1_ray_exit_six_remainder_classes_and_exact_ledger():
    # Check the formulas at the first parity disagreements, using the
    # independently specified reference cycles.  This covers e mod 6.
    a_ref, b_ref = (-5,-7,-10), (1,2)
    for e in range(6):
        got = run('q1-ray-exit',0,e,1)
        assert got['steps'] == e+4
        assert got['shared_phase_steps'] == e
        assert got['complete_six_blocks'] == e//6
        assert got['first_parity_mismatch'] == {'A':e+3,'B':e}
        assert got['shadow_formulas_checked'] is True
        assert got['inherited_relation_checked'] is True
        for name,index in (('initial',0),('B_first_mismatch',e),
                           ('B_after_mismatch',e+1),
                           ('A_first_mismatch',e+3),('final',e+4)):
            row = got['checkpoints'][name]
            assert row['index'] == index
            assert row['A_reference'] == a_ref[index%3]
            assert row['B_reference'] == b_ref[index%2]
            m = Fraction(*row['m'])
            d = Fraction(*row['d'])
            assert row['A']+1 == m*(row['B']-1)+d
            for label,reference in (('A',a_ref[index%3]),
                                    ('B',b_ref[index%2])):
                offset = row[label+'_offset']
                assert offset['difference'] == row[label]-reference
                assert offset['reference_hit'] == (row[label] == reference)
                if offset['reference_hit']:
                    assert offset['v2'] is None
                else:
                    power = 2**offset['v2']
                    assert abs(offset['difference'])%power == 0
                    assert (abs(offset['difference'])//power)%2 == 1
            if index <= e:
                assert row['B'] == b_ref[index%2] + (
                    3**((index+1)//2)*2**(e-index))
            if index <= e+3:
                assert row['A'] == a_ref[index%3] + (
                    9*3**(index-index//3)*2**(e+3-index))
        if e == 2:
            assert got['checkpoints']['B_after_mismatch']['B_offset'] == {
                'difference':0,'reference_hit':True,'v2':None}


def test_q1_ray_exit_rejects_invalid_parameters():
    for j,e,v in ((-1,0,1),(129,0,1),(0,-1,1),(0,513,1),
                  (0,0,0),(0,0,2),(0,0,-1)):
        bad = subprocess.run([sys.executable,str(CLI),'q1-ray-exit',
                              str(j),str(e),str(v)],capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'ray-exit needs' in bad.stderr


def test_q1_ray_refill_hand_six_step_controls():
    def shortcut(value):
        return (3*value+1)//2 if value%2 else value//2
    # v=7 and v=71 have 9v+1=64 and 640, respectively.  The latter
    # supplies one new factor of two after division by 64.
    for v,a_path,b_path,fuel in (
        (7,[499,749,1124,562,281,422,211],
         [8,4,2,1,2,1,2],0),
        (71,[5107,7661,11492,5746,2873,4310,2155],
         [72,36,18,9,14,7,11],1),
    ):
        assert all(shortcut(a_path[i]) == a_path[i+1] for i in range(6))
        assert all(shortcut(b_path[i]) == b_path[i+1] for i in range(6))
        assert ''.join(str(x%2) for x in a_path[:-1]) == '110010'
        assert ''.join(str(x%2) for x in b_path[:-1]) == '000101'
        assert a_path[0]+1 == 72*(b_path[0]-1)-4
        assert a_path[-1] == (243*v-13)//8
        assert b_path[-1] == (9*v+65)//64
        assert a_path[-1]+1 == 216*(b_path[-1]-1)-4
        assert (b_path[-1]-1)%(2**fuel) == 0
        assert (b_path[-1]-1)%(2**(fuel+1)) != 0


def test_q1_ray_refill_actual_hard_family_crt_and_prefix():
    def shortcut(value):
        return (3*value+1)//2 if value%2 else value//2
    for depth in (0,2,24,128):
        got = run('q1-ray-refill',depth)
        v = got['v']
        assert got['K'] == depth
        assert got['t'] == 1690+2048*got['z_residue']
        assert 0 <= got['z_residue'] < 2**(depth+5)
        assert got['z_modulus'] == 2**(depth+5)
        assert got['u'] == 23629975235+2*12348281925*got['t']
        assert got['s'] == 7+8*got['t']
        assert got['v_slope'] == 4*3**6*12348281925
        assert v == got['v_base']+got['v_slope']*got['z_residue']
        assert (9*v+1)%(2**(depth+6)) == 0
        assert (9*v+1)%(2**(depth+7)) != 0
        assert got['nine_v_plus_one_v2'] == depth+6
        assert got['entry']['A'] == 72*v-5
        assert got['entry']['B'] == v+1
        assert got['exit']['A'] == (243*v-13)//8
        assert got['exit']['B'] == (9*v+65)//64
        assert got['exit']['new_fuel_v2'] == depth
        assert got['six_step_words'] == {'A':'110010','B':'000101'}
        a,b = got['entry']['A'],got['entry']['B']
        for _ in range(6):
            a,b = shortcut(a),shortcut(b)
        assert (a,b) == (got['exit']['A'],got['exit']['B'])
        assert got['entry']['A']+1 == 72*(got['entry']['B']-1)-4
        assert got['exit']['A']+1 == 216*(got['exit']['B']-1)-4
        assert got['growth'] == {'A':'shrink','B':'shrink'}
        n_path,q_path = [got['n']],[got['q']]
        for _ in range(23):
            n_path.append(shortcut(n_path[-1]))
        for _ in range(19):
            q_path.append(shortcut(q_path[-1]))
        assert (n_path[17],q_path[13]) == (got['entry']['A'],got['entry']['B'])
        assert (n_path[23],q_path[19]) == (got['exit']['A'],got['exit']['B'])
        assert min(n_path) == got['n']
        assert max(q_path) < got['n']
        assert got['original_prefix_bounds']['n_ge_start_through_23'] is True
        assert got['original_prefix_bounds']['q_lt_n_through_19'] is True
        phase = got['following_phase']
        assert phase['odd_V']%2 == 1
        assert got['exit']['B']-1 == 2**depth*phase['odd_V']
        assert phase['complete_six_blocks'] == depth//6
        assert phase['first_parity_mismatch'] == {'A':depth+3,'B':depth}
        assert phase['at_B_first_mismatch']['index'] == depth
        assert phase['at_A_first_mismatch']['index'] == depth+3
        assert phase['at_end']['index'] == depth+4
        last = phase['last_six_block_endpoint']
        blocks = depth//6
        assert (last['index'],last['j'],last['m'],last['d'],
                last['remaining_fuel']) == (
            6*blocks,1+blocks,216*3**blocks,-4,depth%6)
        assert (last['A']+5)*64**blocks == (got['exit']['A']+5)*81**blocks
        assert (last['B']-1)*64**blocks == (got['exit']['B']-1)*27**blocks
        assert last['A']+1 == last['m']*(last['B']-1)-4
        a,b = got['exit']['A'],got['exit']['B']
        for index in range(depth+5):
            if index == 6*blocks:
                assert (a,b) == (last['A'],last['B'])
            if index == depth:
                row = phase['at_B_first_mismatch']
                assert (a,b) == (row['A'],row['B'])
            if index == depth+3:
                row = phase['at_A_first_mismatch']
                assert (a,b) == (row['A'],row['B'])
            if index == depth+4:
                row = phase['at_end']
                assert (a,b) == (row['A'],row['B'])
                break
            a,b = shortcut(a),shortcut(b)
    # Modulo 64 and 128, direct substitution yields the first two CRT
    # residues z=8 and z=56 for exact valuations 6 and 7.
    assert run('q1-ray-refill',0)['z_residue'] == 8
    assert run('q1-ray-refill',1)['z_residue'] == 56

    # Four six-block multipliers overcome the initial refill contraction:
    # (27/64)*(81/64)^4 > 1.  This is a finite regrowth statement, with
    # the auxiliary still below its pre-refill entry, not convergence.
    assert 27*81**4 > 64**5
    regrown = run('q1-ray-refill',24)['following_phase']['last_six_block_endpoint']
    assert (regrown['j'],regrown['remaining_fuel'],
            regrown['A_vs_pre_refill_entry'],
            regrown['B_vs_pre_refill_entry']) == (5,0,'grow','shrink')
    zero = run('q1-ray-refill',0)
    initial_block = zero['following_phase']['last_six_block_endpoint']
    assert initial_block['index'] == 0
    assert (initial_block['A'],initial_block['B']) == (
        zero['exit']['A'],zero['exit']['B'])


def test_q1_ray_refill_rejects_invalid_depths():
    for depth in (-1,129):
        bad = subprocess.run([sys.executable,str(CLI),'q1-ray-refill',
                              str(depth)],capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'ray-refill needs' in bad.stderr


def test_q1_ray_refill_odd_part_residue_controls():
    def shortcut(value):
        return (3*value+1)//2 if value%2 else value//2
    # On the j=1 start A=216V-5, B=V+1, V=1 misses the six-step
    # return; V=45 has A-word 110010 and B-word 011100 and returns.
    one_a = [211,317,476,238,119,179,269]
    one_b = [2,1,2,1,2,1,2]
    forty_five_a = [9715,14573,21860,10930,5465,8198,4099]
    forty_five_b = [46,23,35,53,80,40,20]
    for a_path,b_path in ((one_a,one_b),(forty_five_a,forty_five_b)):
        assert all(shortcut(a_path[i]) == a_path[i+1] for i in range(6))
        assert all(shortcut(b_path[i]) == b_path[i+1] for i in range(6))
    assert one_a[-1]+1 != 216*(one_b[-1]-1)-4
    assert forty_five_a[-1]+1 == 216*(forty_five_b[-1]-1)-4

    for residue,returns in ((1,False),(45,True)):
        got = run('q1-ray-refill',0,'--odd-part-mod64',residue)
        phase = got['following_phase']
        assert got['requested_odd_part_mod64'] == residue
        assert got['z_modulus'] == 2**10
        assert phase['odd_V_mod64'] == residue
        assert phase['odd_V']%64 == residue
        assert got['exit']['new_fuel_v2'] == 0
        assert phase['complete_six_blocks'] == 0
        assert phase['ordinary_six_block_available'] is False
        assert phase['last_six_block_endpoint']['j'] == 1
        assert phase['last_six_block_endpoint']['m'] == 216
        assert phase['j1_six_return_residue45'] is returns
        row = phase['post_zero_fuel_six']
        assert row['same_j1_relation'] is returns
        a,b = got['exit']['A'],got['exit']['B']
        word_a,word_b = '', ''
        for _ in range(6):
            word_a += str(a%2)
            word_b += str(b%2)
            a,b = shortcut(a),shortcut(b)
        assert (a,b,word_a,word_b) == (
            row['A'],row['B'],row['A_word'],row['B_word'])
        assert row['original_n_step'] == 29
        assert row['original_q_step'] == 25
        n_at_29 = got['n']
        for _ in range(29):
            n_at_29 = shortcut(n_at_29)
        assert n_at_29 == row['A']
        if returns:
            assert (word_a,word_b) == ('110010','011100')
            assert row['A']+1 == 216*(row['B']-1)-4
            assert row['A'] < got['n']
            assert row['A_below_original_n'] is True
        else:
            assert (word_a,word_b) == ('110011','010101')
            assert row['A']+1 != 216*(row['B']-1)-4
            assert row['A_below_original_n'] is False


def test_q1_ray_refill_rejects_invalid_odd_part_residues():
    for residue in (0,2,65):
        bad = subprocess.run([sys.executable,str(CLI),'q1-ray-refill','0',
                              '--odd-part-mod64',str(residue)],
                             capture_output=True,text=True)
        assert bad.returncode != 0
        assert 'odd-part-mod64 needs odd R in 1..63' in bad.stderr


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
