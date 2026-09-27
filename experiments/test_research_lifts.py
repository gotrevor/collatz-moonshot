"""Independent hand-computed anchors through the actual research CLI."""
from pathlib import Path
import json
import subprocess
import sys
import pytest

CLI=Path(__file__).with_name('research_lifts.py')


def run(*args):
    return json.loads(subprocess.check_output([sys.executable,str(CLI),*map(str,args)],text=True))


def test_three_path():
    # 2^3*(3/5)*(5/8)=3, realized by reversing 3,5,8,4,2,1.
    got=run('certificate','--twos',3,'--odd-sources',3,5)
    assert got['value']=='3'
    assert got['backward_path']==[1,2,4,8,5,3]


def test_nine_product_is_not_a_path():
    # Squaring that scalar certificate yields 9, but cannot concatenate it.
    got=run('certificate','--twos',6,'--odd-sources',3,3,5,5)
    assert got['value']=='9'
    assert got['realizable'] is False


def test_nine_actual_path():
    got=run('certificate','--twos',7,'--odd-sources',9,7,11,17,13,5)
    assert got['value']=='9'
    assert got['backward_path']==[1,2,4,8,5,10,20,13,26,17,11,7,14,9]


@pytest.mark.parametrize('word,mult,states,ratio,gap',[
    ('10',3,['1','2'],'2','1'),
    ('110',3,['-5','-7','-10'],'8/3','2'),
    ('1100',3,['5/7','11/7','20/7','10/7'],'64/3','1/7'),
    ('1110000',5,['13','33','83','208','104','52','26'],'2097152/125','7'),
])
def test_pair_anchors(word,mult,states,ratio,gap):
    got=run('pair-energy',word,'--multiplier',mult)
    assert got['states']==states
    assert got['mixed_ratio']==ratio
    assert got['minimum_gap']==gap
    assert got['identity_holds'] is True


def test_large_rational_gap_control():
    # Denominator 2^8-3^5=13; sorted closest numerators are 422 and 491.
    got=run('pair-energy','11111000')
    assert got['states']==['211/13','323/13','491/13','743/13','1121/13','1688/13','844/13','422/13']
    assert got['minimum_gap']=='69/13'
    assert got['integral'] is False
    assert got['identity_holds'] is True


def test_signed_fixed_series():
    got=run('signed-fixed','--odd-source',3,'--cutoff',64)
    assert got['positive']==[10,20,40]
    assert got['negative']==[3,6,12,24,48]
    assert got['residuals']==[]


def test_positive_sparse_control_for_a_different_map():
    got=run('multiplicative-fixed','--cutoff',64)
    assert got['support']==[1,2,3,4,8,9,16,27,32,64]
    assert got['residuals']==[]


def test_repeated_cycle_rejected():
    got=subprocess.run([sys.executable,str(CLI),'pair-energy','1010'],capture_output=True,text=True)
    assert got.returncode!=0
    assert 'primitive cycle required' in got.stderr


def test_positive_approximate_fixed_vector_actual_collatz():
    # D_3+z^5: P F-F=z^8, ||F||_(1/n)=2/3+1/5=13/15.
    got=run('approx-fixed','--depth',2,'--cutoff',64)
    assert got['orbit']==[3,5,8]
    assert got['weighted_mass']=='13/15'
    assert got['error_mass']=='1/8'
    assert got['relative_error']=='15/104'
    assert got['residuals']==[[8,1]]


def test_approximate_fixed_second_anchor_and_boundary():
    # D_7+z^11+z^17: 2/7+1/11+1/17=570/1309.
    got=run('approx-fixed','--depth',3,'--cutoff',26)
    assert got['orbit']==[7,11,17,26]
    assert got['weighted_mass']=='570/1309'
    assert got['relative_error']=='1309/14820'
    assert got['residuals']==[[26,1]]
    assert run('approx-fixed','--depth',3,'--cutoff',25)['residuals']==[]


def test_pair_discriminant_anchors():
    # For 5/7,11/7,20/7,10/7, the six numerator gaps are 6,15,5,9,1,10.
    got=run('pair-discriminant','1100')
    assert got['vandermonde']=='40500/117649'
    assert got['all_differences_integral'] is False
    assert got['discriminant_integral'] is False
    got=run('pair-discriminant','110')
    assert got['vandermonde']=='30'
    assert got['all_differences_integral'] is True


def test_discriminant_scan_small_anchor():
    # Positive primitive necklaces through length 3: 01 (1,2), 001 (1/5,2/5,4/5).
    got=run('discriminant-scan','--depth',3)
    assert got['positive_primitive_cycles_examined']==2
    assert got['nonintegral_cycles_with_integral_discriminant']==[]


def test_wild_five_repair_hand_computed_anchor():
    got=run('wild-five-repair',7)
    assert got['virtual_prefix']==[35,53,80,40,20,10,5]
    assert got['actual_path']==[7,11,17,26,13,20,10,5,8,4,2,1]
    assert got['smaller_path']==[5,8,4,2,1]
    assert got['certificate_value']=='7'
    assert got['actual_factors']==11
    assert got['virtual_factors']==19
    assert got['meeting_steps']==[7,0]
    assert got['exchange']=={'remove_twos':3,'add_twos':0,
                            'remove_odds':[7,35,53,55,65,83],'add_odds':[13]}


def test_wild_five_length_decrease_is_impossible_at_71():
    # 50 has the displayed 17-step path, plus 6 virtual steps and 9 inverse-5
    # factors: 32.  Direct arithmetic in blocks from 71 gives
    # 71 -(2)->161 -(2)->121 -(2)->91 -(3)->103 -(4)->175 -(5)->445
    # -(3)->167 -(4)->283 -(3)->319 -(4)->1619, totaling 32 steps.
    # Since {1,2} is invariant, that endpoint excludes reaching 1 by step 32.
    got=run('wild-five-repair',71)
    assert got['virtual_prefix']==[355,533,800,400,200,100,50]
    assert got['smaller_path']==[50,25,38,19,29,44,22,11,17,26,13,20,10,5,8,4,2,1]
    assert got['virtual_factors']==32
    assert got['actual_path'][32]==1619
    assert got['actual_factors']>32
    assert got['certificate_value']=='71'


def test_exact_fixed_series_can_be_nearly_positive():
    # H_2 = D_3 + z^5 - D_16.  Positive mass 13/15; negative mass 1/8.
    got=run('nearly-positive-fixed','--depth',2,'--cutoff',64)
    assert got['positive']==[3,5,6,12,24,48]
    assert got['negative']==[16,32,64]
    assert got['positive_mass']=='13/15'
    assert got['negative_mass']=='1/8'
    assert got['negative_to_positive']=='15/104'
    assert got['residuals']==[]


def test_integral_vandermonde_with_halving_edge_is_insufficient():
    # Differences 63/5,188/5,25 multiply to 63*188=11844.
    got=run('gap-control','--parameter',1)
    assert got['states']==['63/5','126/5','251/5']
    assert got['minimum_gap']=='63/5'
    assert got['vandermonde']=='11844'
    assert got['has_halving_edge'] is True
    assert got['integral_states'] is False
    assert got['closed_under_collatz'] is False


@pytest.mark.parametrize('t,old,new,value',[
    (1,[23,245],[35,53,80],'7/16'),
    (5,[115,1211],[175,263,395],'35/79'),
])
def test_parametric_two_edge_repair(t,old,new,value):
    got=run('two-edge-repair','--parameter',t)
    assert got['disconnected_sources']==old
    assert got['connected_path']==new
    assert got['value']==value
    assert got['before_boundary_l1']==4
    assert got['after_boundary_l1']==2


def test_local_connectivity_gain_can_stall_before_a_path():
    got=run('two-edge-repair','--parameter',1)['certificate_seven']
    assert got['before']['value']==got['after']['value']=='7'
    assert got['before']['realizable'] is False
    assert got['after']['realizable'] is False
    assert got['before_defect_l1']==6
    assert got['after_defect_l1']==4
    assert got['after_defect']=={'7':-1,'16':1,'35':1,'80':-1}


def test_entire_two_factor_fiber_has_a_nonzero_local_minimum():
    # (c-21)(d-21)=448.  The even divisor pairs are
    # (2,224),(4,112),(8,56),(14,32),(16,28); add 21 to each entry.
    got=run('two-odd-fiber','--ratio','7/16')
    assert got['D']==1
    assert got['factor_product']==448
    assert got['unordered_odd_pairs']==[[23,245],[25,133],[29,77],[35,53],[37,49]]
    assert [row['defect_l1'] for row in got['certificate_seven_fiber']]==[6,6,6,4,6]
    assert all(not row['realizable'] for row in got['certificate_seven_fiber'])


def test_followup_snapshot_checks_the_nonzero_boundary():
    got=run('controls','--followup','--scan-depth',3)
    assert got['discriminant_scan']['positive_primitive_cycles_examined']==2
    # 3^8-1=6560.  The cutoff includes the defect and the first negative point.
    assert got['positive_approximation']['residuals']==[[6560,1]]
    assert got['exact_nearly_positive_fixed']['negative']==[13120]
    assert got['exact_nearly_positive_fixed']['residuals']==[]


def test_short_units_and_parity_obstruction():
    # For k>=1, 2^t(5/8)^k <= 1 < 2^t(2/3)^k.  Below odd
    # length 13, only t=2,k=3 survives; its least label is 5, leaving
    # (c-3)(d-3)=10 with c,d odd, impossible modulo 4.
    got=run('unit-parity')
    assert got['odd_length_candidates_below_thirteen']==[[2,3]]
    assert got['reduced_unit_candidates_below_eight']==[[2,3]]
    assert got['candidate_triple_fiber']['unordered_odd_tuples']==[]
    assert got['unit_value']=='1'
    assert got['unit_length']==13


def test_exact_factor_fibers_small_anchors():
    assert run('odd-factor-fiber','--ratio','3/5','--count',1)['unordered_odd_tuples']==[[3]]
    assert run('odd-factor-fiber','--ratio','1/4','--count',2)['unordered_odd_tuples']==[[1,1]]
    assert run('odd-factor-fiber','--ratio','1/8','--count',3)['unordered_odd_tuples']==[[1,1,1]]
    assert run('odd-factor-fiber','--ratio','2/3','--count',1)['unordered_odd_tuples']==[]


def test_catalytic_repair_of_seven():
    # U8 telescopes multiplicatively to
    # (19/38)*(25/125)*(55/44)=1/8.  U13 is the published inverse-5
    # certificate times 5 -> 8 -> 4 -> 2 -> 1.
    got=run('catalytic-seven')
    assert got['unit8']['value']==got['unit13']['value']=='1'
    assert got['count_lattice_determinant']==-1
    assert got['exchange']['before_value']==got['exchange']['after_value']=='65/352'
    assert [row['twos'] for row in got['stages']]==[4,9,9,9,6]
    assert all(row['value']=='7' for row in got['stages'])
    assert got['stages'][-1]['sources']==[5,7,11,13,17]
    assert got['original']['realizable'] is False
    assert got['repaired']['backward_path']==[1,2,4,8,5,10,20,13,26,17,11,7]


def test_quadratic_moves_cannot_replace_the_cubic_exchange():
    # High pair equation: (17c-741)(17d-741)=553280, c<=d.
    # The valid pairs are (53,247) and (65,133).  Pairs involving 7
    # in either triple have no alternative (the smaller label is <15).
    got=run('quadratic-path','--sources',7,65,133,'--target',13,19,29,
            '--max-label',1000,'--max-states',20)
    assert got['path'] is None
    assert got['bounded_graph_exhausted'] is True
    assert got['height_pruned']==0
    assert got['visited_states']==[[7,53,247],[7,65,133]]


def test_quadratic_path_and_incomplete_search_are_distinguished():
    got=run('quadratic-path','--sources',35,53,'--target',23,245)
    assert got['path']==[[35,53],[23,245]]
    got=run('quadratic-path','--sources',7,65,133,'--target',13,19,29,
            '--max-states',1)
    assert got['path'] is None
    assert got['bounded_graph_exhausted'] is False


@pytest.mark.parametrize('n,peak,prefix',[(3,8,[3,5,8]),(7,26,[7,11,17,26]),(8,4,[8,4])])
def test_sharp_anchored_cut(n,peak,prefix):
    got=run('anchored-cut',n,'--cutoff',64)
    assert got['peak_future']==peak
    assert got['prefix_to_peak']==prefix
    assert got['anchor_coefficient']==1
    assert got['cycle_coefficients']==[0,0]
    assert got['sharp_defect_norm']==f'1/{peak}'
    assert got['forward_cut_residual_sum']==1
    assert got['residuals']==[[peak,1]]


def test_dyadic_cycle_ledger_is_prefix_bookkeeping():
    # For 1100 only the pairs of 1-starts and 0-starts agree for one bit.
    got=run('dyadic-pair-ledger','1100')
    assert got['vandermonde_v2']==got['prefix_collision_sum']==2
    assert got['prefix_collision_counts']==[[1,2]]
    assert all(row['gap_v2']==row['common_prefix'] for row in got['pairs'])
    # For 11111000: length-one groups 5,3 give 13 pairs; length-two
    # groups 4,2,1,1 give 7; then 3 and 1, totaling 24.
    got=run('dyadic-pair-ledger','11111000')
    assert got['prefix_collision_counts']==[[1,13],[2,7],[3,3],[4,1]]
    assert got['vandermonde_v2']==got['prefix_collision_sum']==24
    assert got['integral'] is False


def test_catalyst_makes_the_first_cubic_quadratically_reachable():
    # r7*r121=r11*r17 supplies the first move; the explicit seven-step
    # chain is checked edge-by-edge in Lean's CatalyticRepair module.
    got=run('quadratic-path','--sources',7,65,133,121,'--target',13,19,29,121,
            '--max-label',2000,'--max-states',500)
    assert got['path'][0]==[7,65,121,133]
    assert got['path'][-1]==[13,19,29,121]
    assert got['value']=='209/1120'


def test_quadratic_unit_assisted_seven_repair():
    got=run('unit-assisted-seven')
    assert all(v=='7' for v in got['stage_values'])
    assert got['final_twos']==6
    assert got['final_sources']==[5,7,11,13,17]
    assert got['final_certificate']['realizable'] is True
    assert got['moves'][0]=={'remove':[35,53],'add':[25,133],'value':'7/16'}
    assert got['moves'][-1]=={'remove':[7,121],'add':[11,17],'value':'11/26'}


def test_small_generators_are_frozen_without_a_height_bound():
    for n in [1,3,5]:
        got=run('quadratic-neighbors',n)
        assert got['frozen'] is True
        assert got['height_cutoff'] is None
    got=run('quadratic-neighbors',7)
    # Directly solving the small-variable equations gives exactly these
    # three partners.  Only 121 is 3-free.
    assert got['nontrivial_exchanges']==[
        {'before':[7,121],'after':[11,17]},
        {'before':[7,261],'after':[9,29]},
        {'before':[7,429],'after':[13,15]}]


def test_unit_palette_obstruction_and_essential_cubic():
    got=run('palette-obstruction')
    assert got['unit_indices']=={'trivial':0,'eight':0,'thirteen':0}
    # Virtual: 5*16-3*16-1=31.  Actual: 5*28-3*37-1=28.
    assert got['seventy_one']['virtual_index']==31
    assert got['seventy_one']['actual_index']==28
    # (11/17)*(13/20)*(17/26)=11/40
    # (5/8)*(55/83)*(83/125)=11/40.
    assert got['essential_cubic']['left_value']==got['essential_cubic']['right_value']=='11/40'
    assert got['essential_cubic']['index_change']==1
    assert got['new_unit']['value']=='1'
    assert got['new_unit']['index']==1


def test_structural_snapshot_contains_both_kinds_of_cubic_obstruction():
    got=run('controls','--structural')
    assert got['cubic_component']['path'] is None
    assert got['cubic_component']['height_pruned']==0
    assert got['catalyst_121']['path'] is not None
    assert got['small_neighbors'][2]['frozen'] is True
    assert got['sharp_anchors'][1]['sharp_defect_norm']=='1/26'
