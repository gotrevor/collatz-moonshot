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
