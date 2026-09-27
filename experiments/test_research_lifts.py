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
