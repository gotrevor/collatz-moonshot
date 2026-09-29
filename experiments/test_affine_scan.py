"""External real-CLI controls for the sampled affine quadratic instrument."""

from fractions import Fraction
from math import gcd, lcm
from pathlib import Path
import json
import subprocess
import sys


CLI = Path(__file__).with_name('affine_scan.py')


def run(command):
    return json.loads(subprocess.check_output(
        [sys.executable,str(CLI),command],text=True))


def test_symbolic_five_head_positive_control():
    # The hand-derived family has n=(85s+1)/2 and
    # d(15n+1-12c)=5c(3n+1) for c=17s,d=25s.
    assert run('control')['five_head_symbolic_control'] is True
    for s in (217,601):
        n=(85*s+1)//2
        assert 25*s*(15*n+1-12*17*s) == 5*17*s*(3*n+1)
        r=lambda u:Fraction(2*u,3*u+1)
        assert r(5*n)*r(17*s) == r(n)*r(25*s)


def test_sampled_affine_scan_reports_its_exact_scope():
    got=run('scan')
    assert got['five_head_symbolic_control'] is True
    assert [row['sample_heights'] for row in got['comparisons']] == [
        [0,2],[1,3],[0,3]]
    assert all(row['nonnegative_below_n_affine_candidates'] > 0
               for row in got['comparisons'])
    assert all(row['exact_polynomial_matches'] == []
               for row in got['comparisons'])


def test_all_direct_supply_to_head_matches_fail_exact_congruence():
    got=run('closure')
    assert got['all_eight_impossible'] is True
    assert len(got['comparisons']) == 8
    # An affine equality a+bt=c+ds requires gcd(b,d) | c-a.
    for row in got['comparisons']:
        assert row['base_difference']%row['slope_gcd'] != 0
    anchors={(row['input'],row['head']):row for row in got['comparisons']}
    first=anchors['x64','c64']
    assert first['slope_gcd'] == 124032
    assert first['base_difference'] == 16745-3349 == 13396
    second=anchors['z79','c79']
    assert second['slope_gcd'] == gcd(284400,515712) == 3792
    assert second['base_difference'] == 10217-5635 == 4582


def test_generic_root_dilation_is_exact_but_only_two_levels():
    got=run('dilate')
    expected={
        'x64':([157,3349],[197,629],124032),
        'z64':([209,785],[289,385],29070),
        'x79':([161,3005],[205,601],151680),
        'z79':([107,5635],[175,263],284400),
    }
    r=lambda u:Fraction(2*u,3*u+1)
    periods={}
    for row in got['rules']:
        old,new,target_step=expected[row['input']]
        assert row['base_rule'] == {'before':old,'after':new}
        assert r(old[0])*r(old[1]) == r(new[0])*r(new[1])
        coeff=row['coefficients']
        U,B,X,Z=(coeff[key] for key in ('u','b','x','z'))
        u,b,x,z=U[0],B[0],X[0],Z[0]
        assert U[1] == 3*u*(3*x+1)*(3*u+1)
        assert B[1] == 9*u*b*(3*x+1)
        assert X[1] == 3*x*(3*x+1)*(3*u+1)
        assert Z[1] == 9*x*z*(3*u+1)
        assert all(v[0]%2 and v[0]%3 and v[1]%6==0
                   for v in (U,B,X,Z))
        assert all(v[0]<u and v[1]<U[1] for v in (B,X,Z))
        # The cross-multiplied identity has degree at most four.  These
        # five independent rational evaluations therefore certify it.
        for q in range(5):
            Uq,Bq,Xq,Zq=(v[0]+v[1]*q for v in (U,B,X,Z))
            assert r(Uq)*r(Bq) == r(Xq)*r(Zq)
        divisor=gcd(U[1],target_step)
        period=U[1]//divisor
        assert row['target_parameter_period'] == period
        assert row['deformation_parameter_step'] == target_step//divisor
        assert row['borrowing_prerequisites_constructed'] is False
        periods[row['input']]=period
    assert got['simultaneous_target_parameter_periods'] == {
        '64':lcm(periods['x64'],periods['z64']),
        '79':lcm(periods['x79'],periods['z79'])}
