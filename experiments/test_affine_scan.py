"""External real-CLI controls for the sampled affine quadratic instrument."""

from fractions import Fraction
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
