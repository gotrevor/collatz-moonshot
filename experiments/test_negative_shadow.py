"""Hand-computed anchors through the shipped CLI; structural tests are secondary."""
import json
from pathlib import Path
import subprocess
import sys
import pytest
from negative_shadow import references, score

CLI = Path(__file__).with_name("negative_shadow.py")


@pytest.mark.parametrize("n,a,b,want", [
    (3,1,1,"16"), (5,1,1,"12"),
    (26,1,1,"27"), (13,1,1,"28"),
    (26,2,1,"28"), (9,5,3,"1024/25"), (14,2,1,"64"),
])
def test_cli_anchors(n,a,b,want):
    out=subprocess.check_output([sys.executable,str(CLI),"score",str(n),str(a),str(b)],text=True)
    assert json.loads(out)["score"] == want


def test_small_catalog():
    # Length <= 3: 1 -> -1; 110 -> -5; 101 -> -7; 011 -> -10.
    assert references(3) == [(1,1),(5,1),(7,1),(10,1)]


@pytest.mark.parametrize("n,k,a,b,want", [
    (3,4,7,3,"256/49"), (3,6,19,15,"4096/361"),
    (6,6,10,9,"1024/25"),
])
def test_cli_envelope_witness(n,k,a,b,want):
    out=subprocess.check_output([sys.executable,str(CLI),"envelope",str(n),str(k)],text=True)
    assert json.loads(out) == {"a":a,"b":b,"score":want,"upper":(n+1)**2}


@pytest.mark.parametrize("repeats,a,b,want", [
    (0,1,1,"4"), (1,5,3,"192/25"), (2,23,9,"9216/529"),
])
def test_cli_weighted_cycle_obstruction(repeats,a,b,want):
    out=subprocess.check_output([sys.executable,str(CLI),"cycle-witness",str(repeats)],text=True)
    assert json.loads(out) == {"a":a,"b":b,"weighted_score":want}


def test_height_bound_and_branch_transport():
    # Supplementary exhaustive finite check of the paper inequalities.
    for a,b in references(6):
        for n in range(1,80):
            assert score(n,a,b) <= (n+1)**2
            if n%2 != a%2:
                continue
            if n%2:
                assert score((3*n+1)//2,(3*a-b)//2,b) <= 3*score(n,a,b)/4
            else:
                assert score(n//2,a//2,b) == score(n,a,b)
