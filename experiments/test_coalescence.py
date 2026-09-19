"""Hand-checked anchors for `parity_reconstruction.py coalescence`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_coalescence.py -q

Every expected number below was worked out by hand on the shortcut map, not read off the
tool's output:
  3  -> 5 -> 8 -> 4 -> 2 -> 1                    L=5, A=2, S=1;  smaller orbits {1,2}: c=4, sigma=4
  7  -> 11 -> 17 -> 26 -> 13 -> 20 -> 10 -> 5     first value <7 is 5 at step 7; nothing earlier lies in
                                                 the orbits of 1..6 = {1,2,3,4,5,6,8}; L=11, A=5, S=1
  15 -> 23 -> 35 -> 53 -> 80 -> 40 -> 20 -> 10    20 is on the orbit of 13 (13 -> 20): c=6; 10 < 15: sigma=7
  27: the handoff leaf's all-time proofs give sigma=59, S=-12, and no coalescence before step 59.
"""
import re
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def run(limit):
    return subprocess.run([sys.executable, str(SCRIPT), "coalescence", str(limit)],
                          capture_output=True, text=True, check=True).stdout


def row(out, n):
    m = re.search(rf"n={n}: c=(\d+) sigma=(\d+) S=(-?\d+)", out)
    assert m, f"no row for n={n} in output"
    return tuple(int(g) for g in m.groups())


def test_hand_anchors():
    out = run(100)
    assert row(out, 3) == (4, 4, 1)
    assert row(out, 7) == (7, 7, 1)
    assert row(out, 15) == (6, 7, 2)
    assert row(out, 27) == (59, 59, -12)


def test_27_is_first_odd_without_balanced_partner():
    out = run(100)
    m = re.search(r"NO balanced partner below them: (\d+) of 50\n  first few: \[(\d+)", out)
    assert m and m.group(2) == "27"
