"""Hand-checked anchors for `parity_reconstruction.py cst-check`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_cst_small.py -q

By hand (shortcut map, a = odd steps so far, crossing at the first m with 3^a < 2^m):
  n=3: 3 →5 →8 →4 →2.  Parities 1,1,0,0; at m=4, a=2, 9 < 16.  Endpoint 2 < 3.  (m, y) = (4, 2).
  n=7: 7 →11 →17 →26 →13 →20 →10 →5.  Parities 1,1,1,0,1,0,0; a=4 after m=5 (81 < 32 no),
       m=6 (81 < 64 no), m=7 (81 < 128 yes).  Endpoint 5 < 7.  (m, y) = (7, 5).
Rozier–Terracol Cor 5.4 (t(n) = τ(n) for 2 ≤ n ≤ 2.8·10^19) covers n ≤ 4614 by citing
Terras 1976 / Garner 1981; the zero-failure assertion below re-derives that range directly.
"""
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def run(limit):
    out = subprocess.run([sys.executable, str(SCRIPT), "cst-check", str(limit)],
                         capture_output=True, text=True, check=True).stdout
    failures = None
    anchors = {}
    for line in out.splitlines():
        parts = line.split()
        if parts[:1] == ["failures"]:
            failures = int(parts[1])
        elif parts[:1] == ["anchor"]:
            anchors[int(parts[1])] = tuple(int(x) for x in parts[2:])
    return failures, anchors


def test_hand_anchors():
    _, anchors = run(10)
    assert anchors[3] == (4, 2)
    assert anchors[7] == (7, 5)


def test_no_failure_to_4614():
    failures, _ = run(4614)
    assert failures == 0
