"""Hand-computed anchors for g2_mahler_triage.py, driven through the real CLI."""
import json
import subprocess
import sys
from pathlib import Path

CLI = Path(__file__).with_name("g2_mahler_triage.py")


def run(*args):
    return json.loads(subprocess.check_output([sys.executable, str(CLI), *map(str, args)], text=True))


def test_benchmark_row_one():
    # 0: x-1, 1: x+1, 2: (9x-2)/4, 3 halts.  By hand: classes 6, 10 mod 16 survive with
    # c = 1/2, -1/2; y* = 2/5; windows [17/45, 2/5] and [3/5, 28/45]; covering arc 11/45 > 1/9.
    got = run("windows", "0:1,-1,0;1:1,1,0;2:9,-2,2")
    assert got["rho"] == "9/4" and got["M"] == 16
    assert got["classes"] == {"6": "1/2", "10": "-1/2"}
    assert got["ystar"] == "2/5"
    assert got["windows"] == {"6": ["17/45", "2/5"], "10": ["3/5", "28/45"]}
    assert got["arc_length"] == "11/45" and got["wraps"] is False
    assert got["verdict"] == "window-too-wide"


def test_mahler_map_is_not_claimed():
    # Mahler's Z-number map (open since 1968): 3x/2 on 0,2; (3x+1)/2 on 1; 3 halts.  By hand:
    # classes 0,4,6 (c=0), 1,5 (c=1/2) mod 8; windows [0,1/12],[1/6,1/4],[1/2,7/12],[2/3,5/6];
    # largest gap 1/4, so the arc is 3/4 and wraps.  The instrument must not claim this map.
    got = run("windows", "0:3,0,1;1:3,1,1;2:3,0,1")
    assert got["M"] == 8 and got["ystar"] == "0"
    assert got["classes"] == {"0": "0", "1": "1/2", "4": "0", "5": "1/2", "6": "0"}
    assert got["arc_length"] == "3/4" and got["wraps"] is True
    assert got["verdict"] != "terminates-by-FLP"


def test_mixed_map_is_skipped():
    # The shortcut Collatz map itself has a contracting branch (x/2).
    assert run("windows", "0:1,0,1;1:3,1,1")["kind"] == "mixed-contracting"
