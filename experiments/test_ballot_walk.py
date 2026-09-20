"""Anchors for `parity_reconstruction.py ballot-walk`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_ballot_walk.py -q

The walk: Φ = 3^d·B − A for the trajectories A, B of x and x + k, d = ones(w) − ones(u),
M = 3^max(0,−d)·Φ; M even ⇔ the two letters agree.  Both words are kept exactly ballot.

By hand, k = 4, S = 3.  j = 0: M = 4, both words must start with 1 (ballot), (1,1) gives
M = (12 + 1 − 1)/2 = 6, d = 0.  j = 1: M = 6 even; (0,0) would give w = 10 with 4 > 3, so
only (1,1): M = (18 + 0)/2 = 9.  j = 2: M = 9 odd, letters differ: (1,0) → M = (27 − 1)/2 = 13,
d = 1 (w = 111, u = 110, both ballot); (0,1) from d = 0 → M = (27 + 1)/2 = 14, d = −1 (w = 110,
u = 111).  Nodes visited: 1 + 1 + 1 + 2 = 5, no collision.  S = 4: from (13, d=1, w=111,
u=110): (1,0) makes u = 1100 (16 > 9), dead; (0,1) → M = (13 + 1)/2 = 7, d = 0 (w = 1110,
u = 1101).  From (14, d=−1, w=110, u=111): (0,0) makes w = 1100, dead; (1,1) → M =
(42 + 1 − 3)/2 = 20 (w = 1101, u = 1111).  Nodes: 5 + 2 = 7, no collision.

Conjecture C (two ballot words of one shape never coalesce) is FALSE: the tool's first
collision, at length 34 with k = 4, is re-verified here from scratch by iterating T from the
witness start 15231450875: its parity word is w, the start four above it has parity word u,
both words are ballot (exact integer check), and both reach 27822043514 after 34 steps.
"""
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def tstep(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def word_and_end(x, s):
    w = []
    for _ in range(s):
        w.append("1" if x % 2 else "0")
        x = tstep(x)
    return "".join(w), x


def ballot_exact(w):
    c = 0
    for j, ch in enumerate(w, 1):
        c += ch == "1"
        if 2 ** j > 3 ** c:
            return False
    return True


def cli(*args):
    return subprocess.run([sys.executable, str(SCRIPT), *args],
                          capture_output=True, text=True, check=True).stdout


def test_small_walks_by_hand():
    assert cli("ballot-walk", "3", "4").strip().endswith("nodes=5 collisions=0")
    assert cli("ballot-walk", "4", "4").strip().endswith("nodes=7 collisions=0")


def test_conjecture_c_counterexample_length_34():
    w = "1101101110011011010110110110110101"
    u = "1111111101111011101101011000100100"
    x = 15231450875
    assert len(w) == len(u) == 34 and w.count("1") == u.count("1") == 22
    assert ballot_exact(w) and ballot_exact(u)
    assert word_and_end(x, 34) == (w, 27822043514)
    assert word_and_end(x + 4, 34) == (u, 27822043514)
    out = cli("ballot-walk", "34", "4")
    assert f"  w={w}\n  u={u}\n" in out and "collisions=5" in out


def test_walk_finds_the_cprime_pair_when_u_may_dip():
    """The length-29 C' counterexample (k = 2, u starts 10 and dips 0.415 bits) is found
    once u is allowed a 0.5-bit deficit, and is absent when both must be exactly ballot."""
    out = cli("ballot-walk", "29", "2", "0.5")
    assert "  w=11101101100110110110110101101\n  u=10111111110101111011100001100\n" in out
    assert cli("ballot-walk", "29", "2").strip().endswith("collisions=0")


def test_c_twin_matches(tmp_path):
    """`ballot_walk.c` is the same walk in C; it must reproduce the hand-counted small walks and
    the five length-34 collisions.  Skipped when no C compiler is on the PATH."""
    import shutil
    cc = shutil.which("cc")
    if cc is None:
        import pytest
        pytest.skip("no C compiler")
    exe = tmp_path / "ballot_walk"
    subprocess.run([cc, "-O2", "-o", str(exe), str(SCRIPT.with_name("ballot_walk.c"))], check=True)
    run = lambda *a: subprocess.run([str(exe), *a], capture_output=True, text=True, check=True).stdout
    assert run("3", "4").strip().endswith("nodes=5 collisions=0")
    assert run("4", "4").strip().endswith("nodes=7 collisions=0")
    out = run("34", "4")
    assert "collisions=5" in out
    assert "  w=1101101110011011010110110110110101\n  u=1111111101111011101101011000100100\n" in out
