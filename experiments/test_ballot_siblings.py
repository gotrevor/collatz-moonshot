"""Hand-checked anchors for `parity_reconstruction.py ballot-siblings`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_ballot_siblings.py -q

By hand.  Ballot words (every prefix j has 2^j ≤ 3^(ones)) of length 5 are 11100, 11010, 11011,
11110 and 11111 minus those failing at some prefix: 1 ✓, 11 ✓, 110 (8 ≤ 9) ✓, 1100 (16 ≤ 9) ✗,
1101 ✓ (16 ≤ 27), 111 ✓, 1110 ✓, 1111 ✓; length 5: 11010 (32 ≤ 27) ✗, 11011 ✓, 11100 (32 ≤ 27) ✗,
11101 ✓, 11110 ✓, 11111 ✓.  So s = 5 has exactly 4 ballot words, and by the tool's definition
(supercritical at every prefix INCLUDING length s) 11100 and 11010 are excluded.
Numerators: 11011 = 9+6+16+32 → a=4: N = 27 + 18 + 0 + 8·3 + 16 = 27+18+24+16 = 85;
11101: 27+18+12+16 = 73; 11110: 27+18+12+8 = 65; 11111: 81+54+36+24+16 = 211 (a=5).
Mod 81 (a=4): 85 ≡ 4, 73, 65: distinct.  So no collision at s = 5.
The unrestricted anchor (0011 vs 1001 at shape (4,2), numerators 20 and 11) is checked directly
through `word_numer`.
"""
import importlib.util
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def rows(S):
    out = subprocess.run([sys.executable, str(SCRIPT), "ballot-siblings", str(S)],
                         capture_output=True, text=True, check=True).stdout
    return {int(l.split()[0]): l.split() for l in out.splitlines() if l[:1].isdigit()}


def test_s5_by_hand():
    r = rows(8)
    assert r[5][1] == "4" and r[5][2] == "0"


def test_no_ballot_collision_to_16():
    assert all(r[2] == "0" for r in rows(16).values())


def test_unrestricted_anchor():
    spec = importlib.util.spec_from_file_location("pr", SCRIPT)
    pr = importlib.util.module_from_spec(spec)
    sys.argv = ["x"]
    spec.loader.exec_module(pr)
    assert pr.word_numer([0, 0, 1, 1]) == 20 and pr.word_numer([1, 0, 0, 1]) == 11
    assert (20 - 11) % 9 == 0
