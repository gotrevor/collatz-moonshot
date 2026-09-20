"""Hand-checked anchors for `parity_reconstruction.py residue-height`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_residue_height.py -q

By hand.  N(v) = Σ_i v_i · 2^i · 3^(ones after i); x_v = (−N · 3^(−a)) mod 2^m is the least
start whose first m parities are v.  At m = 5 the two first-crossing words are
  11100: N = 9 + 6 + 4 = 19, a = 3, 3^(−3) ≡ 19 (mod 32) since 27·19 = 513 = 16·32 + 1,
         x = (−19·19) mod 32 = (−361 + 384) = 23; check 23 → 35 → 53 → 80 → 40 → 20 (1,1,1,0,0).
  11010: N = 9 + 6 + 8 = 23, x = (−23·19) mod 32 = (−437 + 448) = 11;
         check 11 → 17 → 26 → 13 → 20 → 10 (1,1,0,1,0).  Runs: 1 and 2.
So the m = 5 row reads: 2 words, a = 3, min x_v = 11 attained at r = 2, and the by-r minima are
r = 1 → 23 (log2 4.5), r = 2 → 11 (log2 3.5).
"""
import re
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def rows(M):
    out = subprocess.run([sys.executable, str(SCRIPT), "residue-height", str(M)],
                         capture_output=True, text=True, check=True).stdout
    table = {}
    for line in out.splitlines():
        parts = line.split()
        if parts and parts[0].isdigit():
            table[int(parts[0])] = parts
    return table


def test_m5_by_hand():
    row = rows(6)[5]
    assert row[1] == "2" and row[2] == "3" and row[3] == "11" and row[5] == "2"
    byr = dict(re.findall(r"(\d+):([\d.]+)/", " ".join(row)))
    assert byr["1"] == "4.5" and byr["2"] == "3.5"
