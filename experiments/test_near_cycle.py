"""Hand-checked anchors for `parity_reconstruction.py near-cycle`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_near_cycle.py -q

rho(v) = N(v) * 3^(-a) mod D with D = 2^m - 3^a, computed by hand:
  m=5, a=3, D=5: the two first-crossing words are 11100 (N=19) and 11010 (N=23);
      3^-3 ≡ 2^-1 ≡ 3 (mod 5), so rho = 4*3 ≡ 2 and 3*3 ≡ 4.  min rho = 2.
  m=8, a=5, D=13: the seven words (numerators from the 2026-09-19 swap-audit table,
      211, 227, 251, 259, 283, 287, 319); 3^5 ≡ 9, 9^-1 ≡ 3 (mod 13);
      residues 3*3=9, 6*3=18≡5, 4*3=12, 12*3=36≡10, 10*3=30≡4, 1*3=3, 7*3=21≡8.  min rho = 3.
The tool also asserts, on every word, that the near-cycle window test agrees with the direct
descent test D*c(v) <= N(v); a failed assertion is a non-zero exit, caught by check=True.
"""
import re
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def rows(max_len):
    out = subprocess.run([sys.executable, str(SCRIPT), "near-cycle", str(max_len)],
                         capture_output=True, text=True, check=True).stdout
    table = {}
    for line in out.splitlines():
        m = re.match(r"^(\d+) (\d+) (\d+) (\d+) (\d+) (\d+) ", line)
        if m:
            g = [int(x) for x in m.groups()]
            table[g[0]] = dict(a=g[1], D=g[2], words=g[3], failures=g[4], min_rho=g[5])
    return table


def test_hand_anchors():
    t = rows(9)
    assert t[5] == dict(a=3, D=5, words=2, failures=0, min_rho=2)
    assert t[8] == dict(a=5, D=13, words=7, failures=0, min_rho=3)
