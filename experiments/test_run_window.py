"""Hand-checked anchors for `parity_reconstruction.py run-window`, via the real CLI.

  a_min(1, 5): e = v2(3 - 1) = 1, modulus 2^6 = 64, 3^-1 ≡ 43 (3·43 = 129 ≡ 1), so
      a ≡ (1 - 2)·43 ≡ -43 ≡ 21 (mod 64); check 3·21 = 63 ≡ -1 = 1 - 2.  a_min = 21.
  a_min(12, 5): e = v2(3^12 - 1) = v2(531440) = 4 (531440 = 16·33215), modulus 2^9 = 512,
      3^12 = 531441 = 1037·512 + 497, so 3^12 ≡ 497 ≡ -15 = 1 - 16: a = 1 works.  a_min = 1.
      (Orbit check: 4095 → 12 odd steps → 3^12 - 1 = 531440 → /16 → 33215, and 33216 = 2^6·519,
      a next run of length 6 ≥ 5.)
"""
import re
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def test_anchors():
    out = subprocess.run([sys.executable, str(SCRIPT), "run-window", "20"],
                         capture_output=True, text=True, check=True).stdout
    m = re.search(r"anchors: a_min\(1,5\) = (\d+)  a_min\(12,5\) = (\d+)", out)
    assert m and m.group(1) == "21" and m.group(2) == "1"
