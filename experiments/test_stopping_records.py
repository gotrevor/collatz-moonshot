"""Hand-checked anchors for `parity_reconstruction.py stopping-records`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_stopping_records.py -q

Shortcut stopping times by hand:
  σ(2) = 1 (2 → 1).
  σ(3) = 4 (3 → 5 → 8 → 4 → 2; the first value below 3 is 2 at step 4).
  σ(7) = 7 (7 → 11 → 17 → 26 → 13 → 20 → 10 → 5; every earlier value is ≥ 7).
  σ(27) = 59 (the classical record; 27 is the least start with σ ≥ 59, cf. the coalescence
  anchor c(27) = 59 in test_coalescence.py, computed by hand there).
  Between 7 and 27 no start beats 7: 15 → 23 → 35 → 53 → 80 → 40 → 20 → 10 has σ(15) = 7.
So the record list up to 100 is exactly [(2, 1), (3, 4), (7, 7), (27, 59)].
"""
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("parity_reconstruction.py")


def records(limit):
    out = subprocess.run([sys.executable, str(SCRIPT), "stopping-records", str(limit)],
                         capture_output=True, text=True, check=True).stdout
    rows = []
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0].isdigit():
            rows.append((int(parts[0]), int(parts[1])))
    return rows


def test_records_to_100():
    assert records(100) == [(2, 1), (3, 4), (7, 7), (27, 59)]
