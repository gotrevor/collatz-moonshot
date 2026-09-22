"""Hand-checked anchors for `sibling_survivors.py`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_sibling_survivors.py -q

5n+1 (a=5, s=+1), by hand:
  13 -> 33 -> 83 -> 208 -> 104 -> 52 -> 26 -> 13: word 1110000, m=7, K=3, 125 < 128,
      every proper prefix supercritical (2^6 = 64 <= 125); one odd run; E = 0.
      N = 2^7*13 - 5^3*13 = 1664 - 1625 = 39, D = 3, and 39 ≡ 0 = 125*0 (mod 3).
  17 -> 43 -> 108 -> 54 -> 27 -> 68 -> 34 -> 17: word 1100100, m=7, K=3; two odd runs; E = 0.
      N = 128*17 - 125*17 = 51 ≡ 0 (mod 3).
  5 -> 13 enters the 13-cycle from below.  Walk after one step: log 2 - log 5 = -0.9163;
      each lap of the cycle adds 7 log 2 - 3 log 5 = 0.0237 > 0, so the first crossing needs
      ceil(0.9163/0.0237) = 39 laps: m = 1 + 39*7 = 274, K = 1 + 39*3 = 118, odd runs = 39,
      E = 13 - 5 = 8.
  No other survivor below 10^4 (the only cycle entries from below are 5 -> 13; 10 is even).
3n-1 (a=3, s=-1): N < 0, so D*n + 2^m*E = N has no solution: zero survivors.
3n+1: zero survivors below 10^4 (CST is verified far beyond).

`words 8` (a=3), by hand:
  m=1: the single word 0 (an even start descends at once), K=0, u = 2, N = 0: 0 <= 0.
  m=2: the single word 10, K=1, u = 4/3, N = 1: N/2^m = 1/4 <= K/(3u) = 1/4.
  m=4: the single word 1100, K=2, u = 16/9, N = 5: 5/16 <= 2*9/48 = 3/8.
  m=5: words 11100 (N=19), 11010 (N=23), K=3, u = 32/27: max = 23/32 <= 27/32.
  m=7: words 1111000 (N=65), 1110100 (N=73), 1101100 (N=85), K=4, u = 128/81: 85/128 <= 4*81/384 = 27/32.
  m=8: seven words, K=5, u = 256/243; max numerator 319 (swap-audit table): 319/256 <= 5*243/768.
  No first-crossing word of length 3 or 6 (3^K < 2^m <= 2*3^K has no solution).
  Every listed word is primitive (a proper power u^j would have 2^m = (2^|u|)^j <= 3^K).
"""
import subprocess
import sys
from pathlib import Path
from fractions import Fraction

SCRIPT = Path(__file__).with_name("sibling_survivors.py")


def run(*args):
    return subprocess.run([sys.executable, str(SCRIPT), *args],
                          capture_output=True, text=True, check=True).stdout


def rows(*args):
    return [tuple(int(x) if x.isdigit() else x for x in line.split())
            for line in run(*args).splitlines() if not line.startswith("#")]


def test_five_n_plus_one():
    got = rows("survivors", "5", "1", "10000", "2000")
    assert got == [(5, 274, 118, 39, 8, "True"), (13, 7, 3, 1, 0, "True"),
                   (17, 7, 3, 2, 0, "True")]


def test_sign_and_three():
    assert rows("survivors", "3", "-1", "10000") == []
    assert rows("survivors", "3", "1", "10000") == []


def test_words():
    got = {}
    for line in run("words", "8").splitlines():
        m, K, u, cnt, prim, mx, bound = line.split()
        got[int(m)] = (int(K), int(cnt), int(prim), Fraction(mx), Fraction(bound))
    assert set(got) == {1, 2, 4, 5, 7, 8}
    assert got[7] == (4, 3, 1, Fraction(85, 128), Fraction(27, 32))
    assert got[1] == (0, 1, 1, Fraction(0), Fraction(0))
    assert got[2] == (1, 1, 1, Fraction(1, 4), Fraction(1, 4))
    assert got[4] == (2, 1, 1, Fraction(5, 16), Fraction(3, 8))
    assert got[5] == (3, 2, 1, Fraction(23, 32), Fraction(27, 32))
    assert got[8] == (5, 7, 1, Fraction(319, 256), Fraction(5 * 243, 768))
