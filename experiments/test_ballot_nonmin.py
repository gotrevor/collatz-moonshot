"""Anchors for `parity_reconstruction.py ballot-nonmin` / `ballot-pair`, driven via the real CLI.

Run:  uv run --with pytest pytest experiments/test_ballot_nonmin.py -q

Conjecture C' (2026-09-19) said: a prefix-supercritical ("ballot") word's numerator is the
least in its class mod 3^a among same-shape words.  It is FALSE; the first counterexample
has length 29.  The independent instrument in this file is direct iteration of the shortcut
map T (n ↦ n/2, (3n+1)/2): a pair (w, u) of one shape is a class collision with
N(w) − N(u) = k·3^a exactly when the starts x_w and x_w + k have parity words w and u and
the same s-th iterate.  The tool's numerator/residue machinery is never used as an anchor.

By hand, the k = 1 family: w = 1001111101 (ones at 0,3,4,5,6,7,9; a = 7),
N(w) = 729 + 8·243 + 16·81 + 32·27 + 64·9 + 128·3 + 512 = 729+1944+1296+864+576+384+512 = 6305;
u = 0111111100, N(u) = 2·(3^7 − 2^7) = 2·2059 = 4118; 6305 − 4118 = 2187 = 3^7, so k = 1.
Starts: 765 → 1148 → 574 → 287 → 431 → 647 → 971 → 1457 → 2186 → 1093 → 1640 (parities
1,0,0,1,1,1,1,1,0,1 = w) and 766 → 383 → 575 → 863 → 1295 → 1943 → 2915 → 4373 → 6560 → 3280
→ 1640 (parities 0,1,1,1,1,1,1,1,0,0 = u).  Neither word is ballot (w fails at prefix 100:
8 > 3; u fails at prefix 0).
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


def test_k1_family_by_hand():
    w, u = "1001111101", "0111111100"
    assert word_and_end(765, 10) == (w, 1640) and word_and_end(766, 10) == (u, 1640)
    out = cli("ballot-pair", w, u)
    assert "N(w)=6305 N(u)=4118" in out and "k=1.0" in out
    assert "x_w=765 x_u=766" in out


def test_cprime_counterexample_length_29():
    """The witness start 490466983 is checked from scratch by iterating T: its parity word is
    the ballot word w (2^j ≤ 3^c at every prefix, exact integers), the start two above it has
    the same-shape word u, and both reach 1061802506 after 29 steps.  So N(w) − N(u) = 2·3^19
    and the ballot word is not the least numerator of its class: C' is false."""
    w = "11101101100110110110110101101"
    u = "10111111110101111011100001100"
    x = 490466983
    assert w.count("1") == u.count("1") == 19 and len(w) == len(u) == 29
    assert ballot_exact(w) and not ballot_exact(u)
    assert word_and_end(x, 29) == (w, 1061802506)
    assert word_and_end(x + 2, 29) == (u, 1061802506)
    out = cli("ballot-pair", w, u)
    assert "k=2.0" in out and "w ballot=True" in out and "u ballot=False" in out


def test_length_22_near_miss_by_iteration():
    """The tool's first success with a 0.6-bit margin (length 22, k = 2) checked by iteration."""
    w = "1110110110010110101101"
    u = "1011111111011100001100"
    x = 1556135
    assert word_and_end(x, 22)[0] == w and word_and_end(x + 2, 22)[0] == u
    assert word_and_end(x, 22)[1] == word_and_end(x + 2, 22)[1] == 1774541


def test_nonmin_cli_small():
    """Shape (4,2) by hand: the colliding pairs are {0011,1001} and {0101,1100}; the words
    starting with 1 (1001, 1100) are the class minima (11 < 20, 5 < 14), so length 4 has no
    success at any margin.  Length 10 with a 1.5-bit margin admits the k = 1 family above
    (min height of 1001111101 is 1·log₂3 − 3 = −1.415 ≥ −1.5), so at least one success, and
    that success has neither word ballot."""
    rows = {int(l.split()[0]): l.split() for l in cli("ballot-nonmin", "10", "1.5").splitlines()
            if l[:1].isdigit()}
    assert rows[4][1] == "0"
    assert int(rows[10][1]) >= 1 and rows[10][3] == "0" and rows[10][4] == "0"
