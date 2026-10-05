#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Cycle hunt over Nashida's open entangled G_2 benchmark (driver for g2_orbit_hunt.c).

Builds the C hunter (exact 128-bit arithmetic, memoized halting) and runs it on a spec TSV
(`k<TAB>spec<TAB>category`, Nashida's maps_G2_open.tsv).  Output lines:
    CYCLE  spec  min=  period=  from=     a positive periodic orbit: the map does NOT terminate
    ESCAPE spec  start=  steps=           an orbit passed 2^120 (lucky long run; recheck with `chase`)
    CAP    spec  start=                   no halt / cycle / escape within S steps

    g2_orbit_hunt.py run TSV [N] [S]      # every start 1..N, at most S steps
    g2_orbit_hunt.py chase SPEC START     # follow one orbit with bignums until it halts
    g2_orbit_hunt.py test                 # persistent suite (hand-computed controls)

Result 2026-10-05 (N = 10^7, S = 10^5, 12 min): no CYCLE and no CAP in any of the 4389 maps;
1273 ESCAPE lines, and every escape followed with bignums halts (the longest at 152 steps).
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "g2_orbit_hunt.c"


def build() -> Path:
    out = Path(tempfile.gettempdir()) / "g2_orbit_hunt"
    if not out.exists() or out.stat().st_mtime < SRC.stat().st_mtime:
        subprocess.run(["cc", "-O2", "-o", str(out), str(SRC)], check=True)
    return out


def run(lines: list[str], n: int, s: int) -> list[list[str]]:
    exe = build()
    p = subprocess.run([str(exe), str(n), str(s)], input="".join(lines), capture_output=True,
                       text=True, check=True)
    return [ln.split("\t") for ln in p.stdout.splitlines()]


def parse(spec: str) -> dict[int, tuple[int, int, int]]:
    br = {}
    for part in spec.split(";"):
        r, v = part.split(":")
        br[int(r)] = tuple(int(z) for z in v.split(","))
    return br


def chase(spec: str, x: int, cap: int = 10**6) -> tuple[str, int]:
    br = parse(spec)
    for n in range(cap):
        t = br.get(x % 4)
        if t is None:
            return "halt", n
        a, b, e = t
        y = (a * x + b) >> e
        if y < 1:
            return "halt", n
        x = y
    return "alive", cap


def main(argv: list[str]) -> int:
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "run":
        lines = Path(argv[1]).read_text().splitlines(keepends=True)[1:]
        n = int(argv[2]) if len(argv) > 2 else 10**5
        s = int(argv[3]) if len(argv) > 3 else 10**5
        for row in run(lines, n, s):
            print("\t".join(row))
        return 0
    if argv[0] == "chase":
        print(*chase(argv[1], int(argv[2])))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite: answers worked out by hand ----

COLLATZ = "0:1,0,1;1:3,1,1;2:1,0,1;3:3,1,1"      # T(x): x/2 or (3x+1)/2, never halts
THREE_MINUS = "0:1,0,1;1:3,-1,1;2:1,0,1;3:3,-1,1"  # x/2 or (3x-1)/2
MAHLER = "0:3,0,1;1:3,1,1;2:3,0,1"                # ceil(3x/2), halts at 3 mod 4


def _cycles(spec: str, n: int) -> set[tuple[str, str]]:
    return {(r[2], r[3]) for r in run([f"2\t{spec}\tX\n"], n, 10**4) if r[0] == "CYCLE"}


def test_collatz_trivial_cycle():
    # 1 -> (3+1)/2 = 2 -> 1
    assert _cycles(COLLATZ, 100) == {("min=1", "period=2")}


def test_three_minus_cycles():
    # 1 -> (3-1)/2 = 1;  5 -> 7 -> 10 -> 5;  17 -> 25 -> 37 -> 55 -> 82 -> 41 -> 61 -> 91 -> 136
    #   -> 68 -> 34 -> 17 (11 steps)
    assert _cycles(THREE_MINUS, 100) == {("min=1", "period=1"), ("min=5", "period=3"),
                                         ("min=17", "period=11")}


def test_mahler_map_silent():
    # strictly increasing, so no cycle; 1 -> 2 -> 3 halts, 4 -> 6 -> 9 -> 14 -> 21 -> 32 -> 48
    #   -> 72 -> 108 -> 162 -> 243 (= 3 mod 4) halts
    assert run([f"2\t{MAHLER}\tX\n"], 1000, 10**4) == []
    assert chase(MAHLER, 4) == ("halt", 10)


def test_escape_flag_is_not_divergence():
    # 2026-10-05 benchmark escape: an orbit from 1447 passes 2^120, then halts at step 152
    spec = "0:3,0,1;2:9,2,2;3:9,1,0"
    assert any(r[0] == "ESCAPE" for r in run([f"2\t{spec}\tX\n"], 1447, 10**5))
    assert chase(spec, 1447) == ("halt", 152)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
