#!/usr/bin/env python3
"""Known-answer control against Rozier–Terracol Theorem 1.3 ("593 paradoxical segments start at or
below 4614"): count every acyclic paradoxical segment (T^m(n) > n, 3^a < 2^m, n > 2) with start
n <= 4614 over ALL lengths.  A window longer than the total stopping time ends in the 1-2 cycle and
cannot exceed n > 2, so the scan is finite.  Result 2026-09-13: exactly 593, by length
{8: 5, 27: 50, 46: 231, 54: 2, 65: 244, 73: 56, 92: 5}; no endpoint equals its start; the five
length-92 segments start at 3567, 4491, 4513, 4521, 4551 (all odd).  Together with
paradoxical_orbit_census.py's complete sweep (588 segments at lengths <= 80, all starts <= 4614,
maximum start exactly 4614 at length 73) this pins the repository's conventions to the paper's.
Usage: paradoxical_rt593_control.py [NMAX]"""
import sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import tstep

def count_segments(nmax=4614):
    count = 0; bylen = Counter(); eq = 0; witnesses = []
    for n in range(3, nmax + 1):
        x = n; a = 0; m = 0
        while True:
            m += 1
            if x % 2 == 1:
                a += 1
            x = tstep(x)
            if x <= 2:
                break
            if 3 ** a < 2 ** m:
                if x > n:
                    count += 1; bylen[m] += 1; witnesses.append((n, m))
                elif x == n:
                    eq += 1
    return count, dict(sorted(bylen.items())), eq, witnesses

if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4614
    count, bylen, eq, w = count_segments(nmax)
    print(f"starts 3..{nmax}, all lengths: {count} acyclic paradoxical segments; {eq} cyclic endpoints; by length {bylen}")
    print("longest:", [t for t in w if t[1] == max(bylen)])
    if nmax == 4614:
        assert count == 593 and eq == 0, "Rozier–Terracol Thm 1.3 control failed"
        print("Rozier–Terracol Theorem 1.3 reproduced: 593")
