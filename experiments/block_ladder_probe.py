#!/usr/bin/env python3
"""Odd-block ladder probe for acyclic paradoxical segments (FRONT-A-PARADOXICAL follow-up).

Question.  Front B has the m-cycle ladder (Steiner m=1, Simons-de Weger m<=75, Hercher m<=91).
Front A's paradoxical project proved the 1-block (Rozier-Terracol App. A) and 2-block exclusions.
Is there a b-block ladder: for each fixed number b of odd blocks, finitely many acyclic paradoxical
words?  Two exact-integer probes (host run 2026-09-01, ~20 s total):

  Probe 1.  Front-normalized 3-odd-block words [T]^b[F]^c[T]^d[F]^e[T]^f[F]^g (b,c,d,e,f>=1, g>=0),
            all lengths 3..26 exhaustively (65,780 words at j=26).  RESULT: exactly four words admit
            an acyclic paradoxical start, ALL of length 8 (the 7->8 family, e.g. (1,1,3,1,1,1) from
            n=9 and (1,1,2,2,2,0) from n=25); zero for every j in 9..26.
            Rung-3 conjecture: every 3-odd-block acyclic paradoxical segment has length 8.
            (acyclicParadoxical_seven_eight in Assumed/Paradoxical.lean is the kernel-checked
            existence half; this probe is the word-based instrument.)

  Probe 2.  Orbit-based (no numer, no residue reconstruction): minimum odd-block count of an acyclic
            paradoxical window, per window length m, starts < 300000, m <= 160.  Windows exist only
            for m in 8..92 in that range; the minimum steps up: m=8 -> 3, 27 -> 6, 46 -> 9,
            54 -> 12, 65 -> 13, 73 -> 17, 92 -> 22 (roughly blocks >= 0.22 m).

Caveat that limits what Probe 2 can mean: under Rozier-Terracol Conjecture 6.1 (no paradoxical start
above 4614) the set of acyclic paradoxical windows is FINITE and a start range of 300000 already
contains all of it, so any word-level statistic over that set is a fact about a finite list, not a law
about hypothetical long windows.  Only a proved rung carries content.

Usage: python3 experiments/block_ladder_probe.py   (run from the repo root; exact ints, no floats)
"""
import sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast, realizing_residue_fast, tstep


def admits_acyclic(v):
    """Least realizing start n > 2 of word v if it is an ACYCLIC paradoxical start, else None."""
    m = len(v); a = sum(v); p = 3 ** a; M = 2 ** m
    if p >= M:
        return None
    d = M - p; num = numer_fast(v); r = realizing_residue_fast(v)
    n0 = r
    while n0 <= 2:
        n0 += M
    return n0 if d * n0 < num else None


def three_block_words(j):
    for b in range(1, j):
        for c in range(1, j - b):
            for d in range(1, j - b - c):
                for e in range(1, j - b - c - d):
                    for f in range(1, j - b - c - d - e + 1):
                        g = j - b - c - d - e - f
                        if g < 0:
                            continue
                        yield ([True] * b + [False] * c + [True] * d + [False] * e
                               + [True] * f + [False] * g), (b, c, d, e, f, g)


def probe1(jmax=26):
    print("== Probe 1: 3-odd-block words admitting an acyclic paradoxical start, by length j ==")
    total = 0
    for j in range(3, jmax + 1):
        words = 0; hits = []
        for v, params in three_block_words(j):
            words += 1
            n0 = admits_acyclic(v)
            if n0 is not None:
                hits.append((params, n0))
        total += len(hits)
        print(f"j={j:2d} words={words:6d} admitting={len(hits):3d} cumulative={total:3d} e.g. {hits[:2]}")


def probe2(nmax=300000, mmax=160):
    print(f"\n== Probe 2: min odd-block count of acyclic paradoxical windows per length (starts<{nmax}, m<={mmax}) ==")
    minb = {}
    for n in range(3, nmax):
        x = n; blocks = 0; prev_odd = False; p = 1
        for m in range(1, mmax + 1):
            odd = (x % 2 == 1)
            if odd:
                p *= 3
                if not prev_odd:
                    blocks += 1
            prev_odd = odd
            x = tstep(x)
            if p < (1 << m) and x > n and (m not in minb or blocks < minb[m][0]):
                minb[m] = (blocks, n)
    last = None
    for m in sorted(minb):
        if minb[m][0] != last:
            print(f"m={m:3d}: blocks>={minb[m][0]:2d}  witness n={minb[m][1]}")
            last = minb[m][0]
    ms = sorted(minb)
    print(f"lengths with any acyclic paradoxical window: {ms[0]}..{ms[-1]}")


if __name__ == "__main__":
    t0 = time.time(); probe1(); probe2(); print(f"done in {time.time() - t0:.1f}s")
