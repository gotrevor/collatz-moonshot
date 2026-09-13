#!/usr/bin/env python3
"""Odd-block ladder: rung census for a fixed number of odd blocks (host probe, 2026-09-13).

Companion to `block_ladder_probe.py` (rung 3).  Enumerates every front-normalized word with exactly
BLOCKS odd blocks, `[T]^b1 [F]^c1 ... [T]^bB [F]^cB` (all interior lengths >= 1, final even tail
>= 0), for every length j up to JMAX, and reports the words admitting an ACYCLIC paradoxical start
(least start > 2 in the word's residue class, exact integer criterion d*n < numer).

Two modes:
    block_ladder_rung_census.py BLOCKS JMAX            # every length 2*BLOCKS-1 .. JMAX
    block_ladder_rung_census.py BLOCKS --fixed M A     # exact length M with exactly A odd steps

Results 2026-09-13 (exact integers, word-exhaustive; known-answer control: BLOCKS=3 reproduces the
four rung-3 words at j=8 and nothing else to 14):
    BLOCKS=4: zero admitting words for every j <= 30  (2 035 800 words at j=30)
    BLOCKS=5: zero admitting words for every j <= 27  (4 686 825 words at j=27)
    BLOCKS=3 at (M,A)=(27,17): zero (5400 words) - rung 3 really is length 8 only
    BLOCKS=4 at (M,A) = (46,29): zero (2 227 680 words); (46,28): zero (2 386 800); (54,34): zero
    (6 219 840, 20 min); (65,41): zero (19 997 120 words, 98 min).  Independent-origin confirmation
    of `paradoxical_orbit_census.py`, whose complete sweep of every length <= 80 finds the
    smallest realized run counts 3@8, 7@27, 9@46, 13@65, 17@73 and nothing with 4 or 5 runs.
Together with `block_ladder_probe.py`'s Probe 2 (min blocks per length: 8->3, 27->6, 46->9, ...,
the picture is: paradoxical windows live only at near-critical lengths (3^a just below 2^m)
and need many short blocks there (smallest observed runs/length ratio 9/46, at 1807@46 - the
"0.22*m" figure is descriptive, not a bound).  Rungs 4 and 5 are empty; front-normalized, the
first rung realized after 3 is 7, at length 27 (the earlier "6 at 27" allowed an even first step).

Caveat (same as block_ladder_probe.py): under Rozier-Terracol Conj. 6.1 the whole set of acyclic
paradoxical windows is a finite list, so only a PROVED uniform-in-BLOCKS statement carries content.
"""
import sys, os, time
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast, realizing_residue_fast


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


def comps_pos(total, parts):
    """Compositions of `total` into `parts` positive parts."""
    if parts == 0:
        if total == 0:
            yield ()
        return
    for cuts in combinations(range(1, total), parts - 1):
        prev = 0; out = []
        for c in cuts:
            out.append(c - prev); prev = c
        out.append(total - prev)
        yield tuple(out)


def words_of_length(j, blocks):
    """All front-normalized `blocks`-odd-block words of length j: 2*blocks-1 positive parts + tail."""
    k = 2 * blocks - 1
    for s in range(k, j + 1):
        for parts in comps_pos(s, k):
            v = []
            for idx, ln in enumerate(parts):
                v += [idx % 2 == 0] * ln
            v += [False] * (j - s)
            yield v, parts + (j - s,)


def words_fixed(m, a, blocks):
    """Words of exact length m with exactly a odd steps and `blocks` odd blocks."""
    for odd in comps_pos(a, blocks):
        for s in range(blocks - 1, m - a + 1):
            for even in comps_pos(s, blocks - 1):
                v = []
                for i in range(blocks):
                    v += [True] * odd[i]
                    if i < blocks - 1:
                        v += [False] * even[i]
                v += [False] * (m - a - s)
                yield v, (odd, even, m - a - s)


def census(gen, label):
    t0 = time.time(); n = 0; hits = []
    for v, params in gen:
        n += 1
        n0 = admits_acyclic(v)
        if n0 is not None:
            hits.append((params, n0))
    print(f"{label} words={n} admitting={len(hits)} e.g. {hits[:4]} [{time.time() - t0:.0f}s]",
          flush=True)
    return hits


if __name__ == "__main__":
    blocks = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == "--fixed":
        m, a = int(sys.argv[3]), int(sys.argv[4])
        assert 3 ** a < 2 ** m
        census(words_fixed(m, a, blocks),
               f"blocks={blocks} m={m} a={a} D/2^m={(2 ** m - 3 ** a) / 2 ** m:.4f}")
    else:
        jmax = int(sys.argv[2]) if len(sys.argv) > 2 else 28
        total = 0
        for j in range(2 * blocks - 1, jmax + 1):
            total += len(census(words_of_length(j, blocks), f"blocks={blocks} j={j:2d}"))
        print(f"cumulative admitting words for blocks={blocks}, j<={jmax}: {total}")
