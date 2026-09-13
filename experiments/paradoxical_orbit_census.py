#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Complete census of acyclic paradoxical segments of a fixed LENGTH m, by orbit enumeration.

Independent-origin control for the word census (paradoxical_block_distribution.py enumerates words
and reconstructs residues; this enumerates STARTS and reads the parity itinerary off the orbit),
and the only feasible route past m = 27: the word population C(m-1,a-1) is ~10^12 at (46,29), but
every admitting start is small.  Bound (exact): an odd start n whose length-m word has a odd
letters is acyclic paradoxical iff D*n < N(v) with D = 2^m - 3^a > 0, and N(v) <= N_max(m,a) =
2^(m-a+1)(3^(a-1) - 2^(a-1)) + 3^(a-1) (paradoxical_random_model.closed_form_Nmax, checked
against the DP and enumeration), so  n <= X(m) := max_a floor((N_max(m,a) - 1) / D(m,a)).
Enumerating all odd n <= X(m) therefore finds EVERY front-normalized acyclic paradoxical segment
of length m, for every a at once.  Values stay below 2^63 on subcritical rows (n * (3/2)^a); rows
that leave the subcritical range are masked by their exact odd count before any wrap matters, and
every hit is re-verified in exact Python integers.

Usage:  paradoxical_orbit_census.py M [--quiet] [--horizon H] [--trunks]
  --trunks groups the admitting starts by the MINIMUM of their length-m orbit (the "trunk" t at
  depth k): every admitting segment is a descent from n0 to t followed by t's climb, so the
  clusters, not the words, are the independent events.  Also reports whether t lies on the
  trajectory of 27 (the record climber 27 -> 9232).
Known-answer controls: m=8 gives starts 7, 9, 19, 25 (a=5); m=27 gives the 19 words of the word
census at a=17 (starts 165 .. 885).

Results 2026-09-13 (admitting words = admitting starts once 2^m > X): see the KB leaf
projects/moonshot-review-2026-09-13.md §7.1 and the commit message.
"""
import sys, os, time
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import tstep, trace_word, ones, numer_fast
from paradoxical_random_model import closed_form_Nmax, closed_form_SN, dp_aggregates
from paradoxical_block_distribution import word_fields, fmt, n_odd_blocks


def subcritical_as(m):
    return [a for a in range(1, m + 1) if 3 ** a < 2 ** m]


def start_bound(m):
    """X(m) and the per-a bounds, from the closed-form N_max (cross-checked with the DP for m <= 30)."""
    per_a = {}
    for a in subcritical_as(m):
        D = 2 ** m - 3 ** a
        Nmax = closed_form_Nmax(m, a)
        if m <= 30:
            assert dp_aggregates(m, a)[2] == Nmax, (m, a)
        per_a[a] = (Nmax - 1) // D
    return max(per_a.values()), per_a


def census(m, quiet=False, horizon=100_000, chunk=4_000_000):
    t0 = time.time()
    X, per_a = start_bound(m)
    a_max = max(per_a)
    print(f"m={m}: subcritical a <= {a_max}; start bound X = {X} (from a={max(per_a, key=per_a.get)}); "
          f"enumerating {(X - 1) // 2} odd starts in chunks of {chunk}", flush=True)
    hits = []
    lo = 3
    while lo <= X:
        n = np.arange(lo, min(lo + 2 * chunk, X + 1), 2, dtype=np.int64)
        x = n.copy(); cnt = np.zeros_like(n)
        for _ in range(m):
            odd = (x & 1) == 1
            cnt += odd
            x = np.where(odd, (3 * x + 1) >> 1, x >> 1)
        sel = np.nonzero((cnt <= a_max) & (x > n))[0]
        for i in sel:
            n0 = int(n[i]); v = trace_word(n0, m); a = ones(v)
            D = 2 ** m - 3 ** a; N = numer_fast(v)
            assert v[0] and D > 0 and D * n0 < N and a == int(cnt[i]), (n0, a)   # exact re-check
            hits.append((n0, a, v))
        lo += 2 * chunk
    M = 2 ** m
    by_a = {}
    for n0, a, v in hits:
        by_a.setdefault(a, []).append((n0, v))
    print(f"m={m}: {len(hits)} acyclic paradoxical starts <= X, by a: "
          f"{ {a: len(h) for a, h in sorted(by_a.items())} } [{time.time() - t0:.0f}s]", flush=True)
    for a, h in sorted(by_a.items()):
        D = M - 3 ** a
        words = len({n0 % M for n0, _ in h})
        R = Fraction(closed_form_SN(m, a), D * M)
        blocks = {}
        for n0, v in h:
            b = n_odd_blocks(v); blocks[b] = blocks.get(b, 0) + 1
        print(f"  a={a} delta={D / M:.5f} starts={len(h)} words={words} R={float(R):.4f} obs/R={words / float(R):.2f} "
              f"by_blocks={dict(sorted(blocks.items()))} min_start={min(n0 for n0, _ in h)} max_start={max(n0 for n0, _ in h)}",
              flush=True)
        if not quiet:
            for n0, v in sorted(h, key=lambda t: (n_odd_blocks(t[1]), t[0])):
                print(fmt(v, n0, word_fields(v, n0, horizon), horizon), flush=True)
    return hits


def trunks(m, hits):
    traj27 = set(); x = 27
    while x != 1:
        traj27.add(x); x = tstep(x)
    by_t = {}
    for n0, a, v in hits:
        x = n0; orb = [n0]
        for _ in range(m):
            x = tstep(x); orb.append(x)
        k = min(range(m + 1), key=lambda j: orb[j]); t = orb[k]
        by_t.setdefault(t, []).append((n0, k))
    print(f"m={m}: {len(hits)} admitting starts, {len(by_t)} distinct orbit minima (trunks); "
          f"on the 27-trajectory: {sum(1 for t in by_t if t in traj27)}/{len(by_t)}", flush=True)
    for t, l in sorted(by_t.items(), key=lambda kv: -len(kv[1])):
        ks = sorted(k for _, k in l); st = sorted(n0 for n0, _ in l)
        x = t; climb = Fraction(1)                       # t's own climb over the longest window m - k_min
        for _ in range(m - ks[0]):
            x = tstep(x); climb = max(climb, Fraction(x, t))
        print(f"  trunk t={t} on27={t in traj27} cluster={len(l)} depth k={ks[0]}..{ks[-1]} "
              f"climb(t, {m - ks[0]} steps)={float(climb):.1f} starts={st[:6]}{'...' if len(st) > 6 else ''}", flush=True)
    return by_t


if __name__ == "__main__":
    args = sys.argv[1:]
    horizon = int(args[args.index("--horizon") + 1]) if "--horizon" in args else 100_000
    h = census(int(args[0]), quiet="--quiet" in args, horizon=horizon)
    if "--trunks" in args:
        trunks(int(args[0]), h)
