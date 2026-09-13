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
of length m, for every a at once.

Arithmetic is numpy int64.  Every ADMITTING row stays exact: for an admitting start n with a odd
letters, each orbit value V_j = T^j(n) satisfies both  V_j < (3/2)^a (n + 1)  (from 2^j V_j =
3^(a_j) n + N_j and N_j < 2^j (3/2)^(a_j))  and  V_j < (2^m / D) ((3/2)^a + 2^(m-a))  (from
V_j <= 2^(m-j) T^m(n) / 3^(a-a_j), T^m(n) < N/D under admission, and the numerator split
N = 3^(a-a_j) N_j + 2^j N' with N' < 2^(m-j-a+a_j) 3^(a-a_j)); orbit_bound(m) = max_a min(both)
is printed and is ~6e14 at m = 92 (5.5e11 at 73, 1e16 at 100), far inside int64.  Rows that are NOT admitting can wrap at
large m (a large n with a front-loaded parity prefix); every row is flagged the moment a value
exceeds (2^63 - 2)/3 (the last value 3x + 1 cannot overflow from) and flagged rows are decided in
exact Python integers, so the scan is complete whatever the bound says, and the count of wrapped
rows is reported.  Unflagged candidates that fail the exact check are an instrument bug and raise.

Usage:  paradoxical_orbit_census.py M [--quiet] [--horizon H] [--trunks] [--workers W]
  --workers W splits the start range over W processes (chunks are independent; default 1).
  --trunks groups the admitting starts by the MINIMUM of their length-m orbit (the "trunk" t at
  depth k): every admitting segment is a prefix from n0 to t followed by t's climb.  Clusters
  expose shared orbit data; no independence between clusters is asserted.  Also reports whether t lies on the
  trajectory of 27 (the record climber 27 -> 9232).
Known-answer controls: m=8 gives starts 7, 9, 19, 25 (a=5); m=27 gives the 19 words of the word
census at a=17 (starts 165 .. 885).

Results 2026-09-13 (admitting words = admitting starts once 2^m > X).  Sweep of every length
2..80: segments exist at exactly five lengths, m = 8, 27, 46, 65, 73, with 4, 19, 101, 155, 41
words (all at the near-critical a = 5, 17, 29, 41, 46); m = 54 has none.  Every trunk (orbit
minimum) at m >= 27 lies on the trajectory of 27: {31, 47} at 27 and 73, {91, 47, 31, 71, 103, 61}
at 46, {31, 47, 91, 103, 71, 23} at 65.  Detail: KB leaf projects/moonshot-review-2026-09-13.md §7.1.
Length 92 (2026-09-13, 10 workers, 84 min, 1.1e11 odd starts): exactly 5 starts, all at a = 58,
3567, 4491, 4513, 4521, 4551 - the five that Rozier-Terracol's count of 593 predicted beyond the
588 of lengths <= 80 (paradoxical_rt593_control.py); trunks 31 (3567, 4491, 4551) and 47 (4513,
4521), both on 27's trajectory; 995 rows left int64 and were decided exactly, none admitting.
"""
import sys, os, time
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import tstep, trace_word, ones, numer_fast
from paradoxical_random_model import closed_form_Nmax, closed_form_SN, dp_aggregates
from paradoxical_block_distribution import word_fields, fmt, n_odd_blocks

LIM = (2 ** 63 - 2) // 3          # x <= LIM  =>  3x + 1 <= 2^63 - 1: no int64 wrap on this step


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


def orbit_bound(m):
    """B(m): every orbit value of every admitting start of length m is < B(m) (docstring argument)."""
    best = Fraction(0)
    for a, Xa in start_bound(m)[1].items():
        if Xa < 3:
            continue
        D = 2 ** m - 3 ** a
        naive = Fraction(3, 2) ** a * (Xa + 1)
        split = Fraction(2 ** m, D) * (Fraction(3, 2) ** a + 2 ** (m - a))
        best = max(best, min(naive, split))
    return best


def _scan_chunk(job):
    """Odd starts n in [lo, hi] of length-m orbits.  Returns (hits, rows_wrapped, wrapped_hits)."""
    m, a_max, lo, hi = job
    n = np.arange(lo, hi + 1, 2, dtype=np.int64)
    x = n.copy(); cnt = np.zeros_like(n); wrapped = np.zeros(n.shape, dtype=bool)
    for _ in range(m):
        wrapped |= x > LIM
        odd = (x & 1) == 1
        cnt += odd
        x = np.where(odd, (3 * x + 1) >> 1, x >> 1)
    mask = (cnt <= a_max) & (x > n)
    hits = []; wrapped_hits = 0
    for i in np.nonzero(mask | wrapped)[0]:
        n0 = int(n[i]); v = trace_word(n0, m); a = ones(v)
        D = 2 ** m - 3 ** a; N = numer_fast(v)
        admits = D > 0 and D * n0 < N
        if wrapped[i]:
            wrapped_hits += admits
        else:
            assert admits and a == int(cnt[i]), (n0, a, int(cnt[i]))   # exact re-check of the int64 path
        if admits:
            hits.append((n0, a, v))
    return hits, int(wrapped.sum()), wrapped_hits


def census(m, quiet=False, horizon=100_000, chunk=4_000_000, workers=1):
    t0 = time.time()
    X, per_a = start_bound(m)
    a_max = max(per_a)
    B = orbit_bound(m)
    print(f"m={m}: subcritical a <= {a_max}; start bound X = {X} (from a={max(per_a, key=per_a.get)}); "
          f"enumerating {(X - 1) // 2} odd starts in chunks of {chunk} on {workers} worker(s); "
          f"admitting orbits stay below B(m) = {float(B):.3g} ({'inside' if B < 2 ** 63 else 'OUTSIDE'} int64)",
          flush=True)
    jobs = [(m, a_max, lo, min(lo + 2 * chunk - 1, X)) for lo in range(3, X + 1, 2 * chunk)]
    hits = []; rows_wrapped = 0; wrapped_hits = 0
    if workers > 1:
        from multiprocessing import Pool
        pool = Pool(workers); results = pool.imap(_scan_chunk, jobs)
    else:
        pool = None; results = map(_scan_chunk, jobs)
    step = max(1, len(jobs) // 10)
    for k, (h, w, wh) in enumerate(results, 1):
        hits += h; rows_wrapped += w; wrapped_hits += wh
        if len(jobs) >= 20 and k % step == 0:
            print(f"  ... {k}/{len(jobs)} chunks, {len(hits)} hits so far [{time.time() - t0:.0f}s]", flush=True)
    if pool is not None:
        pool.close(); pool.join()
    M = 2 ** m
    by_a = {}
    for n0, a, v in hits:
        by_a.setdefault(a, []).append((n0, v))
    print(f"m={m}: {len(hits)} acyclic paradoxical starts <= X, by a: "
          f"{ {a: len(h) for a, h in sorted(by_a.items())} }; rows that left int64 (decided exactly): "
          f"{rows_wrapped}, admitting among them: {wrapped_hits} [{time.time() - t0:.0f}s]", flush=True)
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
    workers = int(args[args.index("--workers") + 1]) if "--workers" in args else 1
    h = census(int(args[0]), quiet="--quiet" in args, horizon=horizon, workers=workers)
    if "--trunks" in args:
        trunks(int(args[0]), h)
