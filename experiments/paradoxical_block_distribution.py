#!/usr/bin/env python3
"""Exact census of admitting acyclic paradoxical words at a fixed (m, a), with excursion fields.

Population and admission as in paradoxical_random_model.py: front-normalized words v (first letter
odd), length m, a odd letters; N = numer(v), M = 2^m, D = M - 3^a > 0; the least realizing start
n0 > 2 (residue via the affine identity, paradoxical.realizing_residue_affine) admits iff D*n0 < N.
The census counts admitting WORDS at their least start; `starts` reports how many starts in the
class admit (all n ≡ n0 mod M with D*n < N).

Per admitting word, the observables the 2026-09-13 campaign brief asks to keep separate:
  E        = N/M = (1/2) sum_{i: v_i odd} Q_{i+1}, Q_i = prod_{j>=i} 3^{v_j}/2   (checked exactly)
  H        = max_{i: v_i odd} Q_{i+1}            sandwich quantity: H/2 <= E <= a*H/2 (checked)
  Hs       = max_{1<=i<=m+1} Q_i = max(1, 3H/2)  suffix amplification (empty suffix = 1 included)
  P        = max_{1<=j<=m} prod_{i<j} 3^{v_i}/2    max prefix product
  peak     = max_{0<=j<=m} T^j(n0)/n0             realized orbit peak of the least start
  end      = T^m(n0)/n0 = (3^a n0 + N)/(M n0)     endpoint ratio (>1 iff acyclic paradoxical)
  descent  = least j with T^j(n0) < n0 (or '-')   first descent inside the segment
  tau      = hitting time of {1,2} from n0        censored at --horizon (default 10^5): 'ge<H>'
Aggregates: block-count histogram, the continuous null R = sum min(1, N/(D*M)) and the odd-residue
null R_odd = sum (2/M) clamp(floor((N-1-D)/(2D)), 0, M/2), both exact, and observed/expected.

Usage:
  paradoxical_block_distribution.py M A [--horizon H] [--quiet]
  paradoxical_block_distribution.py --controls        the brief's three word-level controls
  paradoxical_block_distribution.py --selftest        (8,5) known answer + identity checks

Results 2026-09-13: (8,5) 4 admitting words (all 3 blocks; starts 7, 9, 19, 25), R = 5.0802,
R_odd = 4.8047.  (27,17) 19 admitting words {7 blocks: 9, 8: 8, 9: 1, 10: 1}, R = 10.8619.
"""
import sys, os, time
from fractions import Fraction
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast, realizing_residue_affine, tstep, ones


def n_odd_blocks(v):
    return sum(1 for i in range(len(v)) if v[i] and (i == 0 or not v[i - 1]))


def least_start(v):
    M = 1 << len(v); r = realizing_residue_affine(v)
    return r if r > 2 else r + M


def admitting_starts(v, n0):
    """Number of starts n ≡ n0 (mod M), n >= n0, with D*n < N."""
    m = len(v); M = 1 << m; D = M - 3 ** ones(v); N = numer_fast(v)
    nmax = (N - 1) // D
    return 0 if n0 > nmax else (nmax - n0) // M + 1


def word_fields(v, n0, horizon=100_000):
    m = len(v); a = ones(v); M = 1 << m; N = numer_fast(v)
    E = Fraction(N, M)
    # suffix products Q_{i+1} for odd positions i, prefix products before each position
    Q = []; tail_ones = 0
    for i in range(m - 1, -1, -1):          # Q_{i+1} = 3^{ones(v[i+1:])} / 2^{m-i-1}
        if v[i]:
            Q.append(Fraction(3 ** tail_ones, 1 << (m - i - 1)))
            tail_ones += 1
    assert E == sum(Q) / 2, "E = (1/2) sum Q identity"
    H = max(Q); Hs = max(Fraction(1), 3 * H / 2)     # Q_i = (3/2) Q_{i+1} at an odd letter i
    assert H / 2 <= E <= Fraction(a) * H / 2, "H/2 <= E <= aH/2"
    pref = 0; P = Fraction(0)
    for j in range(1, m + 1):
        pref += v[j - 1]
        P = max(P, Fraction(3 ** pref, 1 << j))
    # realized orbit of the least start
    x = n0; peak = Fraction(1); peak_at = 0; descent = None
    for j in range(1, m + 1):
        x = tstep(x)
        r = Fraction(x, n0)
        if r > peak:
            peak, peak_at = r, j
        if descent is None and x < n0:
            descent = j
    end = Fraction(x, n0)
    assert end == Fraction(3 ** a * n0 + N, M * n0), "iterate identity"
    # hitting time of {1,2}
    x = n0; tau = None
    for j in range(1, horizon + 1):
        x = tstep(x)
        if x <= 2:
            tau = j; break
    return dict(E=E, H=H, Hs=Hs, P=P, peak=peak, peak_at=peak_at, end=end, descent=descent, tau=tau,
                starts=admitting_starts(v, n0))


def fmt(v, n0, f, horizon):
    w = ''.join('T' if x else 'F' for x in v)
    tau = f['tau'] if f['tau'] is not None else f"ge{horizon}"
    return (f"  {w} blocks={n_odd_blocks(v)} n0={n0} starts={f['starts']} E={float(f['E']):.4f} "
            f"H={float(f['H']):.4f} Hs={float(f['Hs']):.4f} P={float(f['P']):.4f} peak={float(f['peak']):.4f}@{f['peak_at']} "
            f"end={float(f['end']):.4f} descent={f['descent'] if f['descent'] is not None else '-'} tau={tau}")


def census(m, a, horizon=100_000, quiet=False):
    M = 1 << m; D = M - 3 ** a
    assert D > 0
    DM = D * M; half = M // 2
    t0 = time.time(); n = 0; clip = 0; odd = 0
    by_blocks = {}; hits = []
    for odd_pos in combinations(range(1, m), a - 1):      # position 0 odd (front-normalized)
        v = [False] * m; v[0] = True
        for i in odd_pos:
            v[i] = True
        n += 1
        N = numer_fast(v)
        clip += min(N, DM)
        c = (N - 1 - D) // (2 * D)
        odd += min(max(c, 0), half)
        if N <= 3 * D:                # exact prefilter: D*n0 < N needs n0 >= 3
            continue
        n0 = least_start(v)
        if D * n0 < N:
            b = n_odd_blocks(v)
            by_blocks[b] = by_blocks.get(b, 0) + 1
            hits.append((v, n0))
    R = Fraction(clip, DM); R_odd = Fraction(2 * odd, M); k = len(hits)
    print(f"m={m} a={a} delta={D/M:.5f} words={n} admitting={k} by_blocks={dict(sorted(by_blocks.items()))} "
          f"R={float(R):.4f} R_odd={float(R_odd):.4f} obs/R={k/float(R):.2f} obs/R_odd={k/float(R_odd):.2f} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    if not quiet:
        for v, n0 in sorted(hits, key=lambda h: (n_odd_blocks(h[0]), h[1])):
            print(fmt(v, n0, word_fields(v, n0, horizon), horizon), flush=True)
    return hits, R, R_odd


def controls(horizon=100_000):
    """The three word-level controls from the brief, with the same fields."""
    print("control 1: the Rozier-Terracol 7 -> 8 orbit (first descent at step 7, paradoxical at 8)")
    x = 7; orb = [7]
    for _ in range(8):
        x = tstep(x); orb.append(x)
    print(f"  orbit {orb}: first descent at step {next(j for j, y in enumerate(orb) if y < 7)}, "
          f"T^8(7) = {orb[8]} >= 7")
    v = [n % 2 == 1 for n in orb[:8]]
    print(fmt(v, 7, word_fields(v, 7, horizon), horizon))
    print("control 2: 1^a 0^b - one block, E = 2^-b((3/2)^a - 1) < 1, Hs = 1, P = (3/2)^a")
    for a, b in ((5, 4), (10, 7), (20, 13)):
        v = [True] * a + [False] * b
        f = word_fields(v, least_start(v), horizon)
        assert f['E'] == Fraction(3 ** a - 2 ** a, 2 ** (a + b)) and f['Hs'] == 1 and f['P'] == Fraction(3 ** a, 2 ** a)
        print(fmt(v, least_start(v), f, horizon) + f"  admits={f['end'] > 1}")
    print("control 3: balanced rho-word (v_i = ceil(i rho) - ceil((i-1) rho), rho = log2/log3) + 00:")
    print("  prefix products in [1,3), Hs = 1, but E >= a/24 grows without bound")
    for L in (10, 30, 60, 120):
        def c(i):   # ceil(i*rho) = least k with 3^k >= 2^i, exact
            k = 0
            while 3 ** k < 2 ** i:
                k += 1
            return k
        v = [c(i) - c(i - 1) == 1 for i in range(1, L + 1)] + [False, False]
        a = ones(v); f = word_fields(v, least_start(v), horizon)
        assert f['Hs'] == 1 and f['E'] >= Fraction(a, 24) and 1 <= f['P'] < 3
        print(f"  L={L} a={a} E={float(f['E']):.3f} (a/24={a/24:.3f}) H={float(f['H']):.4f} Hs={float(f['Hs']):.4f} "
              f"P={float(f['P']):.4f} blocks={n_odd_blocks(v)} admits={f['end'] > 1}")


def selftest():
    hits, R, R_odd = census(8, 5, quiet=True)
    assert sorted(n0 for _, n0 in hits) == [7, 9, 19, 25], [n0 for _, n0 in hits]   # orbit-based check: the only odd n <= 1000 with T^8(n) > n, 3^ones < 2^8
    assert all(n_odd_blocks(v) == 3 for v, _ in hits)
    assert R == Fraction(16907, 13 * 256) and R_odd == Fraction(615, 128)
    print("selftest (8,5): four admitting words, starts 7 9 19 25, all 3 blocks; R=16907/3328, R_odd=615/128")
    # identities on every word at (8,5) and (12,7), admitting or not
    for m, a in ((8, 5), (12, 7)):
        for odd_pos in combinations(range(1, m), a - 1):
            v = [False] * m; v[0] = True
            for i in odd_pos:
                v[i] = True
            word_fields(v, least_start(v), horizon=1000)
    print("selftest: E-identity, H-sandwich, iterate identity hold on every word at (8,5) and (12,7)")


if __name__ == "__main__":
    args = sys.argv[1:]
    horizon = int(args[args.index("--horizon") + 1]) if "--horizon" in args else 100_000
    if args[:1] == ["--selftest"]:
        selftest()
    elif args[:1] == ["--controls"]:
        controls(horizon)
    else:
        census(int(args[0]), int(args[1]), horizon, quiet="--quiet" in args)
