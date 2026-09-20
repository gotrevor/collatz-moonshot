#!/usr/bin/env python3
"""Carry-budget probe (2026-09-20).  Does surviving a long ballot prefix change the binary
digit structure of the iterates beyond the low bits that literally encode the coming parities?

Starts are random odd integers in [lo, 2*lo) (a contiguous window pins the high bits).
Shortcut map T(n) = (3n+1)/2 (n odd), n/2 (n even).  A start n "survives" k steps if
T^j(n) >= n for all j <= k.  For every start in a window we record, at steps i in STEPS, the
bit-density profile of the iterate (fraction of 1-bits at each position, low to high) and the
carry profile of n + 2n + 1 when the iterate is odd, for survivors vs non-survivors.

Prediction under "the joint is one bit wide, carries flow up": survivors differ from the
control only in the low bits at early steps (they encode the FUTURE word), and not at all at
step k, where the future is unconstrained.  Kummer identity carries = 2*s2(n)+1-s2(3n+1) is
asserted against the bitwise simulation as a self-check.
"""
import sys, random
from collections import defaultdict

def carries(n):
    """Positions where a carry-out occurs computing n + 2n + 1 (n odd)."""
    a, b = n, 2 * n
    c = 1  # the +1 as carry-in at position 0
    out = []
    pos = 0
    while a or b or c:
        s = (a & 1) + (b & 1) + c
        c = s >> 1
        if c:
            out.append(pos)
        a >>= 1; b >>= 1; pos += 1
    return out

def run(lo, count, k, steps, probe_bits):
    stats = {}  # (surv, step) -> dict of accumulators
    def acc(surv, step):
        key = (surv, step)
        if key not in stats:
            stats[key] = dict(n=0, odd=0, bits=[0] * probe_bits, top=0, toplen=0,
                              carry=[0] * probe_bits, c_all=0, s2=0, L=0)
        return stats[key]
    nsurv = 0
    rng = random.Random(20260920)
    for _ in range(count // 2):
        n0 = rng.randrange(lo, 2 * lo) | 1
        n = n0
        traj = [n]
        surv = True
        for _ in range(k):
            n = (3 * n + 1) // 2 if n & 1 else n // 2
            traj.append(n)
            if n < n0:
                surv = False
        nsurv += surv
        for i in steps:
            m = traj[i]
            a = acc(surv, i)
            a['n'] += 1
            L = m.bit_length()
            a['L'] += L
            a['s2'] += bin(m).count('1')
            for p in range(probe_bits):
                a['bits'][p] += (m >> p) & 1
            # bits above probe_bits, below the top 4 (which are size-biased)
            hi = m >> probe_bits
            hiL = max(L - probe_bits - 4, 0)
            if hiL > 0:
                a['top'] += bin(hi & ((1 << hiL) - 1)).count('1')
                a['toplen'] += hiL
            if m & 1:
                a['odd'] += 1
                cs = carries(m)
                assert len(cs) == 2 * bin(m).count('1') + 1 - bin(3 * m + 1).count('1'), m
                a['c_all'] += len(cs)
                for p in cs:
                    if p < probe_bits:
                        a['carry'][p] += 1
    return stats, nsurv

if __name__ == '__main__':
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 40
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 1 << 18
    k = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    steps = [0, k // 2, k]
    PB = 24
    stats, nsurv = run(lo, count, k, steps, PB)
    print(f"{count//2} random odd starts in [{lo}, 2*{lo}), k={k}: survivors={nsurv} "
          f"({2*nsurv/count:.4f}), seed 20260920")
    for i in steps:
        print(f"\n== step {i} ==")
        for surv in (True, False):
            a = stats.get((surv, i))
            if not a: continue
            n = a['n']
            prof = ' '.join(f"{a['bits'][p]/n:.2f}" for p in range(PB))
            cprof = ' '.join(f"{a['carry'][p]/a['odd']:.2f}" for p in range(PB)) if a['odd'] else '-'
            print(f"{'SURV' if surv else 'ctrl':4} n={n:6d} odd={a['odd']/n:.3f} "
                  f"s2/L={a['s2']/a['L']:.3f} mid-bits density={a['top']/max(a['toplen'],1):.3f} "
                  f"carries/L={a['c_all']/max(a['odd'],1)/(a['L']/n):.3f}")
            print(f"     bit density pos0..{PB-1}: {prof}")
            print(f"     carry prob  pos0..{PB-1}: {cprof}")
