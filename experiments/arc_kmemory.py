#!/usr/bin/env -S uv run --quiet --with pytest python3
"""k-memory component game for the symmetric arc [beta, 1 - beta] at a fixed rational beta.

Dominates KRelaxedStrategy (ArcTrap.lean) the way arc_barrier.py's game dominates RelaxedStrategy.
State: window W = [lo, hi] (lo in [0, 1)) and r = m mod 2^k.  The constructor keeps a component C of
W ∩ (Z + [beta, 1 - beta]); the child is 1.5 C + d (d = (r mod 2)/2), shifted by sh = floor(left end);
r' = ((3r - r mod 2)/2 + sh) mod 2^(k-1) + bit * 2^(k-1), where the adversary picks bit AFTER seeing C.
The new bit becomes a parity only k - 1 steps later, so for k >= 2 the adversary commits every parity
before the constructor's intermediate choices.  k = 1 is the memoryless game.

Measured at beta = 0.1229 from W = [0, 3], every residue: the adversary kills within 26 (k = 1),
30 (k = 2), 33 (k = 3) steps.  k = 1 reproduces the 26 of the earlier memoryless minimax.

    arc_kmemory.py kill BETA K DMAX
    arc_kmemory.py depths BETA K DMAX      per-residue kill depths
    arc_kmemory.py mono BETA K DMAX          does the price ever rise along the (k+1) optimal kill tree?
    arc_kmemory.py path BETA K DMAX          price along the (k+1)-game's critical line, every start residue
    arc_kmemory.py lag BETA K DMAX LAYERS [split]  local price of committing one bit before the constructor moves
    arc_kmemory.py track BETA LO HI K DMAX  one window over every residue: (max price, its r, max d1, min d0)
    arc_kmemory.py gaps BETA K DMAX LAYERS [WORST]  extra kill depth one more step of delay costs, per state
                                             (WORST > 0: list the WORST costliest states)
    arc_kmemory.py lines BETA K DMAX         signed residues along each critical line (* = a split)
    arc_kmemory.py depthat BETA LO HI N KMAX DMAX  one window at the integer N, depth for k = 1..KMAX
    arc_kmemory.py endgame BETA K DMAX       endgame entry windows of the optimal kill tree
    arc_kmemory.py holds BETA L              single-piece periodic holds over parity words of length <= L
    arc_kmemory.py test
"""
from __future__ import annotations

import itertools
import math
import subprocess
import sys
from fractions import Fraction as F
from functools import lru_cache

sys.setrecursionlimit(100000)
H = F(1, 2)


def make(beta, k):
    half = 1 << (k - 1)

    @lru_cache(maxsize=None)
    def children(lo, hi, r):
        d = H if r % 2 else F(0)
        out = []
        for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
            a, b = max(lo, j + beta), min(hi, j + 1 - beta)
            if a <= b:
                nl, nh = F(3, 2) * a + d, F(3, 2) * b + d
                sh = math.floor(nl)
                base = ((3 * r - r % 2) // 2 + sh) % half if half > 1 else 0
                out.append((nl - sh, nh - sh, base))
        return tuple(out)

    @lru_cache(maxsize=None)
    def adv(lo, hi, r, D):
        """The adversary forces death within D steps."""
        if D == 0:
            return False
        return all(any(adv(nl, nh, base + bit * half, D - 1) for bit in (0, 1))
                   for nl, nh, base in children(lo, hi, r))

    return adv


def kill_depth(beta, k, dmax):
    """Least D such that the adversary kills every residue from [0, 3] within D steps, else None."""
    adv = make(beta, k)
    for D in range(1, dmax + 1):
        if all(adv(F(0), F(3), r, D) for r in range(1 << k)):
            return D
    return None


def residue_depths(beta, k, dmax):
    """Per residue r < 2^k: least D such that the adversary kills [0, 3] at r within D (None if > dmax)."""
    adv = make(beta, k)
    out = []
    for r in range(1 << k):
        out.append(next((D for D in range(1, dmax + 1) if adv(F(0), F(3), r, D)), None))
    return out


def make_children(beta, k):
    half = 1 << (k - 1)

    def children(lo, hi, r):
        d = H if r % 2 else F(0)
        out = []
        for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
            a, b = max(lo, j + beta), min(hi, j + 1 - beta)
            if a <= b:
                nl, nh = F(3, 2) * a + d, F(3, 2) * b + d
                sh = math.floor(nl)
                base = ((3 * r - r % 2) // 2 + sh) % half if half > 1 else 0
                out.append((nl - sh, nh - sh, base))
        return out

    return children


def make_depth(beta, k):
    """Exact kill depth per state with one memo entry per state (`make`'s lru_cache keeps one per
    (state, D), which ran out of memory at k = 6): depth = 1 + max over components of the min over the
    adversary's bits; `None` when above `cap`."""
    ch = make_children(beta, k)
    half = 1 << (k - 1)
    exact, lower = {}, {}

    def dep(st, cap):
        if st in exact:
            return exact[st] if exact[st] <= cap else None
        if cap <= 0 or lower.get(st, 0) >= cap:
            return None
        worst = 0
        for nl, nh, base in ch(*st):
            best = None
            for bit in (0, 1):
                d = dep((nl, nh, base + bit * half), cap - 1 if best is None else best - 1)
                if d is not None:
                    best = d
            if best is None:
                lower[st] = max(lower.get(st, 0), cap)
                return None
            worst = max(worst, best)
        exact[st] = worst + 1
        return worst + 1

    return dep


def delay_gaps(beta, k, dmax, layers, worst=0):
    """Cost of one more step of delay, state by state.  Over the (k+1)-game states reachable from
    ([0, 3], r) within `layers` moves (any constructor component, either adversary bit), compare the
    kill depth d1 in the (k+1)-game with d0 at the projected k-state (window, r mod 2^k) in the k-game.
    Returns {d1 - d0: count}, with 'k+1 survives' counting states killable in the k-game but not
    within dmax in the (k+1)-game."""
    dep0, dep1 = make_depth(beta, k), make_depth(beta, k + 1)
    ch1 = make_children(beta, k + 1)
    half1 = 1 << k

    seen = set()
    frontier = [(F(0), F(3), r) for r in range(1 << (k + 1))]
    for _ in range(layers + 1):
        nxt = []
        for st in frontier:
            if st in seen:
                continue
            seen.add(st)
            for nl, nh, base in ch1(*st):
                nxt += [(nl, nh, base + bit * half1) for bit in (0, 1)]
        frontier = nxt
    hist, rows = {}, []
    for lo, hi, r in seen:
        d0 = dep0((lo, hi, r % (1 << k)), dmax)
        if d0 is None:
            continue
        d1 = dep1((lo, hi, r), dmax)
        key = "k+1 survives" if d1 is None else d1 - d0
        hist[key] = hist.get(key, 0) + 1
        if d1 is not None:
            rows.append((d1 - d0, lo, hi, r, d0, d1))
    if worst:
        rows.sort(reverse=True)
        return rows[:worst]
    return dict(sorted(hist.items(), key=str))


def lag_costs(beta, k, dmax, layers, split=False):
    """Local price of committing early, in the k-game.  At each state s reachable from [0, 3] within
    `layers` moves, adaptive depth d(s) = 1 + max_c min_b d(child(c, b)) against committed depth
    d_u(s) = 1 + min_b max_c d(child(c, b)) (one bit for every component, then adaptive again).
    Returns {d_u - d: count} ('uniform fails' when no single bit kills within dmax)."""
    dep = make_depth(beta, k)
    ch = make_children(beta, k)
    half = 1 << (k - 1)
    seen, frontier = set(), [(F(0), F(3), r) for r in range(1 << k)]
    for _ in range(layers + 1):
        nxt = []
        for st in frontier:
            if st in seen:
                continue
            seen.add(st)
            for nl, nh, base in ch(*st):
                nxt += [(nl, nh, base + bit * half) for bit in (0, 1)]
        frontier = nxt
    hist = {}
    for st in seen:
        d = dep(st, dmax)
        kids = ch(*st)
        if d is None or not kids:
            continue
        unif = []
        for bit in (0, 1):
            ds = [dep((nl, nh, base + bit * half), dmax) for nl, nh, base in kids]
            unif.append(None if None in ds else 1 + max(ds))
        unif = [u for u in unif if u is not None]
        key = (min(unif) - d) if unif else "uniform fails"
        key = (len(kids), key) if split else key
        hist[key] = hist.get(key, 0) + 1
    return dict(sorted(hist.items(), key=str))


def price_path(beta, k, dmax, r):
    """The (k+1)-game's critical line from ([0, 3], r): the constructor keeps the component whose best
    reply is deepest (ties: largest price), the adversary plays its best bit.  Per move: (d1, d0, price,
    components), with d0 the k-game depth at the projected residue.  (k+1)-memory is the k-game with
    every bit committed one move early, so the price is what those early commitments have added up to."""
    dep0, dep1 = make_depth(beta, k), make_depth(beta, k + 1)
    ch1 = make_children(beta, k + 1)
    half1 = 1 << k
    st, out = (F(0), F(3), r), []
    while True:
        d1, d0 = dep1(st, dmax), dep0((st[0], st[1], st[2] % half1), dmax)
        kids = ch1(*st)
        out.append((d1, d0, None if None in (d0, d1) else d1 - d0, len(kids), st[1] - st[0]))
        if d1 is None or not kids:
            return out
        best = None
        for nl, nh, base in kids:
            reply = min(((dep1((nl, nh, base + b * half1), dmax), (nl, nh, base + b * half1)) for b in (0, 1)),
                        key=lambda x: (x[0] is None, x[0] or 0))
            dd = reply[0]
            if dd is None:
                continue
            nxt = reply[1]
            pr = dd - (dep0((nxt[0], nxt[1], nxt[2] % half1), dmax) or 0)
            if best is None or (dd, pr) > best[0]:
                best = ((dd, pr), nxt)
        if best is None:
            return out
        st = best[1]


def price_monotone(beta, k, dmax):
    """Over the whole (k+1)-game optimal kill tree from [0, 3] (every component, the adversary's best bit),
    does the price d1 - d0 ever rise from a position to its child?  Returns (edges, rises, largest rise,
    root prices)."""
    dep0, dep1 = make_depth(beta, k), make_depth(beta, k + 1)
    ch1 = make_children(beta, k + 1)
    half1 = 1 << k

    def price(st):
        d1, d0 = dep1(st, dmax), dep0((st[0], st[1], st[2] % half1), dmax)
        return None if None in (d0, d1) else d1 - d0

    edges = rises = big = 0
    seen = set()
    roots = []
    stack = []
    for r in range(1 << (k + 1)):
        st = (F(0), F(3), r)
        roots.append(price(st))
        stack.append(st)
    while stack:
        st = stack.pop()
        if st in seen:
            continue
        seen.add(st)
        g = price(st)
        for nl, nh, base in ch1(*st):
            kids = [(nl, nh, base + b * half1) for b in (0, 1)]
            kid = min(kids, key=lambda c: (dep1(c, dmax) is None, dep1(c, dmax) or 0))
            if dep1(kid, dmax) is None:
                continue
            gk = price(kid)
            edges += 1
            if g is not None and gk is not None and gk > g:
                rises += 1
                big = max(big, gk - g)
            stack.append(kid)
    return edges, rises, big, roots


def endgame_entries(beta, k, dmax):
    """Over the k-game's optimal kill tree from [0, 3] (every component, the adversary's best bit), the
    endgame entries: states from which every optimal-tree descendant has at most one component, whose
    parent has a descendant that splits.  Returns {(lo, hi): set of (r, depth)}."""
    dep, ch = make_depth(beta, k), make_children(beta, k)
    half = 1 << (k - 1)

    def best(nl, nh, base):
        kids = [(nl, nh, base + b * half) for b in (0, 1)]
        return min(kids, key=lambda c: (dep(c, dmax) is None, dep(c, dmax) or 0))

    calm = {}

    def is_calm(st):
        if st not in calm:
            kids = ch(*st)
            calm[st] = len(kids) <= 1 and all(is_calm(best(*c)) for c in kids if dep(best(*c), dmax) is not None)
        return calm[st]

    out, seen = {}, set()
    stack = [(F(0), F(3), r) for r in range(1 << k)]
    while stack:
        st = stack.pop()
        if st in seen or dep(st, dmax) is None:
            continue
        seen.add(st)
        if is_calm(st):
            out.setdefault((st[0], st[1]), set()).add((st[2], dep(st, dmax)))
            continue
        stack += [best(*c) for c in ch(*st)]
    return out


def critical_residues(beta, k, dmax, r0):
    """The k-game's critical line from ([0, 3], r0): the constructor keeps the component whose best
    reply is deepest, the adversary its best bit.  Per move: (signed residue, components)."""
    dep, ch = make_depth(beta, k), make_children(beta, k)
    half, mod = 1 << (k - 1), 1 << k
    st, out = (F(0), F(3), r0), []
    while dep(st, dmax):
        kids = ch(*st)
        out.append((st[2] - mod if st[2] >= mod // 2 else st[2], len(kids)))
        best = None
        for a, b, c in kids:
            dd = [(dep((a, b, c + bit * half), dmax), bit) for bit in (0, 1)]
            dd = [x for x in dd if x[0] is not None]
            if dd:
                x, bit = min(dd)
                if best is None or x > best[0]:
                    best = (x, (a, b, c + bit * half))
        if best is None:
            break
        st = best[1]
    return out


def depth_at_integer(beta, lo, hi, n, kmax, dmax):
    """Kill depth of ([lo, hi], n mod 2^k) for k = 1..kmax: the window sitting at the integer n."""
    return [make_depth(beta, k)((lo, hi, n % (1 << k)), dmax) for k in range(1, kmax + 1)]


def window_step(beta, w, d):
    """One move of the window under parity shift d: the components, each scaled and renormalized."""
    lo, hi = w
    out = []
    for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
        a, b = max(lo, j + beta), min(hi, j + 1 - beta)
        if a <= b:
            nl, nh = F(3, 2) * a + d, F(3, 2) * b + d
            sh = math.floor(nl)
            out.append((nl - sh, nh - sh))
    return out


def holds(beta, L):
    """Single-piece periodic holds: for each primitive parity word s of length <= L and each periodic
    orbit of x -> 1.5x + s_i/2 (mod 1) inside the band, grow a tiny window around it under s repeated.
    A hold is a window cycle with one component at every move (the constructor never chooses).
    Returns ([(word, period point, hold window)], number of orbits whose window splits)."""
    found, split = [], 0
    for q in range(1, L + 1):
        for s in itertools.product((0, 1), repeat=q):
            if q > 1 and any(s == s[i:] + s[:i] for i in range(1, q) if q % i == 0):
                continue
            c = sum(F(s[i], 2) * F(3, 2) ** (q - 1 - i) for i in range(q))
            g = F(3, 2) ** q
            for mm in range(-int(g) - 2, 3):
                p = (c + mm) / (1 - g)
                if not 0 <= p < 1:
                    continue
                orbit = [p]
                for i in range(q - 1):
                    orbit.append((F(3, 2) * orbit[-1] + F(s[i], 2)) % 1)
                if not all(beta < x < 1 - beta for x in orbit):
                    continue
                w, seen, n = (p - F(1, 10 ** 6), p + F(1, 10 ** 6)), {}, 0
                while (w, n % q) not in seen and n <= 3000:
                    seen[(w, n % q)] = n
                    kids = window_step(beta, w, F(s[n % q], 2))
                    if len(kids) != 1:
                        break
                    w, n = kids[0], n + 1
                else:
                    if n <= 3000:
                        found.append(("".join(map(str, s)), p, w))
                        continue
                split += 1
    return found, split


def track_window(beta, lo, hi, k, dmax):
    """For one window, over every (k+1)-residue r: (max price d1 - d0, its r, max d1, min d0)."""
    dep0, dep1 = make_depth(beta, k), make_depth(beta, k + 1)
    best, arg, top, low = None, None, 0, None
    for r in range(1 << (k + 1)):
        d0, d1 = dep0((lo, hi, r % (1 << k)), dmax), dep1((lo, hi, r), dmax)
        if d0 is None or d1 is None:
            continue
        top, low = max(top, d1), d0 if low is None else min(low, d0)
        if best is None or d1 - d0 > best:
            best, arg = d1 - d0, r
    return best, arg, top, low


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "kill":
        print(kill_depth(F(argv[1]), int(argv[2]), int(argv[3])))
        return 0
    if argv[0] == "gaps":
        worst = int(argv[5]) if len(argv) > 5 else 0
        out = delay_gaps(F(argv[1]), int(argv[2]), int(argv[3]), int(argv[4]), worst)
        if worst:
            for g, lo, hi, r, d0, d1 in out:
                print(f"gap {g}  [{float(lo):.5f}, {float(hi):.5f}] w={float(hi - lo):.5f}  r={r:0{int(argv[2]) + 1}b}  d0={d0} d1={d1}")
        else:
            print(out)
        return 0
    if argv[0] == "mono":
        print(price_monotone(F(argv[1]), int(argv[2]), int(argv[3])))
        return 0
    if argv[0] == "path":
        for r in range(1 << (int(argv[2]) + 1)):
            p = price_path(F(argv[1]), int(argv[2]), int(argv[3]), r)
            entry = max((i for i, x in enumerate(p) if x[3] > 1), default=-1) + 1
            print(f"r={r}: prices " + " ".join(str(x[2]) for x in p) + "   comps " + "".join(str(x[3]) for x in p)
                  + f"   endgame from move {entry}: width {float(p[entry][4]):.4f}, {p[entry][0]} moves left")
        return 0
    if argv[0] == "endgame":
        out = endgame_entries(F(argv[1]), int(argv[2]), int(argv[3]))
        print(f"{len(out)} windows, {sum(len(v) for v in out.values())} (window, residue) entries")
        for (lo, hi), v in sorted(out.items(), key=lambda x: x[0][1] - x[0][0]):
            print(f"  [{lo}, {hi}] w={float(hi - lo):.4f} lo={float(lo):.4f}  depths {sorted({d for _, d in v})}  residues {sorted(r for r, _ in v)}")
        return 0
    if argv[0] == "lines":
        k = int(argv[2])
        for r0 in range(1 << k):
            line = critical_residues(F(argv[1]), k, int(argv[3]), r0)
            print(f"r0={r0}: " + " ".join(f"{x}{'*' if n > 1 else ''}" for x, n in line))
        return 0
    if argv[0] == "depthat":
        print(depth_at_integer(F(argv[1]), F(argv[2]), F(argv[3]), int(argv[4]), int(argv[5]), int(argv[6])))
        return 0
    if argv[0] == "holds":
        found, split = holds(F(argv[1]), int(argv[2]))
        for word, p, w in found:
            print(f"hold: word {word}, orbit point {p}, window [{w[0]}, {w[1]}]")
        print(f"{split} other periodic orbits split as their window grows")
        return 0
    if argv[0] == "lag":
        print(lag_costs(F(argv[1]), int(argv[2]), int(argv[3]), int(argv[4]), len(argv) > 5))
        return 0
    if argv[0] == "track":
        print(track_window(F(argv[1]), F(argv[2]), F(argv[3]), int(argv[4]), int(argv[5])))
        return 0
    if argv[0] == "depths":
        print(residue_depths(F(argv[1]), int(argv[2]), int(argv[3])))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_memoryless_depth_matches_earlier_minimax():
    # 26 at beta = 0.1229 was measured by an independent minimax on 2026-10-05 (ArcTrap docstring)
    assert kill_depth(F(1229, 10000), 1, 40) == 26


def test_two_bits_still_killed():
    assert kill_depth(F(1229, 10000), 2, 40) == 30


def test_memo_depth_matches_iterative_deepening():
    # two implementations of the same game (lru_cache per (state, D) vs one memo entry per state)
    for k in (1, 2, 3):
        dep = make_depth(F(13, 100), k)
        assert [dep((F(0), F(3), r), 40) for r in range(1 << k)] == residue_depths(F(13, 100), k, 40)


def test_below_edge_not_killed():
    # teeth: below 7/57 the constructor wins (relaxedStrategy_757), so no kill may appear within the
    # depth that kills at 0.1229 (a deeper search here grows without bound)
    assert kill_depth(F(7, 57) - F(1, 1000), 1, 26) is None


def test_stall_escape_depth_plateau_then_breaks():
    # E = image of [1.5b + 1/2, 1 - b] at the integer -2, beta = 0.13 (advKills_stall_013 checks k = 3)
    b = F(13, 100)
    E = (F(3, 2) * (F(3, 2) * b + H) - 1, F(3, 2) * (1 - b) - 1)
    assert E == (F(17, 400), F(61, 200))
    assert depth_at_integer(b, E[0], E[1], -2, 7, 45) == [9, 9, 12, 12, 12, 12, 14]


def test_critical_line_stalls_at_minus_two():
    line = critical_residues(F(13, 100), 4, 45, 5)
    assert [x for x, _ in line[4:8]] == [-2, -2, -2, -2]
    assert all(n == 2 for _, n in line[4:8])


def test_the_hold_is_word_10_on_E():
    b = F(13, 100)
    found, _ = holds(b, 6)
    assert [(w, p) for w, p, _ in found] == [("10", F(1, 5))]
    # the hold window is E (or E's cycle partner), at residue -1/5 = ...0011
    E = (F(17, 400), F(61, 200))
    assert window_step(b, window_step(b, E, H)[0], 0) == [E]
    assert depth_at_integer(b, E[0], E[1], 0, 1, 40) and (5 * 3 + 1) % 16 == 0
    assert make_depth(b, 4)((E[0], E[1], 3), 40) == 15


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
