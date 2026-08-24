#!/usr/bin/env python3
"""
Front A: exact parity reconstruction / carry machine (FRONT-A-PARITY-RECONSTRUCTION.md).

Shortcut (accelerated Syracuse) map, matching CollatzMoonshot/FrontB/Dictionary.lean:

    tstep n = n//2           if n even
            = (3n+1)//2       if n odd

Parity trace (matching FrontB.traceWord): traceWord(n,m) = [b_0,...,b_{m-1}] where
b_i = parity of tstep^[i] n (True = odd).

Word arithmetic (matching FrontB.Words):
    ones v            = number of True in v
    numer []          = 0
    numer (False::t)  = 2*numer t
    numer (True::t)   = 2*numer t + 3^(ones t)

Exact iterate identity (tstep_iterate_identity), for v = traceWord(n,m), a = ones v:
    2^m * tstep^[m](n) = 3^a * n + numer v.

Reconstruction residue R(v): the unique r < 2^m with 2^m | 3^(ones v)*r + numer v
(3^a is a unit mod 2^m).  Dictionary:  traceWord(n,m) = v  <->  n ≡ R(v) (mod 2^m),
and R(traceWord(n,m)) = n mod 2^m.

Online one-bit carry recurrence (state (r, q, p, a) for a word v of length m, where
p = 3^a, q = tstep^[m](R(v)) = (p*R(v)+numer v)/2^m):  appending bit b,
    c  = parity(q) XOR b            # next binary digit of the reconstructed start
    r' = r + c*2^m
    b=0:  q' = (q + c*p)//2,          p' = p,    a' = a
    b=1:  q' = (3*(q + c*p)+1)//2,    p' = 3*p,  a' = a+1
c is the next reconstructed output bit; q is the archimedean endpoint.

Everything is exact Python int arithmetic.  We EXHAUSTIVELY cross-check the modular R,
the online recurrence, and traceWord; then probe carry objectives on high-odd-density
words.  No claim about Collatz is drawn from finite data.
"""

import sys
from itertools import product


# ---------------------------------------------------------------------------
# core definitions (mirror the Lean)
# ---------------------------------------------------------------------------

def tstep(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def trace_word(n, m):
    v = []
    x = n
    for _ in range(m):
        v.append(x % 2 == 1)
        x = tstep(x)
    return v


def ones(v):
    return sum(1 for b in v if b)


def numer(v):
    # numer (False::t) = 2*numer t ; numer (True::t) = 2*numer t + 3^(ones t)
    val = 0
    # process right-to-left so ones(t) is available
    ones_t = 0
    for b in reversed(v):
        if b:
            val = 2 * val + 3 ** ones_t
            ones_t += 1
        else:
            val = 2 * val
    return val


def R_modular(v):
    """Unique r < 2^m with 2^m | 3^(ones v)*r + numer v."""
    m = len(v)
    mod = 1 << m
    a = ones(v)
    inv = pow(pow(3, a, mod), -1, mod)  # 3^a is a unit mod 2^m
    return (-numer(v) * inv) % mod


# ---------------------------------------------------------------------------
# online carry recurrence
# ---------------------------------------------------------------------------

def online_states(v):
    """Return the list of (r,q,p,a) states after each prefix of v (length 0..m),
    plus the list of reconstructed output bits c_0..c_{m-1}."""
    r, q, p, a = 0, 0, 1, 0  # empty word: R=0, q=tstep^0(0)=0, p=3^0=1
    states = [(r, q, p, a)]
    cbits = []
    for b in v:
        c = (q % 2) ^ (1 if b else 0)
        r = r + c * (1 << a_len(states))  # 2^(current length)
        base = q + c * p
        if b:
            q = (3 * base + 1) // 2
            p = 3 * p
            a = a + 1
        else:
            q = base // 2
        cbits.append(c)
        states.append((r, q, p, a))
    return states, cbits


def a_len(states):
    # current word length = number of appended letters so far = len(states)-1
    return len(states) - 1


# ---------------------------------------------------------------------------
# exhaustive cross-checks
# ---------------------------------------------------------------------------

def check_dictionary(depth):
    """For every word v of each length m<=depth: R(v) reproduces v as its trace, and
    for every residue r<2^m: R(trace(r,m)) = r.  This proves the bijection exactly."""
    for m in range(0, depth + 1):
        mod = 1 << m
        seen = {}
        for bits in product([False, True], repeat=m):
            v = list(bits)
            r = R_modular(v)
            assert 0 <= r < mod, (v, r)
            # r realizes v
            assert trace_word(r, m) == v, ("R->trace", v, r, trace_word(r, m))
            assert r not in seen, ("R not injective", v, seen.get(r))
            seen[r] = v
        # bijection: all 2^m residues hit
        assert len(seen) == mod, (m, len(seen), mod)
        # R(trace(r,m)) = r for all residues
        for r in range(mod):
            assert R_modular(trace_word(r, m)) == r, ("trace->R", m, r)
    return True


def check_online(depth):
    """Online recurrence agrees with modular R, with the endpoint identity, and the
    reconstructed bits are the binary digits of R."""
    for m in range(0, depth + 1):
        for bits in product([False, True], repeat=m):
            v = list(bits)
            states, cbits = online_states(v)
            # final state
            r, q, p, a = states[-1]
            assert r == R_modular(v), ("online R", v, r, R_modular(v))
            assert p == 3 ** a
            assert a == ones(v)
            # endpoint identity: 2^m * tstep^[m](r) = 3^a r + numer v, and q = that endpoint
            endpoint = tstep_iter(r, m)
            assert (1 << m) * endpoint == p * r + numer(v), ("identity", v)
            assert q == endpoint, ("q endpoint", v, q, endpoint)
            # reconstructed bits are binary digits of r (low bit first)
            val = sum((c << i) for i, c in enumerate(cbits))
            assert val == r, ("bits", v, val, r)
            # prefix nesting: each prefix state's r is r truncated mod 2^k
            for k in range(m + 1):
                rk = states[k][0]
                assert rk == r % (1 << k), ("nesting", v, k, rk, r % (1 << k))
    return True


def tstep_iter(n, m):
    for _ in range(m):
        n = tstep(n)
    return n


# ---------------------------------------------------------------------------
# carry / odd-density probes
# ---------------------------------------------------------------------------

def density_probe(depth):
    """Among words at depth `depth`, examine odd density vs. the reconstructed output.
    Critical shortcut odd density is log2/log3 ~ 0.6309.  We look at whether high-density
    words force nonzero high output bits (i.e. large reconstructed start), and track the
    normalized endpoint q/3^a as a candidate Lyapunov/height coordinate."""
    import math
    crit = math.log(2) / math.log(3)
    mod = 1 << depth
    best_delay = None      # word maximizing index of last nonzero output bit? (want small start)
    max_norm = -1.0
    min_norm = float("inf")
    hi_density = []
    for bits in product([False, True], repeat=depth):
        v = list(bits)
        a = ones(v)
        dens = a / depth
        r = R_modular(v)
        q = tstep_iter(r, depth)
        norm = q / (3 ** a) if a else float(q)
        if norm > max_norm:
            max_norm = norm
        if norm < min_norm:
            min_norm = norm
        if dens > crit:
            hi_density.append((dens, r, q, norm, v))
    hi_density.sort(reverse=True)
    return crit, max_norm, min_norm, hi_density[:8]


def carry_boundedness_probe(max_depth):
    """The key structural question: is q/3^a (normalized endpoint of the canonical
    representative) bounded independent of depth, or can it be driven arbitrarily large
    by choosing the parity word?  For a genuine natural n it equals n (once output bits
    stabilize).  We track, per depth, the max and min normalized endpoint over ALL words,
    and the max over high-odd-density words only."""
    import math
    crit = math.log(2) / math.log(3)
    rows = []
    for m in range(1, max_depth + 1):
        mx = -1.0
        mn = float("inf")
        mx_hi = -1.0
        mx_hi_word = None
        for bits in product([False, True], repeat=m):
            v = list(bits)
            a = ones(v)
            r = R_modular(v)
            q = tstep_iter(r, m)
            norm = q / (3 ** a) if a else float(q)
            mx = max(mx, norm)
            mn = min(mn, norm)
            if a / m > crit and norm > mx_hi:
                mx_hi = norm
                mx_hi_word = v
        rows.append((m, mn, mx, mx_hi, mx_hi_word))
    return crit, rows


def bounded_memory_potential_probe(max_depth):
    """Strength audit: try to defeat any potential that depends only on a bounded parity
    suffix.  For window w, group words by their last-w bits; a bounded-suffix potential
    would predict the normalized endpoint (or its increment) from the suffix alone.  We
    measure the SPREAD of q/3^a within each suffix class: if it grows with depth, no
    bounded-suffix statistic can be a depth-independent Lyapunov function."""
    rows = []
    for w in (2, 3, 4):
        depth_rows = []
        for m in range(w, max_depth + 1):
            classes = {}
            for bits in product([False, True], repeat=m):
                v = list(bits)
                a = ones(v)
                r = R_modular(v)
                q = tstep_iter(r, m)
                norm = q / (3 ** a) if a else float(q)
                key = tuple(v[-w:])
                lo, hi = classes.get(key, (norm, norm))
                classes[key] = (min(lo, norm), max(hi, norm))
            max_spread = max(hi - lo for lo, hi in classes.values())
            depth_rows.append((m, max_spread))
        rows.append((w, depth_rows))
    return rows


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    print(f"# Parity reconstruction / carry machine — exhaustive to depth {depth}")
    print()

    print("## Exact cross-checks")
    d_dict = min(depth, 14)
    print(f"  dictionary bijection (R<->trace, all residues), depth<= {d_dict} ...", end="", flush=True)
    check_dictionary(d_dict)
    print(" OK")
    print(f"  online recurrence == modular R, endpoint identity, nesting, depth<= {d_dict} ...", end="", flush=True)
    check_online(d_dict)
    print(" OK")
    print()

    print("## Odd-density / carry probe")
    crit, mx, mn, hi = density_probe(depth)
    print(f"  critical shortcut odd density log2/log3 = {crit:.6f}")
    print(f"  over all 2^{depth} words: normalized endpoint q/3^a in [{mn:.4f}, {mx:.2f}]")
    print(f"  top high-density words (dens, r, q, q/3^a):")
    for dens, r, q, norm, v in hi[:6]:
        print(f"    dens={dens:.4f} r={r} q={q} q/3^a={norm:.4f} word={''.join('1' if b else '0' for b in v)}")
    print()

    print("## Normalized-endpoint growth vs depth (is q/3^a bounded?)")
    crit, rows = carry_boundedness_probe(min(depth, 16))
    print("  depth   min(q/3^a)   max(q/3^a)   max over hi-density")
    for m, mn, mx, mxhi, _w in rows:
        hh = f"{mxhi:.3f}" if mxhi >= 0 else "   -"
        print(f"   {m:3d}    {mn:9.4f}   {mx:10.3f}   {hh}")
    print()

    print("## Bounded-suffix potential spread (strength audit)")
    print("  window   depth   max spread of q/3^a within suffix class")
    prows = bounded_memory_potential_probe(min(depth, 16))
    for w, drows in prows:
        for m, spread in drows[-4:]:
            print(f"    w={w}     {m:3d}     {spread:.3f}")
    print()
    print("# done")


if __name__ == "__main__" and not (len(sys.argv) > 1 and sys.argv[1] == "deep"):
    main()


# ---------------------------------------------------------------------------
# deeper probes (strength audit + invariant search), appended lap 2
# ---------------------------------------------------------------------------

def output_bits_of_high_density(max_depth, dens_floor=None):
    """Positivity condition = reconstructed output bits c_m eventually zero.  For a genuine
    natural n < 2^depth, R(v)=n so the HIGH output bits are zero.  We ask the load-bearing
    question: can a word sustain odd density >= critical AND have its top output bit zero
    (i.e. r < 2^{m-1}, so the word is realized by a *small* start)?  We tabulate, per depth,
    the maximum odd count among words whose reconstructed start r < 2^{m-1} (top bit 0),
    versus the max odd count overall.  If sustaining density forces the top bits nonzero,
    the two diverge -- an empirical signature that critical density is incompatible with
    'output eventually zero' (the positivity/divergence tension)."""
    import math
    crit = math.log(2) / math.log(3)   # critical shortcut odd density
    rows = []
    for m in range(2, max_depth + 1):
        half = 1 << (m - 1)
        max_ones_all = 0
        max_ones_smallstart = 0     # r < 2^{m-1}: top output bit zero
        for bits in product([False, True], repeat=m):
            v = list(bits)
            a = ones(v)
            if a > max_ones_all:
                max_ones_all = a
            r = R_modular(v)
            if r < half and a > max_ones_smallstart:
                max_ones_smallstart = a
        rows.append((m, max_ones_all / m, max_ones_smallstart / m, crit))
    return rows


def bounded_memory_nogo(max_depth, window=3):
    """Rigorous no-go signature for bounded-suffix Lyapunov potentials: find, at each depth,
    two words sharing their last-`window` bits but with q/3^a differing by a large margin.
    Such a pair defeats ANY potential Phi(last w bits): it cannot separate the two endpoints.
    Preserve the extremal adversarial pair."""
    best = None
    for m in range(window + 2, max_depth + 1):
        classes = {}
        for bits in product([False, True], repeat=m):
            v = list(bits)
            a = ones(v)
            r = R_modular(v)
            q = tstep_iter(r, m)
            norm = q / (3 ** a) if a else float(q)
            key = tuple(v[-window:])
            classes.setdefault(key, []).append((norm, v))
        for key, lst in classes.items():
            lst.sort()
            lo, hi = lst[0], lst[-1]
            spread = hi[0] - lo[0]
            if best is None or spread > best[0]:
                best = (spread, m, key, lo, hi)
    return best


def sharper_invariant_search(max_depth):
    """Hunt for an inequality sharper than q < 3^a.  Candidates keyed on the reconstruction:
    (i) is q + (2^m - r) related to 3^a?   (ii) does 3^a - q (the gap) admit a lower bound
    growing with anything?  We compute, per depth, the min over ALL words of the gap
    (3^a - q) and of the normalized gap (3^a - q)/3^a, and where they are attained."""
    rows = []
    for m in range(1, max_depth + 1):
        min_gap = None
        min_gap_word = None
        # also test candidate identity: 2^m*(3^a - q) == 3^a*(2^m - r) - numer  (should be exact)
        identity_ok = True
        for bits in product([False, True], repeat=m):
            v = list(bits)
            a = ones(v)
            p = 3 ** a
            r = R_modular(v)
            q = tstep_iter(r, m)
            gap = p - q
            if (1 << m) * gap != p * ((1 << m) - r) - numer(v):
                identity_ok = False
            if min_gap is None or gap < min_gap:
                min_gap = gap
                min_gap_word = (a, r, q, v)
        rows.append((m, min_gap, identity_ok, min_gap_word))
    return rows


def deeper_main():
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    print(f"# Deeper probes to depth {depth}")
    print()
    print("## Positivity tension: max odd density, all words vs. small-start (top output bit 0)")
    print("  depth   max dens (all)   max dens (r<2^{m-1})   critical")
    for m, da, ds, crit in output_bits_of_high_density(min(depth, 18)):
        print(f"   {m:3d}     {da:.4f}          {ds:.4f}            {crit:.4f}")
    print()
    print("## Bounded-suffix Lyapunov no-go (extremal adversarial pair, window=3)")
    best = bounded_memory_nogo(min(depth, 16), window=3)
    if best:
        spread, m, key, lo, hi = best
        w = lambda v: ''.join('1' if b else '0' for b in v)
        print(f"  depth {m}: last-3 bits {w(list(key))} shared, q/3^a spread = {spread:.4f}")
        print(f"    low  q/3^a={lo[0]:.4f} word={w(lo[1])}")
        print(f"    high q/3^a={hi[0]:.4f} word={w(hi[1])}")
        print("  => no potential depending only on a bounded parity suffix separates these;")
        print("     any carry Lyapunov function must read unbounded (archimedean) state.")
    print()
    print("## Sharper-invariant search: min gap (3^a - q) and exact gap identity")
    print("  depth   min(3^a - q)   gap-identity-holds   attained-at (a,r,q)")
    for m, g, ok, w in sharper_invariant_search(min(depth, 16)):
        a, r, q, word = w
        print(f"   {m:3d}     {g:6d}         {ok}              a={a} r={r} q={q}")
    print()
    print("# deeper done")


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "deep":
    deeper_main()
