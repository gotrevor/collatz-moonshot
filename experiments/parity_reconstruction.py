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
from math import comb


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
    by choosing the parity word?  For a fixed natural start, the reconstruction residue
    R_m -- not q/3^a -- eventually stabilizes to n.  We track, per depth, the max and min
    normalized endpoint over ALL words, and the max over high-odd-density words only."""
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
    """Strength audit: test whether a bounded parity suffix determines or uniformly
    approximates the normalized endpoint.  For window w, group words by their last-w bits
    and measure the spread of q/3^a in each class.  Large spread refutes endpoint prediction
    from the suffix alone.  It does *not* rule out every finite-state Lyapunov certificate,
    which may use aggregate transition inequalities rather than reconstructing q/3^a."""
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


if __name__ == "__main__" and not (len(sys.argv) > 1 and sys.argv[1] in ("deep", "first-crossing", "coalescence")):
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


def bounded_suffix_collision_probe(max_depth, window=3):
    """Find two words sharing their last-`window` bits but with q/3^a differing by a
    large margin.  This is an exact collision witness for suffix-only endpoint prediction,
    not a universal no-go theorem for finite-state or suffix-state Lyapunov arguments."""
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
    print("## Bounded-suffix endpoint collision (extremal pair, window=3)")
    best = bounded_suffix_collision_probe(min(depth, 16), window=3)
    if best:
        spread, m, key, lo, hi = best
        w = lambda v: ''.join('1' if b else '0' for b in v)
        print(f"  depth {m}: last-3 bits {w(list(key))} shared, q/3^a spread = {spread:.4f}")
        print(f"    low  q/3^a={lo[0]:.4f} word={w(lo[1])}")
        print(f"    high q/3^a={hi[0]:.4f} word={w(hi[1])}")
        print("  => q/3^a is neither determined nor uniformly approximated by this suffix;")
        print("     this does not exclude aggregate finite-state Lyapunov certificates.")
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


# ---------------------------------------------------------------------------
# First-crossing geometry, not unrestricted paradoxical excursions.
# Exact integer DP; decimal output is a uniform-residue NULL MODEL, not a count
# of actual failures and not an independence assertion.
# ---------------------------------------------------------------------------

def first_crossing_sharp_numerator(odd_count):
    """Maximum numerator: delay odd letter i to floor(log_2(3^i)).

    bit_length computes that floor exactly, including i=0.  No floating logs
    decide word membership or the maximizing positions.
    """
    return sum(3**(odd_count-1-i) * (1 << ((3**i).bit_length()-1))
               for i in range(odd_count))


def first_crossing_dp(max_depth):
    """Return exact count, sum numerator, and max numerator for each crossing length.

    Alive states have never crossed.  Aggregate by odd count because the
    affine numerator update only uses that count and the current depth.
    """
    if max_depth < 1:
        raise ValueError("max_depth must be positive")
    alive = {0: (1, 0, 0)}
    powers = [3**a for a in range(max_depth+1)]
    rows = []
    for m in range(1, max_depth+1):
        old_modulus, modulus = 1 << (m-1), 1 << m
        next_alive = {}
        crossed = {}
        for a, (count, total, largest) in alive.items():
            for b in (0, 1):
                aa = a+b
                tt = 3*total+old_modulus*count if b else total
                uu = 3*largest+old_modulus if b else largest
                target = crossed if powers[aa] < modulus else next_alive
                old_count, old_total, old_largest = target.get(aa, (0, 0, 0))
                target[aa] = (old_count+count, old_total+tt, max(old_largest, uu))
        alive = next_alive
        for a, (count, total, largest) in crossed.items():
            assert m == powers[a].bit_length()
            if m > 1:
                # Rotate a zero-total discrepancy walk after a minimum, then append 0.
                # Every rotation class has <= m-1 members, including periodic words.
                all_final_even = comb(m-1, a)
                assert all_final_even <= (m-1)*count and count <= all_final_even
                assert count*(powers[a]-2**a) <= total
            assert 3*largest <= a*powers[a]
            assert largest == first_crossing_sharp_numerator(a)
            gap = modulus-powers[a]
            rows.append({"length": m, "ones": a, "count": count,
                         "numerator_sum": total, "numerator_max": largest,
                         "gap": gap, "modulus": modulus,
                         "null_numerator": total, "null_denominator": gap*modulus})
    return rows


def check_first_crossing(depth=16):
    """Independent exhaustive words vs DP, sharp envelope, and actual least starts.

    Only the tested finite depths are certified.  Least starts exclude 0 and 1.
    Each word's numerator uses the existing right-to-left implementation, not DP.
    """
    rows = {row["length"]: row for row in first_crossing_dp(depth)}
    actual_counts = {}
    failures = []
    checked = 0
    for m in range(1, depth+1):
        count = total = largest = 0
        for bits in product((False, True), repeat=m):
            if 3**ones(bits) >= 1 << m:
                continue
            if any(3**ones(bits[:j]) < 1 << j for j in range(1, m)):
                continue
            count += 1
            checked += 1
            n = numer(bits)
            total += n
            largest = max(largest, n)
            a, modulus = ones(bits), 1 << m
            assert 3*n <= a*3**a
            r = R_modular(bits)
            least = r if r >= 2 else r+modulus
            assert trace_word(least, m) == list(bits)
            gap = modulus-3**a
            if gap*least <= n:
                failures.append((m, least, bits))
        if count:
            row = rows[m]
            assert (count, total, largest) == (
                row["count"], row["numerator_sum"], row["numerator_max"])
            actual_counts[m] = count
        else:
            assert m not in rows
    return {"depth": depth, "words_checked": checked,
            "counts": actual_counts, "actual_failures": failures}


def prefix_supercritical(bits):
    """All proper prefixes have coefficient at least one, including the empty one."""
    a = 0
    for j, bit in enumerate(bits):
        if 3**a < 1 << j:
            return False
        a += bit
    return True


def check_adjacent_swaps(depth=12):
    """Exact independent controls for the Lean swap identities and legal moves.

    The first-crossing family is closed under moving an odd letter left (01->10).
    Moving it right (10->01) requires the extra prefix margin 2^(d+1)<=3^i.
    Neither fact orders the reconstructed residues as ordinary integers.
    """
    checked = legal_first_crossing = 0
    for m in range(2, depth+1):
        modulus = 1 << m
        for bits in product((False, True), repeat=m):
            for d in range(m-1):
                if bits[d:d+2] != (True, False):
                    continue
                swapped = bits[:d]+(False, True)+bits[d+2:]
                i, tail_ones = ones(bits[:d]), ones(bits[d+2:])
                x, y = R_modular(bits), R_modular(swapped)
                assert numer(swapped) == numer(bits)+(1 << d)*3**tail_ones
                assert (3**(i+1)*(y-x)+(1 << d)) % modulus == 0
                # Only the prefix of length d+1 changes its odd count.
                if prefix_supercritical(swapped):
                    assert prefix_supercritical(bits)
                if prefix_supercritical(bits):
                    assert prefix_supercritical(swapped) == (1 << (d+1) <= 3**i)
                    if 3**ones(bits) < modulus and prefix_supercritical(swapped):
                        legal_first_crossing += 1
                checked += 1
    witness = (trace_word(95, 8), trace_word(175, 8))
    assert all(prefix_supercritical(v) and 3**ones(v) < 256 for v in witness)
    assert tuple(numer(v) for v in witness) == (211, 227)
    assert 95 < 175  # refutes numerator-antitone residue order
    return {"depth": depth, "swaps_checked": checked,
            "first_crossing_swaps": legal_first_crossing,
            "antitone_counterexample": {"length": 8, "starts": [95, 175],
                                         "numerators": [211, 227]}}


def first_crossing_main():
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    controls = check_first_crossing(min(depth, 16))
    print("# First coefficient crossing: exact geometry and uniform-residue null baseline")
    print(controls)
    print(check_adjacent_swaps(min(depth, 12)))
    print("m a word_count continuous_null_baseline sharp_start_ceiling")
    selected = {27, 46, 65, 100, 200, 500, 501, depth}
    for row in first_crossing_dp(depth):
        if row["length"] <= 16 or row["length"] in selected:
            baseline = row["null_numerator"]/row["null_denominator"]
            ceiling = row["numerator_max"]/row["gap"]
            print(row["length"], row["ones"], row["count"],
                  f"{baseline:.12g}", f"{ceiling:.12g}")
    print("Baseline is sum_v numer(v)/(D*2^m), NOT an observed admitting-word count.")
    print("No random-residue assumption or infinite-depth exclusion is proved.")


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "first-crossing":
    first_crossing_main()


# ---------------------------------------------------------------------------
# coalescence statistics (2026-09-19 Fable handoff, KB leaf
# collatz-fable-strategy-2026-09-19.md).  For each n >= 2:
#   sigma(n) = first m with tstep^[m](n) < n              (shortcut stopping time)
#   c(n)     = first m with tstep^[m](n) in V(n), where V(n) is the forward-closed
#              union of the orbits of every start s < n     (earliest coalescence)
#   S(n)     = L(n) - 2 A(n), signed score at the first hit of 1; a BALANCED merger
#              to some s < n exists iff some s < n has S(s) = S(n).
# c(n) <= sigma(n) always (the descent target is itself a smaller start).
# Every quantity is computed by exact walking, never from the finite claim's limit.
# ---------------------------------------------------------------------------

def coalescence_scan(limit):
    """Return dict n -> (c, sigma, S) for 1 <= n <= limit, plus the state table."""
    la = {1: (0, 0)}            # state -> (L, A): steps and odd steps to first hit of 1
    out = {1: (0, 0, 0)}        # c(1), sigma(1) are conventional zeros
    for n in range(2, limit + 1):
        path = []               # (state, odd?) not yet in la
        x, m, c, sigma = n, 0, None, None
        while x not in la:
            if sigma is None and x < n:
                sigma = m       # cannot happen: x < n implies x in la
            path.append((x, x % 2 == 1))
            x = tstep(x)
            m += 1
        c = m
        # sigma: first step whose value is < n; x itself may be it
        y, k = n, 0
        while y >= n:
            y = tstep(y)
            k += 1
        sigma = k
        L, A = la[x]
        for st, odd in reversed(path):
            L += 1
            A += 1 if odd else 0
            la[st] = (L, A)
        Ln, An = la[n]
        out[n] = (c, sigma, Ln - 2 * An)
    return out, la


def coalescence_main():
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    out, _ = coalescence_scan(limit)
    print(f"# Coalescence vs descent, exact, 2 <= n <= {limit}")
    scores_seen = {out[1][2]}
    no_gain_odd = []            # odd n with c(n) == sigma(n)
    no_balanced_odd = []        # odd n with no smaller start of equal score
    worst_c = (0.0, None)       # max c(n)/log2(n)
    worst_sigma = (0.0, None)
    gain_hist = {}
    from math import log2
    for n in range(2, limit + 1):
        c, sigma, S = out[n]
        if n % 2 == 1:
            if c == sigma:
                no_gain_odd.append(n)
            if S not in scores_seen:
                no_balanced_odd.append(n)
        scores_seen.add(S)
        g = sigma - c
        gain_hist[g] = gain_hist.get(g, 0) + 1
        rc, rs = c / log2(n), sigma / log2(n)
        if rc > worst_c[0]:
            worst_c = (rc, n)
        if rs > worst_sigma[0]:
            worst_sigma = (rs, n)
    odd_total = limit // 2
    print(f"odd n with c(n) == sigma(n) (coalescence buys nothing): {len(no_gain_odd)} of {odd_total}")
    print(f"  first few: {no_gain_odd[:20]}")
    print(f"odd n with NO balanced partner below them: {len(no_balanced_odd)} of {odd_total}")
    print(f"  first few: {no_balanced_odd[:20]}")
    print(f"max c(n)/log2 n     = {worst_c[0]:.4f} at n={worst_c[1]}  (c={out[worst_c[1]][0]})")
    print(f"max sigma(n)/log2 n = {worst_sigma[0]:.4f} at n={worst_sigma[1]}  (sigma={out[worst_sigma[1]][1]})")
    print("gain sigma-c histogram (gain: count), gains 0..12 then max:")
    print("  " + ", ".join(f"{g}: {gain_hist.get(g, 0)}" for g in range(13)) + f"; max gain {max(gain_hist)}")
    for n in (3, 7, 15, 27, 97, 871, 6171, 77031):
        if n <= limit:
            c, sigma, S = out[n]
            print(f"  n={n}: c={c} sigma={sigma} S={S}")
    print("Finite scan; no claim about all n is drawn from it.")


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "coalescence":
    coalescence_main()
