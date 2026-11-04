#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Numeric probe for the joint law of (|a|, F_n(a) mod 3^n), a ~ Geom(2)^n (Tao 2019 Remark 1.16).

Exactness.  Rows P[s] = P(|a| = s, F_n = Y) are exact up to float rounding: a_i <= s, so nothing is
truncated in a fixed row.  Only the unconditioned law uses a tail cutoff (a_i <= 60, lost mass
<= n 2^-60).  Given |a| = s the tuple is uniform on the C(s-1, n-1) compositions of s.

Parts.
 A  known answers: Tao's tables at n = 1, 2; sum of rows vs Lemma 1.12 DP; sup char vs the repo's
    twisted_charfn.py values.
 B  unconditioned Osc_{m,n} from (1.24): must decay in m (Prop 1.14, Remark 1.15).
 C  Osc_{m,n}(F | |a| = s), s = 2n + k sqrt(2n) and the rich ray s = 3n, with a random-map null:
    same coarse law mod 3^m, atoms hashed uniformly into the 3^(n-m) lifts.
 D  character sums: max_{3 !| xi} |E[chi 1(|a|=s)]| <= max_theta |E[chi e^{i theta |a|}]| <= E prod|f|
    (Tao (7.5)), tested exactly.  This inequality is the whole of the twist step.
 E  coarse correlation of s with F mod 3^k: TV(law(F mod 3^k | s), Syrac(3^k)) as n grows.
 F  renewal node: R(u) -> 2/log(4/3) along theta = log2 3, with the rational control theta = 3/2.
 G  direct probe: L1(Pass_x(Unif odd [y, 2y]), Pass_x(log-uniform reference)), for a scan of y, with
    two-sample null and the small-y control (not yet stabilised).
 H  (`affine_mixing.py H`) the pullback mechanism of Inselmann arXiv:2402.03276 Lemma 2.16, which uses no
    mixing: offset size, preimage multiplicity, amplification of rare Terras events, and stage word
    frequencies at C = 1..6."""
import math
import sys
import time

import numpy as np

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 13
SAMPLES = int(sys.argv[2]) if len(sys.argv) > 2 else 3_000_000
rng = np.random.default_rng(20261104)


def p(*args):
    print(*args, flush=True)


def inv2_powers(mod, amax):
    inv2 = (mod + 1) // 2
    out, cur = [], 1
    for _ in range(amax):
        cur = cur * inv2 % mod
        out.append(cur)
    return out


def osc(law, n, m):
    """Osc_{m,n} of (1.24): sum_Y |law(Y) - 3^(m-n) law(Y mod 3^m)|."""
    Q = 3**m
    idx = np.arange(3**n, dtype=np.int64) % Q
    coarse = np.bincount(idx, weights=law, minlength=Q)
    return float(np.abs(law - coarse[idx] / 3 ** (n - m)).sum())


def uncond_dp(nmax, amax=60):
    """Unconditioned law at every n, Tao Lemma 1.12 with a_i <= amax."""
    laws = {0: np.array([1.0])}
    for n in range(nmax):
        mod = 3 ** (n + 1)
        Y = np.arange(3**n, dtype=np.int64)
        base = (3 * Y + 1) % mod
        new = np.zeros(mod)
        for a, ipow in enumerate(inv2_powers(mod, amax), start=1):
            np.add.at(new, base * ipow % mod, laws[n] * 0.5**a)
        laws[n + 1] = new
    return laws


def joint_dp(nmax, smax):
    """Yield (n, rows) with rows[s] = P(|a| = s, F_n = Y), n <= s <= smax."""
    rows = {0: np.array([1.0])}
    yield 0, rows
    for n in range(nmax):
        mod = 3 ** (n + 1)
        Y = np.arange(3**n, dtype=np.int64)
        base = (3 * Y + 1) % mod
        pw = inv2_powers(mod, smax)
        new = {}
        for s, row in rows.items():
            for a in range(1, smax - s + 1):
                t = s + a
                if t not in new:
                    new[t] = np.zeros(mod)
                new[t][base * pw[a - 1] % mod] += row * 0.5**a
        rows = new
        yield n + 1, rows


def null_osc(coarse_counts, n, m):
    """Random-map null: K_c atoms of class c hashed uniformly into the 3^(n-m) lifts."""
    cells = 3 ** (n - m)
    K = coarse_counts.sum()
    if cells == 1:
        return 0.0
    # one multinomial draw per coarse class
    if coarse_counts.size * cells <= 40_000_000:
        counts = rng.multinomial(coarse_counts, np.full(cells, 1.0 / cells))
        return float(np.abs(counts - coarse_counts[:, None] / cells).sum() / K)
    return float("nan")


def part_A(laws):
    p("== A. Known answers ==")
    p("n=1: law on Z/3 =", np.round(laws[1], 12), " Tao: 0, 1/3, 2/3")
    tao2 = np.array([0, 8, 16, 0, 11, 4, 0, 2, 22]) / 63
    p("n=2: max |law - Tao table| =", f"{np.abs(laws[2] - tao2).max():.2e}", " (table has denominator 63)")
    p("Sup char, repo twisted_charfn.py theta=0 values: n=5 0.129, n=8 0.061, n=10 0.038, n=11 0.032")
    for n in sorted({x for x in (5, 8, 10, 11, 12, NMAX) if x <= NMAX}):
        f = np.fft.fft(laws[n])
        mask = np.arange(3**n) % 3 != 0
        p(f"  n={n:2d}  sup_(3 !| xi) |E chi(F_n)| = {np.abs(f[mask]).max():.4f}")


def part_B(laws):
    p("\n== B. Control: unconditioned Osc_{m,n}, Prop 1.14 predicts decay in m, uniform in n >= m ==")
    ms = list(range(1, NMAX))
    p("  n\\m " + " ".join(f"{m:6d}" for m in ms))
    for n in range(4, NMAX + 1):
        p(f"  {n:3d} " + " ".join(f"{osc(laws[n], n, m):6.3f}" if m < n else " " * 6 for m in ms))


def part_C_D_E(laws, smax):
    p(f"\n== C. Conditioned Osc_(m,n)(F | |a|=s) with random-map null, smax = {smax} ==")
    p("  'meas' is exact.  'null' is one draw of the random-map model with the same coarse law.")
    p("  atoms/cell = C(s-1,n-1)/3^n.  Below about 1 the law cannot be flat at any scale: the row has too few atoms.")
    p("  meas below null at fine scales means the true map spreads more evenly than a random map.")
    d_rows = []
    tilt = {}
    for n, rows in joint_dp(NMAX, smax):
        if n < 4:
            continue
        t0 = time.time()
        # E: coarse correlation
        sd = math.sqrt(2 * n)
        for k in (2, 3, 4):
            if k >= n:
                continue
            ref = np.bincount(np.arange(3**n, dtype=np.int64) % 3**k, weights=laws[n], minlength=3**k)
            for off in (-1, 0, 1):
                s = int(round(2 * n + off * sd))
                if s in rows:
                    q = np.bincount(np.arange(3**n, dtype=np.int64) % 3**k, weights=rows[s], minlength=3**k)
                    q /= q.sum()
                    tilt[(n, k, off)] = float(np.abs(q - ref).sum())
        if n < 8:
            continue
        p(f"-- n = {n}")
        targets = [(f"2n{k:+d}sd", int(round(2 * n + k * sd))) for k in (-1, 0, 1, 2)] + [("2.5n", 5 * n // 2), ("3n", 3 * n)]
        ms = [m for m in (1, 2, 3, 4, 6, 8, 10, 12) if m < n]
        p("  s-label    s  P(|a|=s)  atoms/cell  " + " ".join(f"  m={m:<2d}meas/null " for m in ms))
        for lab, s in targets:
            if s not in rows or s < n:
                continue
            ps = rows[s].sum()
            law = rows[s] / ps
            atoms = math.comb(s - 1, n - 1)
            cells = []
            for m in ms:
                Q = 3**m
                coarse = np.bincount(np.arange(3**n, dtype=np.int64) % Q, weights=law, minlength=Q)
                cnt = np.round(coarse * atoms).astype(np.int64)
                nu = null_osc(cnt, n, m)
                cells.append(f"{osc(law, n, m):6.3f}/{nu:6.3f}")
            ch = np.abs(np.fft.fft(law)[np.arange(3**n) % 3 != 0]).max()
            floor = math.sqrt(math.log(3.0**n) / atoms)
            p(f"  {lab:7s} {s:4d}  {ps:8.2e}  {atoms / 3**n:10.2f}  " + " ".join(f"{c:15s}" for c in cells) + f"  sup|E[chi|s]| {ch:.4f} (random-phase floor {floor:.4f})")
        # joint vs unconditioned
        ms2 = ms
        js = []
        for m in ms2:
            tot = 0.0
            Q = 3**m
            idx = np.arange(3**n, dtype=np.int64) % Q
            for s, row in rows.items():
                c = np.bincount(idx, weights=row, minlength=Q)
                tot += float(np.abs(row - c[idx] / 3 ** (n - m)).sum())
            js.append(tot)
        p("  JointOsc (sum over s): " + " ".join(f"{x:6.3f}" for x in js) + f"   lost mass s>{smax}: {1 - sum(r.sum() for r in rows.values()):.2e}")
        p("  uncond   Osc         : " + " ".join(f"{osc(laws[n], n, m):6.3f}" for m in ms2))
        # D: character sums on rows
        if n <= 12 and n % 2 == 0:
            d_rows.append(part_D(n, rows))
        p(f"  [{time.time() - t0:.0f}s]")
    p("\n== E. Coarse correlation: TV(law(F mod 3^k | s), Syrac(3^k)), full L1, s = 2n + off*sd ==")
    p("   real and non-zero; a conserved quantity would keep this bounded below as n grows.")
    for k in (2, 3, 4):
        for off in (-1, 0, 1):
            vals = [f"n={n}:{tilt[(n, k, off)]:.3f}" for n in range(6, NMAX + 1) if (n, k, off) in tilt]
            p(f"  k={k} off={off:+d}  " + " ".join(vals))


def f_pair_abs(n, xi, x, b):
    """|f(x, b)| of Tao (7.4), x in Z/3^n given as int."""
    mod = 3**n
    t = 0j
    for a in range(1, b):
        t += np.exp(-2j * np.pi * (xi * x * (pow(2, a, mod) + 3) % mod) / mod)
    return abs(t) / (b - 1)


def damping(n, xi, bmax=40):
    """E prod_j |f(3^(2j) 2^(-b[1,j+1]), b_(j+1))|, n even, Tao (7.5), truncated at b <= bmax (lost
    mass reported); backward DP over (j, partial sum mod 2*3^n is not needed, the sum itself is)."""
    mod = 3**n
    inv2 = (mod + 1) // 2
    pairs = n // 2
    Lmax = pairs * bmax
    Q = np.ones(Lmax + 1)
    pb = np.array([0, 0] + [(b - 1) / 2.0**b for b in range(2, bmax + 1)])
    for j in reversed(range(pairs)):
        newQ = np.zeros(Lmax + 1)
        # only l in the reachable range matter
        for l in range(2 * j, min(Lmax, 8 * j + 60) + 1):
            acc = 0.0
            for b in range(2, min(bmax, Lmax - l) + 1):
                if pb[b] < 1e-9:
                    continue
                x = pow(3, 2 * j, mod) * pow(inv2, l + b, mod) % mod
                acc += pb[b] * f_pair_abs(n, xi, x, b) * Q[l + b]
            newQ[l] = acc
        Q = newQ
    return Q[0]


def part_D(n, rows):
    ss = sorted(rows)
    mat = np.array([np.fft.fft(rows[s]) for s in ss])  # s x xi
    mask = np.arange(3**n) % 3 != 0
    fixed = np.abs(mat[:, mask]).max(axis=0)
    idx = np.flatnonzero(mask)
    worst = idx[np.argsort(-fixed)[:3]]
    thetas = np.linspace(0, 2 * np.pi, 180, endpoint=False)
    phase = np.exp(1j * np.outer(thetas, np.array(ss)))
    p(f"  D. n={n}: inequality check, xi: max_s |E chi 1(|a|=s)| <= max_theta |E chi e^(i theta|a|)| <= E prod|f|  (last term truncated to a lower estimate, so a violation would still be visible)")
    xis = [int(x) for x in worst] + [1, 2, 4, 5]
    for xi in xis:
        col = mat[:, xi]
        a = np.abs(col).max()
        b = np.abs(phase @ col).max()
        p(f"     xi={xi:7d}  {a:.5f}  <=  {b:.5f}  <=  {damping(n, xi):.5f}")
    uni = np.abs(mat[:, mask]).max()
    twist = 0.0
    if n <= 10:
        twist = np.abs(phase @ mat[:, mask]).max()
    p(f"     sup over xi: fixed-s numerator {uni:.5f}; sup_(xi,theta) twist {twist:.5f} (n<=10; repo table n=10: 0.048); untwisted {np.abs(np.fft.fft(sum(rows.values()))[mask]).max():.5f}")
    return None


def part_F():
    p("\n== F. Renewal node: R(u) = sum_k E psi(2^(|a_k| - k theta - D + u)), psi(t) = 2t on [1,2) ==")
    p("   limit 2/((2-theta) log 2) as D -> infinity iff theta irrational.  Printed: R normalised to limit 1, min and max over u in [0,1).")
    lf = np.concatenate([[0.0], np.cumsum(np.log(np.arange(1, 20001, dtype=float)))])
    ln2 = math.log(2)
    for name, theta in (("log2 3", math.log2(3)), ("3/2 control", 1.5), ("8/5 control", 1.6)):
        for D in (20, 40, 80, 160, 320, 640, 1280):
            drift = 2 - theta
            kc = D / drift
            w = int(8 * math.sqrt(2 * kc) / drift + 20)
            ks = np.arange(max(1, int(kc) - w), int(kc) + w + 1)
            vals = []
            for u in np.linspace(0, 1, 97)[:-1]:
                ss = np.ceil(ks * theta + D - u - 1e-12).astype(int)
                t = ss - ks * theta - D + u
                ok = ss >= ks
                logp = lf[ss - 1] - lf[ks - 1] - lf[ss - ks] - ss * ln2
                vals.append(float((2 * 2.0**t * np.exp(logp) * ok).sum()))
            vals = np.array(vals) * drift * ln2 / 2
            p(f"   theta={name:12s} D={D:5d}  min {vals.min():.5f}  max {vals.max():.5f}")


def syr_pass(N, x):
    """First passage location below x for the odd array N (uint64); returns locations; drops overflow."""
    out = np.zeros(N.size, dtype=np.uint64)
    active = np.arange(N.size)
    v = N.copy()
    dropped = 0
    for _ in range(100000):
        done = v <= x
        out[active[done]] = v[done]
        active = active[~done]
        v = v[~done]
        if v.size == 0:
            break
        big = v >= (1 << 62)
        if big.any():
            dropped += int(big.sum())
            out[active[big]] = 0
            active = active[~big]
            v = v[~big]
        w = 3 * v + 1
        low = w & (~w + np.uint64(1))
        tz = np.round(np.log2(low.astype(np.float64))).astype(np.uint64)
        v = w >> tz
    return out, dropped


def part_G(x_bits=12, samples=SAMPLES):
    x = np.uint64(1 << x_bits)
    K = 1 << (x_bits - 1)
    p(f"\n== G. Direct probe: Pass_x, x = 2^{x_bits}, {samples} samples per law, full L1 ==")
    p("   columns: L1 on all odd locations; L1 of location mod 81; L1 of bit-length of location.")

    def stats(loc):
        loc = loc[loc > 0]
        full = np.bincount(((loc - np.uint64(1)) // np.uint64(2)).astype(np.int64), minlength=K) / loc.size
        m81 = np.bincount((loc % np.uint64(81)).astype(np.int64), minlength=81) / loc.size
        bits = np.bincount(np.floor(np.log2(loc.astype(np.float64))).astype(np.int64), minlength=x_bits + 1) / loc.size
        return full, m81, bits

    def dist(a, b):
        return tuple(float(np.abs(u - v).sum()) for u, v in zip(a, b))

    def log_law(lo, hi, n):
        # 53-bit floats leave the low bits of large N zero; refill the low 16 bits at random so that
        # N mod 2^k stays uniform (the relative shift is below 2^-30 for N >= 2^46).
        z = np.exp(rng.uniform(np.log(float(lo)), np.log(float(hi)), n)).astype(np.uint64)
        big = z >= np.uint64(1 << 46)
        z[big] = (z[big] >> np.uint64(16) << np.uint64(16)) | rng.integers(0, 1 << 16, int(big.sum()), dtype=np.uint64)
        return z | np.uint64(1)

    def unif_law(y, n):
        return rng.integers(int(y), 2 * int(y), n, dtype=np.uint64) | np.uint64(1)

    # reference far from x, so that it is itself stabilised: log-uniform on 2^(x_bits+20) .. 2^(x_bits+36)
    lo, hi = 2.0**(x_bits + 20), 2.0**(x_bits + 36)
    ref1 = stats(syr_pass(log_law(lo, hi, samples), x)[0])
    ref2 = stats(syr_pass(log_law(lo, hi, samples), x)[0])
    p("   null: reference vs independent reference: %.4f %.4f %.4f" % dist(ref1, ref2))
    ref3 = stats(syr_pass(log_law(2.0 ** (x_bits + 3), 2.0 ** (x_bits + 12), samples), x)[0])
    p("   control, near log window 2^(x_bits+3) .. 2^(x_bits+12) vs reference: %.4f %.4f %.4f" % dist(ref1, ref3))
    p("   'dropped' counts orbits passing 2^62 (excluded): a selection effect of at most that fraction of samples.")
    p("   y/x = 2^d, d:")
    ds = [0.25, 0.5, 1, 1.5, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 24, 28, 32, 36, 40, 44]
    ds += [20 + f for f in (0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)]
    for d in sorted(ds):
        y = 2.0 ** (x_bits + d)
        loc, dropped = syr_pass(unif_law(y, samples), x)
        p(f"   d={d:6.2f}  " + "%.4f %.4f %.4f" % dist(stats(loc), ref1) + (f"  dropped {dropped}" if dropped else ""))
    for j in (20, 25, 30, 35):
        y = 3.0**j
        loc, dropped = syr_pass(unif_law(y, samples), x)
        p(f"   y=3^{j}, log2(y/x)={math.log2(y) - x_bits:6.2f}  " + "%.4f %.4f %.4f" % dist(stats(loc), ref1) + (f"  dropped {dropped}" if dropped else ""))


def tstep_arrays(m, steps):
    """T^steps on the uint64 array m, T(n) = n/2 or (3n+1)/2; returns (iterate, odd-letter count)."""
    v = m.copy()
    a = np.zeros(m.size, dtype=np.int64)
    for _ in range(steps):
        odd = (v & np.uint64(1)).astype(bool)
        a += odd
        v = np.where(odd, (3 * v + np.uint64(1)) >> np.uint64(1), v >> np.uint64(1))
    return v, a


def ones_dev(v):
    """(#odd letters among the first size(v) letters) / size(v) - 1/2, for the uint64 array v."""
    size = np.floor(np.log2(np.maximum(v, np.uint64(1)).astype(np.float64))).astype(np.int64) + 1
    cnt = np.zeros(v.size, dtype=np.int64)
    w = v.copy()
    for t in range(int(size.max())):
        live = t < size
        odd = (w & np.uint64(1)).astype(bool)
        cnt += odd & live
        w = np.where(odd, (3 * w + np.uint64(1)) >> np.uint64(1), w >> np.uint64(1))
    return np.abs(cnt / size - 0.5), size


def part_H():
    p("\n== H. The pullback mechanism (Inselmann arXiv:2402.03276 Lemma 2.16), no mixing used ==")
    p("   T^k m = 3^a m / 2^k + offset.  Given M = T^k m and a, m lies in an interval of length (offset+1) 2^k / 3^a.")
    p("   So the law of M has density at most about k max(offset) / range against uniform, hence")
    p("   P_m(T^k m in B) <= k 2^(eps k) 3^(-D k/2)-style bounds for any B of power-saving density X^(-D).")
    for k, n in ((24, None), (32, 8_000_000), (40, 8_000_000)):
        lo = 1 << (k - 1)
        if n is None:
            m = np.arange(lo, 2 * lo, dtype=np.uint64)
        else:
            m = rng.integers(lo, 2 * lo, n, dtype=np.uint64)
        M, a = tstep_arrays(m, k)
        offset = M.astype(np.float64) - m.astype(np.float64) * np.exp(a * math.log(3) - k * math.log(2))
        q = np.quantile(np.abs(offset), [0.5, 0.999, 1.0])
        p(f" k={k}: offset = T^k m - 3^a m/2^k: median {q[0]:.1f}, 99.9% {q[1]:.1f}, max {q[2]:.1f};  log2(max)/k = {math.log2(max(q[2], 1)) / k:.3f}")
        p(f"   a/k: mean {a.mean() / k:.4f}, min {a.min() / k:.3f}, max {a.max() / k:.3f};  M/2^(k log2 sqrt3): log2 M / k mean {np.log2(M.astype(np.float64)).mean() / k:.4f}")
        if n is None:
            vals, counts = np.unique(M, return_counts=True)
            order = np.sort(counts)[::-1]
            p(f"   max preimages of one M: {order[0]}  (reference (2/sqrt3)^k = {(2 / math.sqrt(3)) ** k:.1f});  distinct M: {vals.size};  mass of the top 0.1% of M: {order[: max(1, vals.size // 1000)].sum() / m.size:.4f}")
        dev_M, size_M = ones_dev(M)
        # reference: uniform integers with the same size distribution
        ref = (np.uint64(1) << (size_M - 1).astype(np.uint64)) + (rng.random(M.size) * (2.0 ** (size_M - 1))).astype(np.uint64)
        dev_R, _ = ones_dev(ref)
        for d in (0.1, 0.15, 0.2, 0.25, 0.3):
            pm, pr = (dev_M > d).mean(), (dev_R > d).mean()
            p(f"   B = letters of M off by > {d:.2f} of size(M): P_m(T^k m in B) = {pm:.3e}, P_uniform(B) = {pr:.3e}, amplification {pm / pr if pr else float('nan'):.2f}")
        # control: a set the law of M really does avoid, showing the law is not uniform
        p(f"   control, B = multiples of 3 (density 1/3): P_m(T^k m in B) = {(M % np.uint64(3) == 0).mean():.2e}")
    p("\n Word frequency over one stage, first C k letters of uniform k-bit starts.")
    p(" Fraction of starts with |#(11)/(C k) - 1/4| > 0.02, 500 starts each; C=5,6 are the above-threshold controls.")
    pyrng = np.random.default_rng(7)
    for k in (100, 400, 1600):
        row = []
        for C in (1, 2, 3, 4, 5, 6):
            bad = 0
            L = C * k
            for _ in range(500):
                n = (1 << (k - 1)) + int.from_bytes(pyrng.bytes(k // 8 + 1), "little") % (1 << (k - 1))
                prev, c = 0, 0
                for _ in range(L):
                    b = n & 1
                    c += prev & b
                    prev = b
                    n = (3 * n + 1) >> 1 if b else n >> 1
                bad += abs(c / L - 0.25) > 0.02
            row.append(f"C={C}: {bad / 500:.3f}")
        p(f"  k={k:5d}  " + "  ".join(row))
    p("\n Window chain of section 7: t_(j+1) = t_j + size(T^(t_j) m).  Mean of t_J / k over 40 k-bit starts; prediction sum_(i<J) theta^i.")
    th = math.log2(3) / 2
    for k in (1000, 4000):
        ts = np.zeros(10)
        for _ in range(40):
            n = (1 << (k - 1)) + int.from_bytes(pyrng.bytes(k // 8 + 1), "little") % (1 << (k - 1))
            t = 0
            for J in range(1, 10):
                size = n.bit_length()
                for _ in range(size):
                    n = (3 * n + 1) >> 1 if n & 1 else n >> 1
                t += size
                ts[J] += t / k / 40
        p(f"  k={k}: " + "  ".join(f"J={J}: {ts[J]:.3f} (pred {(1 - th**J) / (1 - th):.3f})" for J in (1, 2, 4, 6, 8, 9)))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "H":
        part_H()
        sys.exit(0)
    t0 = time.time()
    laws = uncond_dp(NMAX)
    part_A(laws)
    part_B(laws)
    part_F()
    part_G()
    part_C_D_E(laws, 3 * NMAX + 3)
    p(f"\nTotal {time.time() - t0:.0f}s")
