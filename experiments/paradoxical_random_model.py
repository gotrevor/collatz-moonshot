#!/usr/bin/env python3
"""Null models for the paradoxical census at a fixed (m, a) - EXACT aggregate evaluation.

Population: front-normalized words v (first letter odd) of length m with exactly a odd letters,
N = numer(v), M = 2^m, D = M - 3^a > 0, delta = D/M.  A word admits an acyclic paradoxical start
iff its least realizing start n0 > 2 satisfies D*n0 < N (see paradoxical.py).

Two null models for "where does the least start n0 fall":
  continuous proxy   p_cont(v) = min(1, N/(D*M))              (n0 uniform on [0, M))
  odd-residue null   p_odd(v)  = (2/M) * clamp(floor((N-1-D)/(2D)), 0, M/2)
                                                              (n0 uniform on the odd {3,5,..,M+1})
Expected admitting-word counts  R = sum_v p_cont(v),  R_odd = sum_v p_odd(v).

R needs only S_N = sum_v N(v) once clipping is inactive (max_v N < D*M), and S_N has an exact
closed form plus an O(m*a) integer dynamic program (both from the 2026-09-13 campaign brief):
    S_N = C(m-1,a-1)*3^(a-1) + sum_{k=0}^{a-2} C(m-1,k)*(2^m - 2*3^k)
    DP over prefixes (length j, k odd letters): append even: (count, sum) unchanged;
                     append odd: count' = count, sum' = 3*sum + 2^j*count   [numer(v++[T]) = 3N + 2^j]
Binomial form: with U~Bin(m-1,1/2), V~Bin(m-1,3/4),
    S_N/M^2 = (Pr(U<=a-2) - Pr(V<=a-2))/2 + Pr(V=a-1)/4  ->  1/2  (a/m -> log2/log3 in (1/2,3/4)),
so R = (S_N/M^2)/delta ~ 1/(2*delta) on near-critical subsequences.  p_odd needs per-word N, so
R_odd is enumerated when the population is small enough; always 0 < p_cont - p_odd < (3+1/D)/M.

Usage:
  paradoxical_random_model.py M A             exact: DP + closed form (+ enumeration if cheap)
  paradoxical_random_model.py M A --enum      force per-word enumeration (R, R_odd, clipping)
  paradoxical_random_model.py M A --mc K      Monte Carlo estimate of R (legacy check)
  paradoxical_random_model.py --table         the eight near-critical pairs, exact
  paradoxical_random_model.py --selftest      DP vs closed form vs enumeration, small lengths

Results 2026-09-13 (exact rationals, rounded): R = 5.0802 (8,5) 10.8619 (27,17) 18.6925 (46,29)
6.3608 (54,34) 42.3517 (65,41) 7.9097 (73,46) 10.1238 (92,58) 13.8792 (111,70); clipping
inactive at all eight; R_odd = 615/128 = 4.8047 at (8,5).  Census: 4 admitting words at (8,5),
19 at (27,17) (paradoxical_block_distribution.py).
"""
import sys, os, time, random
from fractions import Fraction
from math import comb
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast

NEAR_CRITICAL = [(8, 5), (27, 17), (46, 29), (54, 34), (65, 41), (73, 46), (92, 58), (111, 70)]


def words(m, a):
    """All front-normalized words of length m with a odd letters."""
    for odd_pos in combinations(range(1, m), a - 1):
        v = [False] * m; v[0] = True
        for i in odd_pos:
            v[i] = True
        yield v


def closed_form_Nmax(m, a):
    """Largest numer over front-normalized words: T F^(m-a) T^(a-1) (odd letters back-loaded after the first)."""
    return 2 ** (m - a + 1) * (3 ** (a - 1) - 2 ** (a - 1)) + 3 ** (a - 1)


def closed_form_SN(m, a):
    return comb(m - 1, a - 1) * 3 ** (a - 1) + sum(comb(m - 1, k) * (2 ** m - 2 * 3 ** k)
                                                    for k in range(0, a - 1))


def dp_aggregates(m, a):
    """(count, S_N, N_max, N_min) over front-normalized words of length m with a odd letters."""
    cnt = {1: 1}; sm = {1: 1}; mx = {1: 1}; mn = {1: 1}      # prefix [T]: numer 1
    for j in range(1, m):                                    # append a letter to length-j prefixes
        p = 1 << j
        ncnt, nsm, nmx, nmn = {}, {}, {}, {}
        for k in cnt:
            # even letter: numer unchanged
            ncnt[k] = ncnt.get(k, 0) + cnt[k]; nsm[k] = nsm.get(k, 0) + sm[k]
            nmx[k] = max(nmx.get(k, 0), mx[k]); nmn[k] = min(nmn.get(k, mn[k]), mn[k])
            # odd letter: numer -> 3*numer + 2^j
            if k + 1 <= a:
                ncnt[k + 1] = ncnt.get(k + 1, 0) + cnt[k]
                nsm[k + 1] = nsm.get(k + 1, 0) + 3 * sm[k] + p * cnt[k]
                nmx[k + 1] = max(nmx.get(k + 1, 0), 3 * mx[k] + p)
                nmn[k + 1] = min(nmn.get(k + 1, 3 * mn[k] + p), 3 * mn[k] + p)
        cnt, sm, mx, mn = ncnt, nsm, nmx, nmn
    return cnt.get(a, 0), sm.get(a, 0), mx.get(a, 0), mn.get(a, 0)


def binomial_form(m, a):
    """S_N/M^2 via the Bin(m-1,1/2) / Bin(m-1,3/4) identity (exact Fraction)."""
    pu = Fraction(sum(comb(m - 1, k) for k in range(0, a - 1)), 2 ** (m - 1))
    pv = Fraction(sum(comb(m - 1, k) * 3 ** k for k in range(0, a - 1)), 4 ** (m - 1))
    pv_eq = Fraction(comb(m - 1, a - 1) * 3 ** (a - 1), 4 ** (m - 1))
    return (pu - pv) / 2 + pv_eq / 4


def enumerate_aggregates(m, a):
    """Per-word pass: (count, S_N, N_max, N_min, sum min(N, D*M), sum of odd-null counts)."""
    M = 1 << m; D = M - 3 ** a; DM = D * M; half = M // 2
    cnt = 0; S = 0; mx = 0; mn = None; clip = 0; odd = 0
    for v in words(m, a):
        N = numer_fast(v); cnt += 1; S += N
        if N > mx: mx = N
        if mn is None or N < mn: mn = N
        clip += min(N, DM)
        c = (N - 1 - D) // (2 * D)
        odd += min(max(c, 0), half)
    return cnt, S, mx, mn or 0, clip, odd


def report(m, a, enum=False, cheap_limit=6_000_000):
    M = 1 << m; D = M - 3 ** a
    assert D > 0, "need 3^a < 2^m"
    delta = Fraction(D, M)
    t0 = time.time()
    cnt, S, mx, mn = dp_aggregates(m, a)
    S_cf = closed_form_SN(m, a)
    assert cnt == comb(m - 1, a - 1) and S == S_cf and mx == closed_form_Nmax(m, a), ("DP vs closed form", cnt, S, S_cf)
    assert Fraction(S, M * M) == binomial_form(m, a), "binomial form"
    clipping = mx >= D * M
    R = Fraction(S, D * M)
    print(f"(m,a)=({m},{a}) delta={float(delta):.5f} words={cnt} S_N={S} N_max={mx} N_min={mn} "
          f"clipping={'ACTIVE' if clipping else 'inactive'} (N_max/(D*M)={mx/(D*M):.3e})")
    print(f"  R = S_N/(D*M) = {float(R):.9f}   S_N/M^2 = {float(Fraction(S, M*M)):.6f}   "
          f"1/(2 delta) = {float(1/(2*delta)):.4f}   R*2delta = {float(R*2*delta):.4f}"
          + ("   [R is an UPPER bound: clipping active, sum min(1,.) needs enumeration]" if clipping else ""))
    if enum or cnt <= cheap_limit:
        ecnt, eS, emx, emn, clip, odd = enumerate_aggregates(m, a)
        assert (ecnt, eS, emx, emn) == (cnt, S, mx, mn), ("enumeration vs DP", (ecnt, eS, emx, emn), (cnt, S, mx, mn))
        R_exact = Fraction(clip, D * M); R_odd = Fraction(2 * odd, M)
        print(f"  enumeration agrees (count, S_N, N_max, N_min).  R_exact = sum min(1,N/DM) = {float(R_exact):.9f}"
              f"  R_odd = {R_odd} = {float(R_odd):.9f}  R - R_odd = {float(R_exact - R_odd):.6f}"
              f" (bound (3+1/D)*words/M = {float((3 + Fraction(1, D)) * cnt / M):.6f}) [{time.time()-t0:.0f}s]")
        return R, R_odd
    print(f"  (population {cnt} > {cheap_limit}: R_odd not enumerated; |R - R_odd| < {float((3 + Fraction(1, D)) * cnt / M):.3e}) [{time.time()-t0:.0f}s]")
    return R, None


def monte_carlo(m, a, samples):
    M = 1 << m; D = M - 3 ** a; total = comb(m - 1, a - 1)
    random.seed(1); s = 0.0; t0 = time.time()
    for _ in range(samples):
        v = [False] * m; v[0] = True
        for i in random.sample(range(1, m), a - 1):
            v[i] = True
        s += min(1.0, numer_fast(v) / (D * M))
    print(f"(m,a)=({m},{a}) MC {samples}: R ≈ {s / samples * total:.3f}  (exact {float(Fraction(closed_form_SN(m, a), D * M)):.3f}) [{time.time()-t0:.0f}s]")


def selftest(mmax=16):
    n = 0
    for m in range(2, mmax + 1):
        for a in range(1, m + 1):
            if 3 ** a >= 2 ** m:
                continue
            cnt, S, mx, mn = dp_aggregates(m, a)
            ecnt, eS, emx, emn, clip, odd = enumerate_aggregates(m, a)
            assert (cnt, S, mx, mn) == (ecnt, eS, emx, emn), (m, a)
            assert S == closed_form_SN(m, a), (m, a, "closed form")
            assert Fraction(S, 4 ** m) == binomial_form(m, a), (m, a, "binomial")
            assert mn == 3 ** a - 2 ** a, (m, a, "N_min = 3^a - 2^a (odd letters front-loaded)")
            assert mx == closed_form_Nmax(m, a), (m, a, "N_max closed form")
            n += 1
    print(f"selftest: DP == enumeration == closed form == binomial form on {n} pairs (m <= {mmax}); N_min = 3^a-2^a, N_max = 2^(m-a+1)(3^(a-1)-2^(a-1))+3^(a-1)")
    for m, a in NEAR_CRITICAL:
        cnt, S, mx, mn = dp_aggregates(m, a)
        assert S == closed_form_SN(m, a) and cnt == comb(m - 1, a - 1) and mx == closed_form_Nmax(m, a)
    print("selftest: DP == closed form at the eight near-critical pairs")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args == ["--selftest"]:
        selftest()
    elif args == ["--table"]:
        for m, a in NEAR_CRITICAL:
            report(m, a)
    elif len(args) >= 3 and args[2] == "--mc":
        monte_carlo(int(args[0]), int(args[1]), int(args[3]) if len(args) > 3 else 200_000)
    else:
        report(int(args[0]), int(args[1]), enum="--enum" in args)
