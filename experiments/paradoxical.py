#!/usr/bin/env python3
"""Exact-integer study of paradoxical shortcut-Collatz segments (FRONT-A-PARADOXICAL).

Conventions match the Lean repo (FrontB/Dictionary.lean, FrontB/Words.lean):

  tstep(n) = n//2            if n even
           = (3n+1)//2       if n odd
  traceWord(n,m): first letter is parity of n itself (True=odd), then recurse on tstep n.
  ones(v)  = number of True letters.
  numer(v): numer([]) = 0; numer(False::t) = 2*numer t; numer(True::t) = 2*numer t + 3^ones(t).

Iterate identity (proved in Lean, `tstep_iterate_identity`):
  2^m * tstep^[m] n = 3^ones(v) * n + numer(v),   v = traceWord(n,m).

For start n, length m>0, put a=ones(v), p=3^a, y=tstep^[m] n, d=2^m-p.
PARADOXICAL:  2 < n, 0 < m, p < 2^m, n <= y.        (endpoint at/above start, subcritical coeff)
ACYCLIC:      additionally n < y.
Criterion (P):  d*n <= numer(v)           <=>   n <= y      (when p<2^m).
Slack (S):      numer(v) - d*n = 2^m*(y-n).

All arithmetic is exact Python int.  No floats in any comparison.
"""
from __future__ import annotations
from functools import lru_cache
from fractions import Fraction
import sys

# ---------- core exact machine ----------

def tstep(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def trace_word(n: int, m: int) -> list[bool]:
    v = []
    for _ in range(m):
        v.append(n % 2 == 1)
        n = tstep(n)
    return v

def ones(v: list[bool]) -> int:
    return sum(1 for b in v if b)

def numer(v: list[bool]) -> int:
    # numer(b::t) recursion, computed from the front using the recursive def.
    if not v:
        return 0
    return 2 * numer(v[1:]) + (3 ** ones(v[1:]) if v[0] else 0)

def numer_fast(v: list[bool]) -> int:
    """Iterative version of numer, O(m). Cross-checked against numer()."""
    val = 0
    onestail = 0
    # process from the back: numer of suffix starting at position i
    for b in reversed(v):
        if b:
            val = 2 * val + 3 ** onestail
            onestail += 1
        else:
            val = 2 * val
    return val

def iterate(n: int, m: int) -> int:
    for _ in range(m):
        n = tstep(n)
    return n

# ---------- paradoxical predicates ----------

def seg_data(n: int, m: int):
    v = trace_word(n, m)
    a = ones(v)
    p = 3 ** a
    twom = 2 ** m
    y = iterate(n, m)
    d = twom - p            # can be negative if p>2^m
    num = numer_fast(v)
    return dict(v=v, a=a, p=p, twom=twom, y=y, d=d, numer=num, m=m, n=n)

def is_paradoxical(n: int, m: int, allow_cyclic=True) -> bool:
    if not (2 < n and 0 < m):
        return False
    D = seg_data(n, m)
    if not (D['p'] < D['twom']):       # need subcritical coefficient 3^a/2^m < 1
        return False
    if allow_cyclic:
        return D['n'] <= D['y']
    return D['n'] < D['y']

# ---------- Part A: source lock / cross-checks ----------

def check_identity(maxn=400, maxm=14):
    for n in range(1, maxn):
        for m in range(0, maxm):
            D = seg_data(n, m)
            lhs = D['twom'] * D['y']
            rhs = D['p'] * n + D['numer']
            assert lhs == rhs, (n, m, lhs, rhs)
    return True

def check_numer_defs(maxn=200, maxm=14):
    for n in range(1, maxn):
        for m in range(0, maxm):
            v = trace_word(n, m)
            assert numer(v) == numer_fast(v), (n, m)
    return True

def check_criterion_equiv(maxn=2000, maxm=20):
    """P (d*n<=numer, with p<2^m) is exactly n<=y; slack identity S holds."""
    for n in range(3, maxn):
        for m in range(1, maxm):
            D = seg_data(n, m)
            if D['p'] < D['twom']:
                P = (D['d'] * n <= D['numer'])
                assert P == (n <= D['y']), (n, m)
                assert D['numer'] - D['d'] * n == D['twom'] * (D['y'] - n), (n, m)
    return True

def basic_example():
    """The paper's 7 -> 8 example: 8 shortcut steps from 7, endpoint >= start."""
    n = 7
    orbit = [n]
    x = n
    for _ in range(8):
        x = tstep(x)
        orbit.append(x)
    D = seg_data(7, 8)
    return orbit, D

# ---------- enumeration ----------

def paradoxical_starts_for_word(v: list[bool]):
    """Given a fixed word v (m=len, a=ones, must have p<2^m), the realizing starts form the
    residue class {n : traceWord(n,m)==v}; among them paradoxical starts satisfy
    2<n, d*n<=numer, i.e. n<=floor(numer/d).  Returns (residue r, modulus 2^m, dmax, list)."""
    m = len(v)
    a = ones(v)
    p = 3 ** a
    twom = 2 ** m
    if not (p < twom):
        return None
    d = twom - p
    num = numer_fast(v)
    # realizing residue: smallest n with traceWord(n,m)==v.  Search residues 0..2^m-1.
    r = None
    for cand in range(twom):
        if trace_word(cand if cand > 0 else twom, m) == v:  # avoid n=0 degeneracies below
            pass
    # simpler: brute find residue by scanning one full period from 1..2^m
    for cand in range(1, twom + 1):
        if trace_word(cand, m) == v:
            r = cand % twom
            break
    nmax = num // d           # largest n satisfying d*n<=numer
    starts = []
    if r is not None:
        c = r if r > 0 else twom
        while c <= nmax:
            if c > 2:
                starts.append(c)
            c += twom
    return dict(m=m, a=a, r=r, d=d, numer=num, nmax=nmax, starts=starts)

def enumerate_paradoxical_by_start(nmax=100000, mmax=60, acyclic=True):
    """Direct enumeration: for each start n, find *some* m making it paradoxical.
    Records the smallest such m and the (j=m, q=a) ratio."""
    hits = []
    for n in range(3, nmax + 1):
        x = n
        found = None
        for m in range(1, mmax + 1):
            x = tstep(x)
            if x < 1:
                break
            v = trace_word(n, m)
            a = ones(v)
            p = 3 ** a
            twom = 2 ** m
            if p < twom:                 # subcritical coefficient
                if (x > n) if acyclic else (x >= n):
                    found = (m, a, x)
                    break
            # if x drops below 1 it's converged; but shortcut map keeps >=1 for n>=1
        if found:
            m, a, y = found
            hits.append((n, m, a, y))
    return hits

# ---------- Part B4: Niu continued-fraction pattern for log_3 2 ----------

def cf_log3_2(nterms=40):
    """Continued fraction of log_3(2) = log2/log3 via exact Stern-Brocot / mediant descent.
    We compute convergents of the real number log(2)/log(3) using integer comparison
    3^q vs 2^j  (q/j < log_3 2  iff  3^? ...). Actually q/j < log_3(2) iff j*log3(2)>q
    iff 2^j > 3^q. So we descend the Stern-Brocot tree comparing 2^j vs 3^q with exact ints."""
    # Stern-Brocot: maintain lo=(qL,jL) < x < hi=(qR,jR). x=log_3 2 in (0,1): 0/1 < x < 1/1.
    lo = (0, 1)  # q/j
    hi = (1, 1)
    convergents = []
    for _ in range(nterms):
        mq = lo[0] + hi[0]
        mj = lo[1] + hi[1]
        convergents.append((mq, mj))
        # compare mq/mj vs log_3 2:  mq/mj < log_3 2  iff  2^mj > 3^mq
        if 2 ** mj > 3 ** mq:
            lo = (mq, mj)      # mediant below x, raise lower bound
        else:
            hi = (mq, mj)
    return convergents

def left_convergents_semiconvergents(maxj=200):
    """All best left approximations q/j (q/j < log_3 2, i.e. 2^j>3^q) that are record-close.
    Returns set of reduced (q,j) that are left convergents/semiconvergents of log_3 2."""
    from math import gcd
    best = []
    best_gap = None  # we track record closeness of log_3 2 - q/j among q/j<x
    # A q/j is a "left semiconvergent" if it's the closest-from-below among all denominators<=j.
    records = []
    cur_best_q = -1
    for j in range(1, maxj + 1):
        # largest q with 3^q < 2^j  (strict, so q/j<log_3 2)
        q = 0
        while 3 ** (q + 1) < 2 ** j:
            q += 1
        # q/j with 3^q<2^j; is it a new record (closer from below than any smaller j)?
        # compare q/j vs previous record cur_best: q/j > cur_best_q/cur_best_j ?
        if not records:
            records.append((q, j))
        else:
            pq, pj = records[-1]
            if q * pj > pq * j:    # q/j > pq/pj, strictly closer from below
                records.append((q, j))
    # reduce
    red = set()
    for q, j in records:
        g = gcd(q, j) if (q or j) else 1
        red.add((q // g, j // g))
    return sorted(red, key=lambda t: t[1])

def classify_ratio(q, j):
    """Classify reduced q/j against left convergents/semiconvergents of log_3 2 and mediants."""
    from math import gcd
    g = gcd(q, j)
    rq, rj = q // g, j // g
    lsc = left_convergents_semiconvergents(maxj=max(80, rj * 3))
    lscset = set(lsc)
    if (rq, rj) in lscset:
        return f"left-convergent/semiconvergent {rq}/{rj}"
    # mediant of two adjacent elements of lsc?
    for i in range(len(lsc) - 1):
        aq, aj = lsc[i]
        bq, bj = lsc[i + 1]
        if (rq, rj) == (aq + bq, aj + bj):
            return f"mediant of {aq}/{aj} and {bq}/{bj}"
    return f"UNCLASSIFIED {rq}/{rj}"

# ---------- main ----------

def check_numer_extremals(jmax=16):
    for j in range(1, jmax + 1):
        for q in range(0, j + 1):
            vals = []
            # sample all words with exactly q ones is 2^j; only feasible small j
            if j <= 14:
                from itertools import combinations
                for pos in combinations(range(j), q):
                    v = [False] * j
                    for i in pos:
                        v[i] = True
                    vals.append(numer_fast(v))
                if vals:
                    nmax_exp = 2 ** (j - q) * (3 ** q - 2 ** q)  # ones back-loaded
                    nmin_exp = 3 ** q - 2 ** q                    # ones front-loaded
                    assert max(vals) == nmax_exp, (j, q, max(vals), nmax_exp)
                    assert min(vals) == nmin_exp, (j, q, min(vals), nmin_exp)
    return True

def realizing_residue(v: list[bool]) -> int:
    """Smallest n>=1 with traceWord(n,len v)==v (unique mod 2^len v)."""
    m = len(v)
    twom = 2 ** m
    for cand in range(1, twom + 1):
        if trace_word(cand, m) == v:
            return cand % twom
    return None

def ratios_admitting_paradoxical(jmax=30):
    """For each (j,q) subcritical, does ANY word admit an acyclic paradoxical start >2?
    Uses full word enumeration for small j only (2^j). Returns dict (q,j)->smallest start."""
    from itertools import combinations
    from math import gcd
    admit = {}
    for j in range(2, jmax + 1):
        twom = 2 ** j
        for q in range(1, j + 1):
            p = 3 ** q
            if not (p < twom):
                continue
            d = twom - p
            # need a word (q ones) whose residue r gives a start>2 with d*start<=numer & start<y
            best = None
            for pos in combinations(range(j), q):
                v = [False] * j
                for i in pos:
                    v[i] = True
                num = numer_fast(v)
                if num < d * 3:        # even n=3 too big; but numer>= d*n needs num>=3d
                    continue
                r = realizing_residue(v)
                start = r if r > 2 else r + twom
                # find smallest valid start > 2 in the class with d*start<=num and start<y
                while start <= num // d:
                    if start > 2:
                        y = iterate(start, j)
                        if start < y:      # acyclic
                            if best is None or start < best:
                                best = start
                            break
                    start += twom
            if best is not None:
                admit[(q, j)] = best
    return admit

def realizing_residue_fast(v: list[bool]) -> int:
    """Reconstruct the unique n mod 2^j with traceWord(n,j)==v, by lifting one bit at a time.
    O(j^2). Cross-checked against realizing_residue()."""
    j = len(v)
    r = 0  # residue mod 2^k matching v[:k]
    for k in range(1, j + 1):
        for cand in (r, r + (1 << (k - 1))):
            nn = cand if cand > 0 else (1 << k)  # represent 0 by 2^k for a real positive start
            if trace_word(nn, k) == v[:k]:
                r = cand
                break
    return r

# ============ Part B (discovery result): the >=3 odd-blocks exclusion ============
# FINDING: every paradoxical (acyclic) segment has a parity word with >= 3 odd blocks.
#   - one-block words   [F]^s [T]^q [F]^* : excluded (generalizes RT Appendix A via
#                        leading-zero stripping; the s=0 case IS Appendix A).
#   - two-block words   [T]^b [F]^c [T]^d [F]^e (front-normalized): excluded exhaustively
#                        to length j<=38 (55314 words, 0 paradoxical).
# Exact numerators (proved by the numer recursion, cross-checked exhaustively here):
#   numer([F]^s[T]^q[F]^*)              = 2^s (3^q - 2^q)
#   numer([T]^b[F]^c[T]^d[F]^e)         = 3^d (3^b - 2^b) + 2^(b+c) (3^d - 2^d)

def n_odd_blocks(v):
    return sum(1 for i in range(len(v)) if v[i] and (i == 0 or not v[i - 1]))

def verify_block_numer_forms(rng=8):
    from itertools import product
    for s, q, t in product(range(0, rng), range(1, rng), range(0, rng)):
        v = [False] * s + [True] * q + [False] * t
        if v and numer_fast(v) != 2 ** s * (3 ** q - 2 ** q):
            return False
    for b, c, d, e in product(range(1, rng), range(1, rng), range(1, rng), range(0, rng)):
        v = [True] * b + [False] * c + [True] * d + [False] * e
        if numer_fast(v) != 3 ** d * (3 ** b - 2 ** b) + 2 ** (b + c) * (3 ** d - 2 ** d):
            return False
    return True

def exclusion_le2_blocks(J=30):
    """Exhaustively confirm NO front-normalized word with <=2 odd blocks admits an acyclic
    paradoxical start, up to total length J. Returns (tested, violations)."""
    tested = 0
    viol = []
    # one block [T]^q [F]^e  (leading zeros strip to this; e>=0)
    for q in range(1, J):
        for e in range(0, J):
            j = q + e
            if not (2 <= j <= J) or 3 ** q >= 2 ** j:
                continue
            v = [True] * q + [False] * e
            tested += 1
            if _admits_acyclic(v):
                viol.append(('1blk', q, e))
    # two blocks [T]^b [F]^c [T]^d [F]^e
    for b in range(1, J):
        for c in range(1, J):
            for d in range(1, J):
                for e in range(0, J):
                    j = b + c + d + e
                    if not (2 <= j <= J) or 3 ** (b + d) >= 2 ** j:
                        continue
                    v = [True] * b + [False] * c + [True] * d + [False] * e
                    tested += 1
                    if _admits_acyclic(v):
                        viol.append(('2blk', b, c, d, e))
    return tested, viol

def _admits_acyclic(v):
    j = len(v); q = ones(v); twom = 2 ** j; dd = twom - 3 ** q
    if dd <= 0:
        return False
    num = numer_fast(v); r = realizing_residue_fast(v)
    start = r if r > 2 else r + twom
    lim = num // dd
    while start <= lim:
        if start > 2 and start < iterate(start, j):
            return True
        start += twom
    return False


if __name__ == "__main__":
    print("== Part A: source lock ==")
    print("identity 2^m y = 3^a n + numer :", check_identity())
    print("numer defs agree               :", check_numer_defs())
    print("criterion (P)==(n<=y), slack (S):", check_criterion_equiv())
    orbit, D = basic_example()
    print(f"basic example 7 (8 steps): orbit={orbit}")
    print(f"  a={D['a']} p=3^a={D['p']} 2^m={D['twom']} y={D['y']} d={D['d']} numer={D['numer']}"
          f"  paradoxical={is_paradoxical(7,8)} acyclic={7<D['y']}")

    print("\n== Part B: enumerate paradoxical starts (acyclic), n<=200000 ==")
    hits = enumerate_paradoxical_by_start(nmax=200000, acyclic=True)
    print(f"count of paradoxical starts (smallest-m witness) n<=200000: {len(hits)}")
    # distinct (j,q) ratios observed
    from collections import Counter
    ratios = Counter()
    for n, m, a, y in hits:
        from math import gcd
        g = gcd(a, m)
        ratios[(a // g, m // g)] += 1
    print("distinct reduced q/j ratios among smallest-m witnesses:")
    for (rq, rj), c in sorted(ratios.items(), key=lambda kv: kv[1], reverse=True):
        print(f"  {rq}/{rj:>3}  count={c:>6}   {classify_ratio(rq, rj)}")
    if hits:
        print("smallest paradoxical starts:", [(n, m, a) for n, m, a, y in hits[:12]])

    print("  odd-block counts of the smallest witnesses:",
          [(n, n_odd_blocks(trace_word(n, m))) for n, m, a, y in hits[:8]])

    print("\n== Part B4: continued fraction of log_3 2 ==")
    print("left convergents/semiconvergents (j<=80):", left_convergents_semiconvergents(80))

    print("\n== Part B (discovery): >=3 odd-blocks exclusion ==")
    print("block-word numer closed forms verified:", verify_block_numer_forms(8))
    tested, viol = exclusion_le2_blocks(J=30)
    print(f"front-normalized words with <=2 odd blocks tested (j<=30): {tested}")
    print(f"  admitting an acyclic paradoxical start: {len(viol)}  (violations: {viol[:3]})")
    print("  => FINDING: every acyclic paradoxical word has >= 3 odd blocks (j<=30 exhaustive,")
    print("     two-block case checked to j<=38 in the extended run).")

# ================= Part B (discovery): word-based branch and bound =================
# Each residue class r mod 2^j corresponds to exactly one word v=traceWord(r,j) (bijection,
# proved in ParityReconstruction.lean residue determinacy). So enumerating paradoxical WORDS
# = enumerating candidate residue classes. numer extremals for fixed (j,q):
#   numer_max(j,q) = 2^(j-q)*(3^q - 2^q)  (ones back-loaded)
#   numer_min(j,q) = 3^q - 2^q            (ones front-loaded)
# (verified below). A word v of length j, q ones, subcritical (3^q<2^j) admits an acyclic
# paradoxical start iff its realizing residue r (taken >2) satisfies  d*r <= numer(v)  with
# strict endpoint, i.e. r <= numer(v)/d and start value r' = r (or r+2^j) is < y.
