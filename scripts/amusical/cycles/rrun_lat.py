#!/usr/bin/env python3
"""r-run analysis, exact lattice enumeration (supersedes rrun.py / rrun_np.py).

For a positive U-cycle with length p, halvings e, r E-runs (r local minima), minimum m >= 2:
  Thm A :  m <= (k/|Λ| + 1)/3,  k = e - p                       Λ = e ln2 - p ln3
  Thm A':  m <= 1 + r/|Λ|
  Lem R :  log2 m >= (2p - e)(θ-1)/(θ^r - 1),   θ = log2 3
  Rhin  :  |Λ| >= e^(-13.3)   (Rhin 1987, as applied in Simons 2022 Lemma 10)
Given r, X1:  δ := r/(ln2 (X1-1)).  If ||pθ|| >= δ then |Λ| >= ln2 δ and A' gives m <= X1.
So every r-run cycle with p >= PSTART and m > X1 has ||pθ|| < δ and p <= P_r (Rhin cap).  All
(p, e) with 1 <= p <= P_r and |pθ - e| < δ are enumerated exactly as lattice points
u(q_n, p_n) + v(q_{n+1}, p_{n+1}); for each we check Lemma R against min(A, A').  If every
such p is contradicted, r-run cycles with p >= PSTART have m <= X1 (to be excluded by rsearch).
Usage: rrun_lat.py PSTART X1 RMIN RMAX
"""
import sys, math
from decimal import Decimal, getcontext
getcontext().prec = 100
TH = Decimal(3).ln() / Decimal(2).ln()
LN2 = Decimal(2).ln()
th = float(TH)

# convergents p_n/q_n of θ  (θ ≈ e/p : numerator = e-like, denominator = p-like)
def convergents(N=60):
    a = []; x = TH
    for _ in range(N):
        q = int(x); a.append(q); x = 1 / (x - q)
    P = [1, a[0]]; Q = [0, 1]
    for ai in a[1:]:
        P.append(ai * P[-1] + P[-2]); Q.append(ai * Q[-1] + Q[-2])
    return a, P[1:], Q[1:]
A_CF, PN, QN = convergents()

def P_r(r):
    f = lambda p: ((2 - th) * p - 0.5) * (th - 1) / (th ** r - 1) - math.log2(1 + r * (th * p + 1) ** 13.3)
    p = 1e3
    # f is convex in p; find the last sign change by doubling then bisection on the increasing part
    pmin = 13.3 / math.log(2) / ((2 - th) * (th - 1) / (th ** r - 1))   # argmin of f
    lo = max(p, pmin)
    hi = lo
    while f(hi) <= 0: hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) / 2
        if f(mid) > 0: hi = mid
        else: lo = mid
    return int(hi) + 1

def enumerate_small(P, delta):
    """All (p, e, y) with 1 <= p <= P, |pθ - e| < delta, y = pθ - e (Decimal)."""
    D = Decimal(delta)
    # choose n with q_{n+1} ~ sqrt(P/delta)
    target = math.sqrt(P / delta)
    n = next(i for i in range(len(QN) - 1) if QN[i + 1] >= target)
    qa, pa, qb, pb = QN[n], PN[n], QN[n + 1], PN[n + 1]
    ea, eb = qa * TH - pa, qb * TH - pb
    det = qa * eb - qb * ea                  # = ±1
    assert abs(abs(det) - 1) < Decimal(10) ** -50
    # bounds on u, v over the region 1<=p<=P, |y|<delta
    U = int((abs(eb) * P + qb * D) / abs(det)) + 2
    V = int((abs(ea) * P + qa * D) / abs(det)) + 2
    assert (2 * U + 1) * (2 * V + 1) < 5e7, (U, V)
    out = []
    for v in range(-V, V + 1):
        # p = u qa + v qb in [1, P]  ->  u range
        ulo = -((v * qb - 1) // qa) if True else 0
        ulo = max(-U, -((v * qb - 1) // qa))          # u qa >= 1 - v qb
        uhi = min(U, (P - v * qb) // qa)
        for u in range(ulo, uhi + 1):
            y = u * ea + v * eb
            if abs(y) < D:
                p = u * qa + v * qb; e = u * pa + v * pb
                if 1 <= p <= P: out.append((p, e, y))
    return out, (n, U, V)

def check(PSTART, X1, r):
    delta = r / (math.log(2) * (X1 - 1)) * (1 + 1e-12)
    Pr = P_r(r)
    if Pr < PSTART: return True, Pr, 0, None
    cands, info = enumerate_small(Pr, delta)
    worst = None; bad = []
    for p, e, y in cands:
        if p < PSTART: continue
        lam = abs(y) * LN2                                        # |Λ| = ln2 |pθ - e|
        k = e - p
        MA = (Decimal(k) / lam + 1) / 3
        MAp = 1 + Decimal(r) / lam
        M = min(MA, MAp)
        lb2 = Decimal((2 * p - e)) * (TH - 1) / (TH ** r - 1)     # log2 lower bound for m
        if M > 1 and lb2 <= M.ln() / LN2 * (1 + Decimal(10) ** -30):
            bad.append((p, e, float(M), float(lb2)))
    return (len(bad) == 0), Pr, len(cands), bad

if __name__ == "__main__":
    PSTART, X1, RMIN, RMAX = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    for r in range(RMIN, RMAX + 1):
        ok, Pr, nc, bad = check(PSTART, X1, r)
        print(f"r={r:2d} P_r={Pr:.4e}  candidates(||pθ||<δ)={nc}  {'OK' if ok else 'FAIL'}" +
              ('' if ok else f"  first bad (p,e,M,log2LB)={bad[:3]}  #bad={len(bad)}"))
