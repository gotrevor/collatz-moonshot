# Expected number of cycles of U (q = 1) of length p: each length-p branch word with weight
# n = (#evens) + 2(#odds) closes to the rational c_w / (2^n - 3^p); heuristically it is an
# integer with probability 1/|2^n - 3^p|.  Words: o odd steps (2 choices each), e = 2p - n evens.
from math import comb, log, exp, lgamma
L2, L3 = log(2), log(3)
def log_words(p, n):
    o = n - p
    if o < 0 or o > p: return None
    return lgamma(p + 1) - lgamma(o + 1) - lgamma(p - o + 1) + o * L2
def log_absdiff(p, n):
    # log |2^n - 3^p| computed exactly for small sizes, asymptotically otherwise
    if n < 2000:
        return log(abs(2**n - 3**p)) if 2**n != 3**p else float('inf')
    a, b = n * L2, p * L3
    hi, lo = max(a, b), min(a, b)
    return hi + log(-__import__('math').expm1(lo - hi))
def expected(p):
    tot = 0.0
    for n in range(p, 2 * p + 1):
        lw = log_words(p, n)
        if lw is None: continue
        d = 2**n - 3**p if n < 2000 else None
        if d is not None and abs(d) == 1: continue          # Mihailescu-forced cycles
        tot += exp(lw - log_absdiff(p, n)) / p              # cycles = words / rotations
    return tot
acc = 0.0
rows = []
for p in range(1, 3001):
    e = expected(p); acc += e
    if p in (5, 12) or e > 0.05: rows.append((p, e))
    if p in (4, 5, 11, 12, 13, 50, 100, 199, 200, 500, 1000, 3000): print(f"p<={p:5d} cumulative expected cycles (both signs) {acc:.4f}")
print("p with expected >= 0.05:", [(p, round(e, 3)) for p, e in rows])
tail = sum(expected(p) for p in range(200, 3001))
print(f"expected cycles with 200 <= p <= 3000: {tail:.4f}")
