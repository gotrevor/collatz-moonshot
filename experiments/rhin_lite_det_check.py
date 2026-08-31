#!/usr/bin/env python3
"""EXACT integer sanity-check of the 3x3 form-determinant for the rhin-LITE
even six-factor subsequence  N = 2000*t  (spacing 2000).

Structure (mirrors CollatzMoonshot/FrontA/RhinLiteApprox.lean):
  H_N(x) = (x-3)^(2 W1 t)(x-2)^(2 W2 t)(x-4)^(2 W3 t)(5x-12)^(2 W4 t)
           (17x^2-102x+144)^(2 W5 t)(19x^2-108x+144)^(2 W6 t),  N = 2000 t, deg = 2N.
  c_j    = [x^j] H_N   (integer coefficients)
  D_N    = lcmUpto N   (we FACTOR it out -- it is a nonzero scalar per row)
  B(t)   = D_N * c_N                       (central coeff)
  A1(t)  = D_N * R1,  R1 = sum_{j != N} c_j (3^(j-N) - 2^(j-N)) / (j-N)   (rational part of ∫_2^3 H/x^{N+1})
  A2(t)  = D_N * R2,  R2 = sum_{j != N} c_j (4^(j-N) - 3^(j-N)) / (j-N)   (rational part of ∫_3^4 H/x^{N+1})
The log(3/2), log(4/3) pieces cancel exactly against B*log, leaving A_i integer.

det(B,A1,A2 at t0,t0+1,t0+2) = D_{N0} D_{N1} D_{N2} * det(rows (c_N, R1, R2)).
D_* != 0, so the form-determinant is nonzero  <=>  det(c_N, R1, R2) != 0.
We compute det(c_N, R1, R2) EXACTLY as a Fraction.
"""
from __future__ import annotations
from fractions import Fraction
import sys, time, math
sys.set_int_max_str_digits(2000000)

def frac_float(fr):
    """Safe float of a possibly-astronomical Fraction via logs."""
    if fr == 0: return 0.0
    s = 1 if fr > 0 else -1
    fr = abs(fr)
    e = fr.numerator.bit_length() - fr.denominator.bit_length()
    m = Fraction(fr.numerator >> max(e,0), fr.denominator >> max(-e,0)) if False else None
    # scale by 2^-e to bring near 1
    val = fr / (Fraction(2)**e)
    try:
        return s * float(val) * (2.0**e)
    except OverflowError:
        return s * math.inf

def frac_log10(fr):
    if fr == 0: return None
    fr = abs(fr)
    return (math.log(fr.numerator) - math.log(fr.denominator))/math.log(10) if fr.numerator and fr.denominator else None

W = (705, 551, 449, 109, 39, 54)
# factors as ascending-coeff integer polynomials, with per-t exponent 2*W_i*t
FACT_COEFFS = [
    (-3, 1),           # x - 3
    (-2, 1),           # x - 2
    (-4, 1),           # x - 4
    (-12, 5),          # 5x - 12
    (144, -102, 17),   # 17x^2 -102x +144
    (144, -108, 19),   # 19x^2 -108x +144
]

def polymul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if bj: r[i+j] += ai*bj
    return r

def polypow(base, e):
    result = [1]
    b = base
    while e:
        if e & 1: result = polymul(result, b)
        e >>= 1
        if e: b = polymul(b, b)
    return result

def build_HN(t):
    poly = [1]
    for coeffs, w in zip(FACT_COEFFS, W):
        poly = polymul(poly, polypow(list(coeffs), 2*w*t))
    return poly

def rational_parts(t):
    """Return (c_N, R1, R2) exactly."""
    N = 2000*t
    c = build_HN(t)
    assert len(c) == 2*N + 1, (len(c), 2*N+1)
    cN = c[N]
    R1 = Fraction(0); R2 = Fraction(0)
    for j, cj in enumerate(c):
        if cj == 0 or j == N: continue
        k = j - N  # ranges -N..N, k!=0
        # 3^k - 2^k over k  (k can be negative -> Fraction handles)
        p3 = Fraction(3)**k; p2 = Fraction(2)**k; p4 = Fraction(4)**k
        R1 += Fraction(cj) * (p3 - p2) / k
        R2 += Fraction(cj) * (p4 - p3) / k
    return cN, R1, R2

def det3(rows):
    (a,b,cc),(d,e,f),(g,h,i) = rows
    return a*(e*i-f*h) - b*(d*i-f*g) + cc*(d*h-e*g)

if __name__ == "__main__":
    ts = [int(x) for x in sys.argv[1:]] or [0,1,2]
    data = {}
    for t in sorted(set(ts)):
        t0 = time.time()
        if t == 0:
            data[t] = (1, Fraction(0), Fraction(0))
        else:
            data[t] = rational_parts(t)
        cN,R1,R2 = data[t]
        ratio = R1/R2 if R2 else None
        print(f"t={t} N={2000*t}: c_N digits={len(str(abs(cN)))}, "
              f"log10|R1|={frac_log10(R1)}, log10|R2|={frac_log10(R2)}, "
              f"R1/R2={frac_float(ratio) if ratio is not None else 'inf'}  "
              f"[{time.time()-t0:.1f}s]", flush=True)
    # form determinant over any consecutive triple present
    tl = sorted(data)
    for i in range(len(tl)-2):
        trip = tl[i:i+3]
        if trip[2]-trip[0] == 2:
            rows = [list(data[t]) for t in trip]
            d = det3(rows)
            print(f"det(c_N,R1,R2) for t0={trip[0]}: {'NONZERO' if d!=0 else 'ZERO!!'}  "
                  f"(log10|det|={frac_log10(d)})")
