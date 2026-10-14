"""Ren's independent check of the freeform agent's Theorem F (2026-10-13).
F_2[t] polynomials as Python ints (bit i = coefficient of t^i).  Twin U with Q = t^2+t+1 and
assignment s = (s_E, s_A, s_B, s_C):
  E: n = t m           -> Q m + s_E      (bit0 = 0)
  A: n = 1 + t^2 m     -> Q m + s_A      (low bits 01)
  B: n = 1 + t + t^3 m -> Q m + s_B      (low bits 011)
  C: n = 1+t+t^2+t^3 m -> Q m + s_C      (low bits 111)
Claim: for p = 2^e >= 8, m = p/2, x = e_B t^m (t+1)^(m-3) has exact period p, itinerary E^m B^m."""
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def pw(a, k):
    r = 1
    for _ in range(k): r = mul(r, a)
    return r
Q = 0b111
def U(n, s):
    if n & 1 == 0: return mul(Q, n >> 1) ^ s[0], 'E'
    if n & 0b11 == 0b01: return mul(Q, (n ^ 1) >> 2) ^ s[1], 'A'
    if n & 0b111 == 0b011: return mul(Q, (n ^ 0b011) >> 3) ^ s[2], 'B'
    return mul(Q, (n ^ 0b111) >> 3) ^ s[3], 'C'
S0123 = (0, 1, 0b10, 0b11)
# bijectivity on all polynomials of degree < 14: images distinct and closed under degree bound+1
D = 14
img = {}
for n in range(1 << D):
    y, _ = U(n, S0123)
    assert y not in img; img[y] = n
print("injective on deg<14:", len(img) == 1 << D)
def period(x, s, cap):
    y, word = x, []
    for j in range(1, cap + 1):
        y, a = U(y, s); word.append(a)
        if y == x: return j, ''.join(word)
    return None, None
eB = 0b11001   # t^4 + t^3 + 1
u = 0b11
for e in range(3, 9):
    p = 1 << e; m = p // 2
    x = mul(mul(eB, pw(0b10, m)), pw(u, m - 3))
    per, w = period(x, S0123, 4 * p)
    print(f"p={p:4d}: period={per}  itinerary==E^mB^m: {w == 'E'*m + 'B'*m}  deg x={x.bit_length()-1}")
# teeth 1: non-power-of-2 analogue (m = 6, p = 12) must NOT close
for m in (5, 6, 7):
    x = mul(mul(eB, pw(0b10, m)), pw(u, m - 3)); per, _ = period(x, S0123, 200)
    print(f"teeth m={m} (p={2*m}, not 2^e): period within 200 = {per}")
# teeth 2: s_E != 0 assignment (1023-style) must break the family
S1023 = (1, 0, 0b10, 0b11)
x = mul(mul(eB, pw(0b10, 8)), pw(u, 5)); per, _ = period(x, S1023, 200)
print("teeth s_E=1, p=16: period within 200 =", per)
# over Z: x_m = 2^m (4^m - 3^m)/(9^m - 8^m) integer only at m = 1
from fractions import Fraction
print("Z analogue integral m in 1..40:", [m for m in range(1, 41) if Fraction(2**m * (4**m - 3**m), 9**m - 8**m).denominator == 1])
