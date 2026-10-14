#!/usr/bin/env python3
"""Independent check of bridge Theorem I on the twins W_{a,b,c}: W(2m)=3m+a, W(4m+1)=3m+b, W(4m+3)=3m+c.

Kohl's det = sum over pieces of t/(lambda*m_piece) for x -> lambda x + t on a class mod m_piece... computed
here directly from the formula det W = (a+b+c)/3 - 1 that bridge states, AND from Kohl's definition
(pieces: on 0(2) x -> (3/2)x + a; on 1(4) x -> (3/4)x + (b - 3/4); on 3(4) x -> (3/4)x + (c - 9/4)).
Flux = #{x<0<=Wx} - #{x>=0>Wx}, counted by brute force on a window wide enough to contain every crossing
(crossings satisfy |x| <= 4*max offset + 4).  Teeth: U = W_{0,1,2} must give 0; W_{3,1,2} must give 1 with
the single up-crossing at -2; perturbing the count window to miss x = -2 must change the answer.
"""
from fractions import Fraction as F


def W(a, b, c):
    def f(x):
        if x % 2 == 0:
            return 3 * (x // 2) + a
        if x % 4 == 1:
            return 3 * (x // 4) + b
        return 3 * (x // 4) + c
    return f


def kohl_det(a, b, c):
    pieces = [(F(3, 2), F(a), 2), (F(3, 4), F(b) - F(3, 4), 4), (F(3, 4), F(c) - F(9, 4), 4)]
    return sum(t / (lam * m) for lam, t, m in pieces)


def flux(f, R):
    up = [x for x in range(-R, 0) if f(x) >= 0]
    down = [x for x in range(0, R) if f(x) < 0]
    return len(up) - len(down), up, down


ok = True
for (a, b, c) in [(0, 1, 2), (3, 1, 2), (6, 1, 2), (9, 1, 2), (0, 4, 2), (0, 1, 5), (-3, 1, 2), (3, 4, 5), (0, -2, 2)]:
    if len({a % 3, b % 3, c % 3}) != 3:
        continue
    f = W(a, b, c)
    R = 4 * max(abs(a), abs(b), abs(c)) + 40
    fl, up, down = flux(f, R)
    d = kohl_det(a, b, c)
    formula = F(a + b + c, 3) - 1
    good = (d == fl == formula)
    ok &= good
    print(f"W_{{{a},{b},{c}}}: Kohl det={d} formula={formula} flux={fl} up={up[:6]} down={down[:6]} {'ok' if good else 'MISMATCH'}")
# teeth
f = W(3, 1, 2)
assert flux(f, 100)[1] == [-2]
assert flux(W(0, 1, 2), 100)[0] == 0
assert flux(f, 1)[0] != 1  # window missing -2 misses the crossing
# orbit of 0 under W_{3,1,2}: forward stays >= 0 and never revisits -2's side
x, seen = 0, []
for _ in range(2000):
    seen.append(x); x = f(x)
assert min(seen) >= 0 and 0 not in seen[1:]
print("orbit of 0 under W_{3,1,2}:", seen[:10], "...  forward min", min(seen))
print("PASS" if ok else "FAIL")
