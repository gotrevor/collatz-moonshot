#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Checks the drift argument that normality forces a cycle tail for C >= 5.

Per word (n, s = size n, t = C s letters): E <= s + a H + B, with E even letters, H odd letters at
height > Y, B odd letters at height <= Y.  Summed over words: B / P >= (1/2 - 1/C - a/2 - bias terms).
Control: the per-word inequality with a = 0.5 < log2(3/2) must fail, and C = 4 has a negative margin."""
import math
Y, a = 100, 0.59
tau = 0
for y in range(1, Y + 1):
    x, j = y, 0
    while x != 1:
        x = (3 * x + 1) // 2 if x % 2 else x // 2
        j += 1
    tau = max(tau, j)
print("max steps to reach 1 from y <=", Y, ":", tau)
print("(3y+1)/(2y) at y =", Y + 1, ":", (3 * (Y + 1) + 1) / (2 * (Y + 1)), "<= 2^a =", 2**a)
kmax = 16
for C in (4, 5, 6, 8):
    P = O = B = U = alt4 = 0
    viol = viol_ctrl = 0
    for n in range(1, 2**kmax):
        s = n.bit_length()
        x, E, H, b, u, run, oc = n, 0, 0, 0, 0, 0, 0
        for i in range(C * s):
            if x == 1:
                u += 1
                if i + 8 <= C * s:
                    oc += 1
            if x % 2:
                if x > Y: H += 1
                else: b += 1
                x = (3 * x + 1) // 2
            else:
                E += 1
                x //= 2
        if E > s + a * H + b + 1e-9: viol += 1
        if E > s + 0.5 * H + b + 1e-9: viol_ctrl += 1
        P += C * s; O += H + b; B += b; U += u; alt4 += oc
    margin = 0.5 - 1 / C - a / 2
    print(f"C={C}: O/P={O/P:.4f} B/P={B/P:.4f} U/P={U/P:.4f} occ(10^4 from 1)/P={alt4/P:.4f} "
          f"violations={viol} control-violations={viol_ctrl} margin={margin:+.4f} "
          f"predicted B/P>={(margin + (O/P - 0.5) * (1 + a)) / (1 - a):+.4f}")
