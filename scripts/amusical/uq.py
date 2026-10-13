# The q-layers of the amusical shift: U_q(2n) = 3n, U_q(r) = (3r+q)/4 if r = q (mod 4),
# (3r-q)/4 if r = 3q (mod 4); q coprime to 6.  U_1 = U, and U_q(q r) = q U(r).
import sys
from math import gcd
def Uq(r, q):
    if r % 2 == 0: return 3 * (r // 2)
    if (r - q) % 4 == 0: return (3 * r + q) // 4
    return (3 * r - q) // 4
def Vq(m, q):
    # inverse: reads m mod 3
    for r in (2 * m // 3 if m % 3 == 0 else None, (4 * m - q) // 3, (4 * m + q) // 3):
        if r is not None and (r % 2 == 0 and m % 3 == 0 or r % 2 == 1) and Uq(r, q) == m:
            return r
    raise ValueError((m, q))
def cycles(q, B, esc=2**80, cap=5000):
    out = []
    for r in range(1, B + 1):
        x = r
        for _ in range(cap):
            x = Uq(x, q)
            if x == r:
                c = [r]; y = Uq(r, q)
                while y != r: c.append(y); y = Uq(y, q)
                out.append(c); break
            if abs(x) < r or abs(x) > r * esc: break
    return out
if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    qs = [q for q in range(1, 200) if gcd(q, 6) == 1]
    for q in qs:
        # bijection sanity on a window
        assert all(Uq(Vq(m, q), q) == m for m in range(-300, 300)), q
        cs = cycles(q, B)
        prim = [c for c in cs if any(x % q for x in c)]
        lens = sorted(len(c) for c in prim)
        print(f"q={q:3d} cycles(min<= {B})={len(cs):3d} primitive={len(prim):3d} lengths={lens[:12]}{'...' if len(lens)>12 else ''} max_min={max((min(c) for c in prim), default=0)}")
