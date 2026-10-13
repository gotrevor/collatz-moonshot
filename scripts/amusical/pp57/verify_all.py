"""One-shot verification of the ping-pong example sigma = PP(0) (agent "transitive")."""
import json
from fractions import Fraction as F
from pp57 import PP, DM, IM, vp, engine_slope
from pp57_finite import base_automaton, scc_ok, holonomy, strip23
from pp57_scc import adjacency, scc_count
f = PP(0)
json.dump({"pieces": f.pieces, "format": "x = r + a k  ->  s + b k  (r, a, s, b)", "domain_table_mod": DM}, open("pp57_seed0_pieces.json", "w"))
# (V1) bijection: domain table and image table are exact partitions (asserted in constructor); spot-check inverse
assert all(f.inv(f(x)) == x and f(f.inv(x)) == x for x in range(-50000, 50000))
# (V2) C_3, positive slopes
sl = {F(b, a) for (r, a, s, b) in f.pieces}
assert all(q > 0 and vp(q.numerator, 3) - vp(q.denominator, 3) == 1 for q in sl)
print("V1/V2 ok; slopes", sorted(sl), "pieces", len(f.pieces))
# (C1),(C2)
states, S, out = base_automaton(f)
print("C1:", scc_ok(states, S, out))
g, _ = holonomy(f, states, S, out, states[0])
print("C2: prime-to-6 part of translation gcd =", strip23(g))
# filler leaves: depth d <-> slope 3/2^d, images 2-full (odd modulus)
for (r, a, s, b) in f.pieces:
    if a != 665:
        d = {6650: 1, 13300: 2}[a]; assert F(b, a) == F(3, 2**d) and b % 2 == 1
print("filler leaf structure ok")
for M in (2**6 * 9, 5**5, 7**4, 19**2 * 4, 13300 * 3):
    print("SCC count mod", M, "=", scc_count(adjacency(f, M)))
