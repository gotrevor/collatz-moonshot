# G_2 benchmark cycle hunt; the ceiling of Flatto's Z-number count

5 October 2026, follow-on to [the rewriting-lane landscape](RESEARCH-2026-10-05-rewriting-lane-landscape.md).  Two cheap probes, both closed.  No new theorem.

## 1. Refuting a benchmark map by a cycle: nothing up to 10^7

Nashida's "open" label means that no start x ≤ 500 cycled or escaped within 5000 steps.  A positive cycle above 500 would show that a map does **not** terminate, which would answer his Q2 negatively for that map, with a `decide` certificate.

`experiments/g2_orbit_hunt.py run maps_G2_open.tsv 10000000 100000` covers every start up to 10^7, with exact 128-bit arithmetic.  It found **no cycle and no step-cap hit in any of the 4389 maps**.  The 1273 maps with a start passing 2^120 are lucky long runs: each such orbit, followed with bignums, halts within 152 steps.  Controls: all 300 sampled `INF-cycle` maps report cycles, and 300 sampled `FIN-term` maps stay silent.  The hand-checked suite is `g2_orbit_hunt.py test`.

Scope: 2069 of the 4389 maps never decrease, so they cannot cycle, and this probe could not touch them.  Only the 2320 maps with a shrinking branch were at risk.

## 2. Improving Flatto's Z-number count: the method has a ceiling

Flatto (1992) bounds the Z-numbers below X by `O(X^{log₂(3/2)})`.  Two searches found no later improvement.  The idea was to beat it with more of Mahler's forbidden parity words (`11`, `10101`, ...).  It cannot work inside the 2-adic horizon:

- With `ξ(3/2)^i = g_i + r_i`, the parity word of `g_0` is an itinerary of the slope-3/2 map `rstep` on `[0, 1/2)`, cut at 1/3.  So the forbidden words are exactly that map's non-itineraries, and nothing further is available to add.
- A start `g < 2^n` determines only its first n parities, and every word occurs (Terras's bijection for `⌈3g/2⌉`).
- The admissible words number at least `(3/2)^n`.  Exact counts for n = 1..14: 2, 3, 5, 8, 12, 18, 27, 40, 60, 90, 134, 201, 302, 452, which is about 1.55·(3/2)^n.  So Flatto's exponent is exactly what a horizon-limited count can reach.

Beating log₂(3/2) requires the parities of `⌈3g/2⌉`-iterates beyond `log₂ g` steps, which is the open core of Mahler's problem.  Lean: `CollatzMoonshot/Benchmark/FlattoCeiling.lean` holds five statements, sorried, with English proofs and confidence levels.  Maze row: "within-horizon refinement of Flatto's Z-number count", `adversary2adic`.

## Where this leaves the benchmark

Every benchmark map's termination looks Mahler-type (the 2069 monotone maps) or Collatz-type (the mixed maps).  FLP closes nothing, and cycle search finds nothing.  Confidence that some benchmark map can be settled in either direction with known tools: about 10%.  The staged [Mahler wiring](KICKOFF-2026-10-05-mahler-benchmark.md) remains a valid small edge.
