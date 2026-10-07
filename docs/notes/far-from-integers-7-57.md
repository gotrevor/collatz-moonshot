# Keeping `ξ(3/2)ⁿ` far from the integers: `7/57`, and why that is the method's exact limit

[ Claude wrote this note at my direction.  The Lean file it links is the authority.  -Trevor ]

**Abstract.**  How far from the integers can every `ξ(3/2)ⁿ` stay?  The best published lower bound for `β* = sup_{ξ>0} inf_n ‖ξ(3/2)ⁿ‖` is `5/48 ≈ 0.1042` (Dubickas 2008).  We prove `β* ≥ 7/57 ≈ 0.1228` in Lean, using an explicit memoryless strategy for a nested-interval game: seven intervals with rational endpoints and one window width, `1/8`.  We also prove that this kind of construction cannot pass `7/57`: above it, no memoryless strategy exists.  So the game's value is exactly `7/57`, and it is attained.

All statements live in [`CollatzMoonshot/Benchmark/ArcTrap.lean`](../../CollatzMoonshot/Benchmark/ArcTrap.lean); line links are kept current by `scripts/reanchor-notes.py`.  Every theorem below is proved there.

## The question and what was known

- **Lower bounds** (some `ξ` stays far):
  - Pollington (1981): `4/65` ([`Literature.Pollington1981`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L40)).
  - Dubickas (2008, Math. Nachr., Thm 1.3): `5/48` ([`Literature.Dubickas2008`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L46)).  His proof is also a two-player game, with an adversary choosing between digit pairs.
- **Upper bound** (every `ξ` comes close): Dubickas (2006, JNT, Cor. 1) shows some limit point of `‖ξ(3/2)ⁿ‖` is `≤ 0.2857` ([`Literature.Dubickas2006`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L52)).

So the literature brackets `β*` in `[5/48, 0.2857)`.  This note moves the lower end to `7/57`.  In Lean, `β*` is [`E`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L399) `(3/2)`, with `E α = sup_{ξ>0} inf_n ‖ξαⁿ‖`.  The bracket `7/57 ≤ E(3/2) ≤ 0.2857` is [`E_three_halves_ge_757`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3687) and [`E_three_halves_le`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L472) (the latter from the cited Dubickas 2006 input).  The calibrations [`E_two`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L417) (`E 2 = 1/3`) and [`E_three`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L455) (`E 3 = 1/2`) check that the definition measures what it should.

## 1. The constant

**Theorem** ([`exists_farFromIntegers_757`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3678)).  There is `ξ > 0` with `7/57 ≤ {ξ(3/2)ⁿ} ≤ 50/57` for every `n ≥ 0`.

**The game** ([`RelaxedStrategy`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L136)).  The constructor holds a window `m + [a, a + l]` containing `ξ(3/2)ⁿ`.  The adversary reveals the parity of the integer part `m`, which fixes the offset `d ∈ {0, 1/2}` of `⌊3m/2⌋`.  The constructor then keeps a sub-window `[u, u + 2l/3]` inside a lift of the arc.  Times `3/2` that is a full-width window again, with left end `{3u/2 + d}`, which must lie in the strategy's set `P` of allowed left ends.  The strategy never reads the integer part beyond its parity, so it runs from every starting integer.  [`exists_trapped_of_relaxedStrategy`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L227) turns a winning strategy into an actual `ξ` by nested intervals.

**The certificate** ([`relaxedStrategy_757`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3592)).  Arc `[7/57, 50/57]`, width `l = 1/8`, and `P` the union of seven closed intervals ([`P757`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3580)):

`[13/152, 22/171]`, `[29/152, 11/57]`, `[53/152, 20/57]`, `[565/1368, 79/171]`, `[239/456, 10/19]`, `[311/456, 13/19]`, `[1021/1368, 15/19]`.

Every denominator divides `8 · 9 · 19`.  The move is a clamp `u = max(a, c)`, with one constant `c` per cell.  The fourteen (interval, parity) pairs need eighteen cells, because four of them split once.  Each cell is a handful of rational inequalities checked by `norm_num` ([`cell1228`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L237)).

**How it was found.**  An exact lattice fixed-point search (`experiments/arc_trap_k.py`, `solve_vw`) returns this same set for every `β` from `7/57 − 10⁻³` to `7/57 − 10⁻⁶`.  Read as rationals, its endpoints check exactly at `β = 7/57` with closed intervals (`experiments/arc_value_757.py`).  The search had reported a loss at `7/57` itself only because it discards one-point intersections.  An earlier certificate reached `307/2500 = 0.1228` with eleven intervals ([`exists_farFromIntegers_1228`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L385)).

## 2. The barrier

**Theorem** ([`relaxed_barrier`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L2681)).  For `7/57 < β < 1/2`, no width `l` and no set `P` give a `RelaxedStrategy` for the arc `[β, 1 − β]`.

**Mechanism.**  `4/19 → 6/19 → 9/19` is a 3-cycle of `x ↦ 3x/2 + d (mod 1)` with parities `0, 0, 1/2`.  The arc's right edge maps to `1/2 − 3β/2`, which equals `6/19` exactly at `β = 7/57`.  The proof has three steps:

- **Domination:** a relaxed strategy is dominated by a component game, in which the constructor keeps a whole component of the window cut by the arc.
- **Funnel:** within 13 moves, an adaptive adversary forces death or a window inside `[x₀, 1 − 9β/4]` with `x₀ > 10/19`, using 35 node lemmas (`barrierNode*`) on one `β`-piece.
- **Runaway:** in the funnel's terminal window, the block of parities `(0, 1/2, 1/2)` pushes the left end away from `10/19` geometrically, by `x ↦ 27x/8 − 5/4`, until the window dies.

Larger `β` follows by monotonicity.  The corollaries [`not_relaxedStrategy_13_100`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L2695) and [`mahler_barrier`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L1629) are also proved; no memoryless strategy holds any arc of length `≤ 1/2`, so this game can never produce a Z-number.

**The value** ([`relaxedStrategy_exists_iff`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3694)).  For `β < 1/2`, a memoryless relaxed strategy for `[β, 1 − β]` exists iff `β ≤ 7/57`.  The certificate's endpoints sit on the same `19`-adic grid as the barrier's cycle: `10/19`, `13/19` and `15/19` are right ends of `P`, and `10/19 → 15/19 → 13/19` is the mirror cycle that drives the runaway.

## What is not claimed

- **Not the true value of `β*`.**  The barrier covers memoryless strategies only.  Two observations bear on what lies beyond:
  - Strategies that remember `k` bits of the integer part did no better on this arc: the edge stays at `7/57` for `k = 0, …, 6, 8, 10, 12`.  One bit is provably no help ([`finiteMemoryRelaxedValue_one`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3767)); every `k` is the conjecture [`FiniteMemoryRelaxedValue`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3762).  Off the symmetric position memory does help: for the arc `[2/5, 2/5 + 0.87]`, 3 bits win where 0 to 2 lose ([`MemoryHelpsOffCentre`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3792)).
  - A constructor that knows the whole integer part does much better in experiments.  Every `m < 200` has a `ξ ∈ [m, m + 1)` with `‖ξ(3/2)ⁿ‖ ≥ 0.142` for all `n < 200`, and random `m` up to `10³⁰` behave the same (worst `0.138`).  That is numerics to finite depth, not a theorem ([`FullInformationBeatsSevenFiftySevenths`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3803)).  If both conjectures hold, bounded 2-adic memory stops at exactly `7/57` while full knowledge of the integer part does not.
  - The strong conjecture of the companion note ([`arc-traps-two-thirds-edge.md`](arc-traps-two-thirds-edge.md)) would give `β* ≤ 1/6`.
- **Not uncountably many `ξ`.**  The construction gives, for every integer `m ≥ 1`, one `ξ` with integer part in `[m, m + 3)`, so infinitely many.  Pollington's result is uncountable at `4/65`; we have not shown that here.
- **Prior work, by a limited check.**
  - We read the full texts of Dubickas 2006, 2008 and 2010.
  - We checked the forward citations of Flatto–Lagarias–Pollington 1995 (74 papers) and of Dubickas 2008 (19): none improves `5/48` for `3/2`.
  - Unread: Bugeaud's 2012 book, §3.6, on constructions in a prescribed interval.  Our novelty estimate is ~85%.

## Reproducing

- Lean: `lake build CollatzMoonshot.Benchmark.ArcTrap`.
- `experiments/arc_value_757.py test` covers the closed-interval check at `7/57` (and its failure just above), the eighteen cells, and exact orbit play from several starts.
- `experiments/arc_trap_k.py test` covers the game solver.
- `experiments/arc_barrier.py verify` covers the exact funnel search behind the barrier.
- Research log, with dead ends: [`RESEARCH-2026-10-05-arc-trap-games.md`](../../RESEARCH-2026-10-05-arc-trap-games.md).
