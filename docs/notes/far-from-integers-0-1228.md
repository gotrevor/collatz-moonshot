# Keeping `ξ(3/2)ⁿ` far from the integers: `0.1228`, and a `7/57` barrier

[ Claude wrote this note at my direction.  The Lean file it links is the authority.  -Trevor ]

**Abstract.**  How far from the integers can every `ξ(3/2)ⁿ` stay?  The best published lower bound for `β* = sup_{ξ>0} inf_n ‖ξ(3/2)ⁿ‖` is `5/48 ≈ 0.1042` (Dubickas 2008).  We prove `β* ≥ 307/2500 = 0.1228` in Lean, using an explicit memoryless strategy for a nested-interval game.  We also prove that this kind of construction cannot pass `7/57 ≈ 0.1228`: above `7/57`, no memoryless strategy exists.  So the new constant sits at the exact limit of its own method.

All statements live in [`CollatzMoonshot/Benchmark/ArcTrap.lean`](../../CollatzMoonshot/Benchmark/ArcTrap.lean); line links are as of commit `c3ee166`.  Both theorems are proved there, using only the standard axioms.

## The question and what was known

- **Lower bounds** (some `ξ` stays far):
  - Pollington (1981): `4/65` ([`Literature.Pollington1981`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L39)).
  - Dubickas (2008, Math. Nachr., Thm 1.3): `5/48` ([`Literature.Dubickas2008`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L45)).  His proof is also a two-player game, with an adversary choosing between digit pairs.
- **Upper bound** (every `ξ` comes close): Dubickas (2006, JNT, Cor. 1) shows some limit point of `‖ξ(3/2)ⁿ‖` is `≤ 0.2857` ([`Literature.Dubickas2006`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L51)).

So the literature brackets `β*` in `[5/48, 0.2857)`.  This note moves the lower end to `0.1228`.

## 1. The constant

**Theorem** ([`exists_farFromIntegers_1228`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L384)).  There is `ξ > 0` with `307/2500 ≤ {ξ(3/2)ⁿ} ≤ 1 − 307/2500` for every `n ≥ 0`.

**The game** ([`RelaxedStrategy`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L135)).  The constructor holds a window `m + [a, a + l]` containing `ξ(3/2)ⁿ`.  The adversary reveals the parity of the integer part `m`, which fixes the offset `d ∈ {0, 1/2}` of `⌊3m/2⌋`.  The constructor then keeps a sub-window `[u, u + 2l/3]` inside a lift of the arc.  Times `3/2` that is a full-width window again, with left end `{3u/2 + d}`, which must lie in the strategy's set `P` of allowed left ends.  The strategy never reads the integer part beyond its parity, so it runs from every starting integer.  [`exists_trapped_of_relaxedStrategy`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L226) turns a winning strategy into an actual `ξ` by nested intervals.

**The certificate** ([`relaxedStrategy_1228`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L276)).  Arc `[307/2500, 1 − 307/2500]`, width `l = 123/1000`, and `P` a union of eleven intervals with denominator `2²⁴` ([`P1228`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L263)).  The move is a clamp `u = max(a, c)` with one constant `c` for each of the 22 (interval, parity) cells.  Each cell is a handful of rational inequalities checked by `norm_num` ([`cell1228`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L236)).  The intervals were found by an exact lattice fixed-point search (`experiments/arc_trap_k.py`).

## 2. The barrier

**Theorem** ([`relaxed_barrier`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L2621)).  For `7/57 < β < 1/2`, no width `l` and no set `P` give a `RelaxedStrategy` for the arc `[β, 1 − β]`.

**Mechanism.**  `4/19 → 6/19 → 9/19` is a 3-cycle of `x ↦ 3x/2 + d (mod 1)` with parities `0, 0, 1/2`.  The arc's right edge maps to `1/2 − 3β/2`, which equals `6/19` exactly at `β = 7/57`.  The proof has three steps:

- **Domination:** a relaxed strategy is dominated by a component game, in which the constructor keeps a whole component of the window cut by the arc.
- **Funnel:** within 13 moves, an adaptive adversary forces death or a window inside `[x₀, 1 − 9β/4]` with `x₀ > 10/19`, using 35 node lemmas (`barrierNode*`) on one `β`-piece.
- **Runaway:** in the funnel's terminal window, the block of parities `(0, 1/2, 1/2)` pushes the left end away from `10/19` geometrically, by `x ↦ 27x/8 − 5/4`, until the window dies.

Larger `β` follows by monotonicity.  The corollaries [`not_relaxedStrategy_13_100`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L2635) and [`mahler_barrier`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L1569) are also proved; no memoryless strategy holds any arc of length `≤ 1/2`, so this game can never produce a Z-number.

**Conjecture** ([`RelaxedValueIsSevenFiftySevenths`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L3511), 75% for the open half).  The game's value is exactly `7/57`: every `β < 7/57` is winnable.  Certificates win up to `7/57 − 10⁻⁸`, and the edge is the same with 0 to 3 bits of memory.

## What is not claimed

- **Not the true value of `β*`.**  Strategies that remember finitely many bits of the integer part are not covered by the barrier.  In the experiments they did no better, but that is unproved.  Cleverer constructions could beat `7/57`.  The strong conjecture of the companion note ([`arc-traps-two-thirds-edge.md`](arc-traps-two-thirds-edge.md)) would give `β* ≤ 1/6`.
- **Not uncountably many `ξ`.**  The construction gives, for every integer `m ≥ 1`, one `ξ` with integer part in `[m, m + 3)`, so infinitely many.  Pollington's result is uncountable at `4/65`; we have not shown that here.
- **Prior work, by a limited check.**
  - We read the full texts of Dubickas 2006, 2008 and 2010.
  - We checked the forward citations of Flatto–Lagarias–Pollington 1995 (74 papers) and of Dubickas 2008 (19): none improves `5/48` for `3/2`.
  - Unread: Bugeaud's 2012 book, §3.6, on constructions in a prescribed interval.  Our novelty estimate is ~85%.

## Reproducing

- Lean: `lake build CollatzMoonshot.Benchmark.ArcTrap`.
- `experiments/arc_trap_k.py test` covers the game solver and an independent exact orbit check of the certificate (`test_relaxed_certificate_orbits_stay_far`).
- `experiments/arc_barrier.py verify` covers the exact funnel search behind the barrier.
- Research log, with dead ends: [`RESEARCH-2026-10-05-arc-trap-games.md`](../../RESEARCH-2026-10-05-arc-trap-games.md).
