# How short an arc can hold an orbit of `ξ(3/2)ⁿ`?  The `2/3` edge

[ Claude wrote this note at my direction.  The Lean file it links is the authority.  -Trevor ]

**Abstract.**  Mahler asked whether some `ξ > 0` has every fractional part `{ξ(3/2)ⁿ}` in the arc `[0, 1/2)`.  Flatto–Lagarias–Pollington (1995) showed that no arc shorter than `1/3` can hold such an orbit.  We ask the same question for constructions that only ever read finitely many low bits of the integer part `⌊ξ(3/2)ⁿ⌋`.  The answer is exactly `2/3`.  No such construction holds any arc shorter than `2/3`, at any position.  The closed arc `{x : ‖x‖ ≤ 1/3}` is held, from every starting integer, by a two-state strategy that needs no memory at all.  We then conjecture that `2/3` is the true edge for every `ξ`.  That conjecture contains Mahler's problem.  We give exact computational evidence that integer parts behave like random 2-adic integers here, and a decay law near the extremal arc.

All statements live in [`CollatzMoonshot/Benchmark/ArcTrap.lean`](../../CollatzMoonshot/Benchmark/ArcTrap.lean); line links below are as of commit `0fb5476`.  Each item says how far its proof has got.

## Setting

Fix an arc `I = [s, s + t]` mod 1.  Write `g_n = ⌊ξ(3/2)ⁿ⌋` and `f_n = {ξ(3/2)ⁿ}`.  The digit `a_n = g_{n+1} − 3g_n/2 = 3f_n/2 − f_{n+1}` is a half-integer in `{−1/2, 0, 1/2, 1}`, and

`3ᴺ g_0 = 2ᴺ g_N − Σ_{n<N} 3^{N−1−n} 2^{n+1} a_n`,

so **the first `N` digits fix `g_0 mod 2ᴺ`**.  This is the 2-adic horizon.  The real place sees the digits through `f_n`; the integer part sees them only modulo `2ᴺ`.

A *finite-memory construction* is a rule that reads the integer part mod `2ᵏ` and builds nested intervals of `ξ`.  What any such rule delivers, if it works on a whole residue class, is [`TrapsResidueClass s t k r`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L250): every `m ≡ r (mod 2ᵏ)` has a trapped orbit with integer part in `[m, m + 3)`.  The memoryless version is the game [`RelaxedStrategy`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L135).  There an adversary picks the parity offset `d ∈ {0, 1/2}` fresh at each step, and the constructor keeps a sub-window inside a lift of the arc.  Its soundness, [`trapsResidueClass_of_relaxedStrategy`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L259), is a standard nested-interval argument, stated in Lean with the proof written out in its docstring.

## 1. The edge theorem

**Theorem** ([`finiteMemory_min_arc_two_thirds`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L457)).  For every arc of length `t < 2/3`, every `k` and every `r`, `TrapsResidueClass s t k r` fails.  The closed arc `[2/3, 4/3]`, that is `{‖x‖ ≤ 1/3}`, satisfies `TrapsResidueClass (2/3) (2/3) 0 0`.

So the shortest arc a finite-memory construction holds has length exactly `2/3`, and the minimum is attained.  [`finiteMemoryEdgeIsTwoThirds`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L466) is the "every neighbourhood of the AFS arc is held" form, by monotonicity.

### Below `2/3`: counting

If a construction works on a residue class mod `2ᵏ`, then about `2^{N−k}/3` integer parts below `2ᴺ` are trapped.  By injectivity they need that many distinct admissible digit words of length `N`.  On an arc shorter than `2/3`, admissible words grow like `C(N + 1)λᴺ` with `λ < 2` ([`admissibleWord_growth_lt_two`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L364)), so the count fails for large `N` ([`finiteMemory_barrier_two_thirds`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L374)).  The growth bound combines two path counts:

- Forward paths grow at most like Fibonacci when `t < 3/4` ([`card_forward_le`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L341)).  Of two sibling successors, at most one can branch again, because four grandchildren spaced by `1/4` need an arc of length `3/4`.
- Backward paths lose a branch within `K` steps once `(2/3)^{K−1} < 2 − 3t` ([`card_backward_le`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L353)).

Status: hand proofs, recorded as Lean statements with the proof in the docstring; the Lean proofs are not yet written.  An independent exact certificate covers lengths up to `13/20` at every position ([`finiteMemory_barrier`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L281); `experiments/arc_entropy.py cover`).  At length exactly `2/3` counting gives nothing: every non-wrapping arc of length `2/3` admits at least `2ᴺ` words ([`two_pow_le_card_admissibleWord`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L308)), because `3I/2` has length exactly `1`.

For comparison, the same counting puts the Flatto–Lagarias–Pollington edge at `1/3` (one word), and Mahler's arc (length `1/2`) at growth `3/2`, which is Flatto's `x^{log₂(3/2)}` count of Z-numbers.

### At `2/3`: a two-state strategy

**Theorem** ([`relaxedStrategy_afs_closed`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L425), proved in Lean).  `RelaxedStrategy (2/3) (2/3) (1/2) {0, 1/2}` holds.

The windows are `[0, 1/2]` and `[1/2, 1]` past the current integer part `m`.

- From `m + [0, 1/2]`, keep `m + [0, 1/3]`.  It lies in the arc's lift `[−1/3, 1/3]`, and times `3/2` it is `⌊3m/2⌋ + d + [0, 1/2]`.
- From `m + [1/2, 1]`, keep `m + [2/3, 1]`.  It lies in the lift `[2/3, 4/3]`, and times `3/2` it is `⌊3m/2⌋ + d + [1, 3/2]`.

Whatever parity the adversary picks, the next window starts at `d ∈ {0, 1/2}` mod 1, so the two windows cycle forever.  Hence every positive integer `m` is the integer part of some `ξ ∈ [m, m + 1/3]` with `‖ξ(3/2)ⁿ‖ ≤ 1/3` for all `n` (start from the window `m + [0, 1/2]`).  The Lean form, [`trapsResidueClass_afs_closed`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L451), records the weaker `[m, m + 3)` that every memoryless strategy gives.  The strategy has no interior, which is why lattice searches with inward rounding miss it.  We found it by exact minimax of the game (`experiments/arc_entropy.py closed`).

The arc `{‖x‖ ≤ 1/3}` is the one in Akiyama–Frougny–Sakarovitch (2008), who use rational-base numeration to give countably many `ξ` with `‖ξ(3/2)ⁿ‖ < 1/3`.  The orbit-level fact here is probably already implicit in their tree.  What we add is the pairing with the lower bound: a memoryless rule, from every integer, at exactly the length below which no finite-memory rule works.

## 2. Conjecture: `2/3` is the true edge

**Conjecture** ([`StrongMahlerConjecture`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L499), confidence 60%).  For `t < 2/3`, no `ξ > 0` has every `{ξ(3/2)ⁿ}` in an arc of length `t`.

Proved consequences:

- No Z-numbers, which is Mahler's conjecture ([`strongMahler_no_zNumber`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L527)).
- `sup_ξ inf_n ‖ξ(3/2)ⁿ‖ ≤ 1/6` ([`strongMahler_far_le_one_sixth`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L673)).  The best published upper bound is Dubickas (2006), `≈ 0.2857`.

The known bounds on the shortest arc holding some orbit are `1/3` (FLP) below and `2/3` (attained, §1) above.  The conjecture says the upper one is right.  It is at least as hard as Mahler's problem.  Proving the random model below on short intervals of integers would prove it, and we know no route to that.

**Evidence: integer parts behave like random 2-adic integers.**  If they did, each integer part would survive `N` steps with probability `(λ/2)ᴺ`, where `λ` is the word growth.  `experiments/arc_survival.py rate` measures survival exactly over all integer parts below `2ᴷ`.  `experiments/arc_entropy.py` computes `λ` independently by transfer-matrix bounds.

| arc | `2 × survival decay rate` | entropy `λ` (inner, outer) |
|---|---|---|
| `[0, 1/2]` (Mahler) | 1.5012 (`m < 2^15`) | [1.4986, 1.5079] |
| `[1/6, 23/30]` | 1.7279 (`2^14`) | [1.7183, 1.7270] |
| `[7/10, 13/10]` | 1.9326 (`2^13`) | [1.9223, 1.9281] |

The two numbers agree to within 0.5%, and no integer part outlives its random-model lifetime.  So at these lengths the integers show no structure a construction could exploit.

## 3. At length exactly `2/3`: only the AFS arc survives

At length `2/3` the word growth is exactly `2`, so the random model is a critical branching process: survival `≈ 1/(1 + cN)`, with every integer part eventually dying.  `arc_survival.py profile` follows every integer part below `2^10` to depth 400 at 18 positions `s` of the arc `[s, s + 2/3]`.

| s | survivors at N = 50 | 100 | 200 | 400 | c |
|---|---|---|---|---|---|
| 0 | 385 | 228 | 121 | 72 | 0.033 |
| 1/2 | 441 | 234 | 122 | 66 | 0.036 |
| 19/30 | 855 | 676 | 512 | 311 | 0.0057 |
| 13/20 | 1000 | 918 | 803 | 568 | 0.002 |
| **2/3** | **1023** | **1023** | **1023** | **1023** | **0** |
| 61/90 | 1014 | 976 | 882 | 800 | 0.0007 |
| 7/10 | 807 | 598 | 421 | 221 | 0.0091 |

At generic positions `1/S − 1` doubles each time `N` doubles, the critical-branching signature.  `c(s)` falls toward `0` near the AFS position, but only `s = 2/3` plateaus.  Read as branching, the AFS arc has offspring variance exactly zero (each window keeps one piece), and every other position has positive variance.

Two conjectures record this.

- [`AfsArcIsolatedAtTwoThirds`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L477) (65%): among arcs of length `2/3`, only the AFS arc is held memorylessly.  The exact component game from the window `[0, 3]` survives depth 18 only at `s = 2/3`.  It dies by depth 6–11 elsewhere, including at `2/3 ± 1/100`.
- [`AfsArcIsUniqueMinimal`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L518) (35%): an orbit fits in an arc of length `≤ 2/3` only if the arc is `{‖x‖ ≤ 1/3}`.  It implies the strong conjecture ([`afsArcIsUniqueMinimal_strongMahler`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L523), proved).

## 4. Near the AFS arc: a decay law

Shift the AFS arc by `δ`, to `[2/3 + δ, 4/3 + δ]`.  A piece of a trapped interval anchored at an integer `k` is `k + [e_L, 1/3 + e_R]` or `k + [2/3 + e_L, 1 + e_R]`.  One step of `×3/2` acts on the endpoint errors exactly, as long as the errors stay small:

- anchor parity `0`: `(e_L, e_R) ↦ (3e_L/2, δ)`;
- anchor parity `1`: `(e_L, e_R) ↦ (δ, 3e_R/2)`.

So an error grows by `3/2` along a run of equal parities and resets to `δ` when the parity flips ([`afsErrStep`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L592), checked exactly in `test_endpoint_error_recursion_is_exact`).  The anchor parities of the integer parts below `2ᴺ` run through every binary word of length `N` once.  Consequences (hand proofs, with Lean statements):

- **Every integer part survives `≈ log_{3/2}(1/|δ|)` steps** ([`near_afs_every_floor`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L579)).  This order is sharp: the adversarial game kills at exactly depth `8 + j` at `δ = ±(1/30)(2/3)ʲ`, `j = 0..8`.
- **A typical integer part survives at least `≈ |δ|^{−1/log₂(3/2)} = |δ|^{−1.7095…}` steps** ([`near_afs_density`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L569) with [`run_bounded_count_ge`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L587)).
- **The AFS piece breaks at rate `Θ(|δ|^{1/log₂(3/2)})` up to a logarithm** ([`afsUnbroken_of_noRunLonger`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L614), [`card_afsUnbroken_le`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L636)).

**Conjecture** ([`NearAfsDecayExponent`](../../CollatzMoonshot/Benchmark/ArcTrap.lean#L667), 55%).  The critical decay constant is `c(δ) = Θ(|δ|^{1/log₂(3/2)})`.  Measured: `c = 0.0070` at `δ = 1/30` and `0.0036` at `δ = 1/45`.  That is a ratio of `1.94` per rung of `2/3` in `δ`, against a predicted `2`.  The gap from the proved break rate to `c` is real.  Most breaks are harmless changes of shape (break rate `≈ 0.08` against `c ≈ 0.007` at `δ = 1/30`).  The pieces of one integer part also share bits, so standard critical-branching theorems do not apply directly.

## What is not claimed

- Nothing here proves Mahler's conjecture or improves the FLP lower bound `1/3` for individual `ξ`.  §2 is a conjecture, with evidence.
- Both halves of the edge theorem are now proved in Lean (2026-10-06): `finiteMemory_min_arc_two_thirds` and `finiteMemoryEdgeIsTwoThirds` depend only on the standard axioms.  The lower half runs through `card_forward_le`, `card_backward_le`, `admissibleWord_growth_lt_two` and `finiteMemory_barrier_two_thirds`; the upper half through `trapsResidueClass_of_relaxedStrategy`.  What remains open in the file is off this path: the `1227`/`1228` constants, `relaxed_barrier`, `two_pow_le_card_admissibleWord` (the matching `2^N` lower count), and the near-AFS bounds.
- **Prior work, by a quick check only.**
  - Flatto (1992) treats only arcs `[0, t)`, with no general positions, no `2/3` and no growth-`2` count; his Z-number count is our length-`1/2` case at position `0`.
  - Akiyama–Frougny–Sakarovitch (2008) own the extremal arc (see §1).
  - Unread: Bugeaud's 2012 book, ch. 3, and the open-dynamical-systems literature on β-transformations with holes, where the entropy of a map avoiding a hole is a known theme.  Our novelty estimate for the edge theorem is ~80%.

## Reproducing

- Lean: `lake build CollatzMoonshot.Benchmark.ArcTrap`.
- Experiments, each with a test suite (`<script> test`) that checks against hand-computed values:
  - `experiments/arc_entropy.py`: word growth, the `13/20` certificate, and the exact component game (`closed S`).
  - `experiments/arc_survival.py`: survival rates (`rate`), the critical-length profile (`profile`), adversarial depths (`depth`), and the near-AFS recursion.
- The full research log, with dead ends: [`RESEARCH-2026-10-05-arc-trap-games.md`](../../RESEARCH-2026-10-05-arc-trap-games.md).
