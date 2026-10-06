# Certified nested-interval games for (3/2)^n mod 1: a new constant, and the horizon made explicit

5 October 2026.  Trevor's charge: build a tool that sees past the 2-adic horizon in Mahler's problem, or prove that you can't.  This note records the tool built in response, its first result, and what it says about Mahler's arc.

## The tool

A Z-number keeps every `{ξ (3/2)^n}` in the arc `[0, 1/2)`.  Generalize to any arc `A`, and *construct* `ξ` by nested intervals.  Track `y = ξ (3/2)^n` on a window `[m + a, m + a + l]`: integer part `m`, fractional left end `a`, and window `[a, a + l] ⊂ A`.  Multiplying by 3/2 stretches the window to length `3l/2` at fractional offset `3a/2 + d`, where `d = (m mod 2)/2`.  We then pick a child window of width `l` inside it.  The horizon lives in `d`.  The parity of the integer part at the next step depends on bits of `m` that a finite strategy cannot see.

- **k-memory game** (`experiments/arc_trap_k.py`): the strategy remembers `m mod 2^k`.  The new top bit after each step is adversarial, so the strategy must win for both lifts.  `k = 0` is fully parity-blind (`experiments/arc_trap.py`).
- **Certificate**: for each residue `r`, a finite union `P_r` of rational intervals, closed under the step.  This is the greatest fixed point, computed in exact `Fraction` arithmetic.  A nonempty fixed point implies that some `ξ > 0` keeps every `{ξ (3/2)^n}` in `A`.  Lean: `Benchmark/ArcTrap.lean`, `exists_trapped_of_winningStrategy`.

## Controls (known answers the tool had to find, unprompted)

| Arc | Known | Tool |
|---|---|---|
| `[4/65, 61/65]` | uncountably many `ξ` (Pollington 1981) | winnable at `k = 0` |
| any arc of length `< 1/3` | empty (FLP 1995) | no strategy |
| symmetric around 0, length `t` | `t = 2/3`: countably many (AFS / Akiyama 2008) | `k = 0` winnable for every tested `t > 2/3` (down to 0.67), none at `t = 2/3` |

The last row is the striking one.  The parity-blind game dies exactly where the AFS double points take over.  Their double points are 2-adically rigid, so a parity-blind strategy should not find them.

## New result (pending formal proof)

**There is `ξ > 0` with `‖ξ (3/2)^n‖ ≥ 1227/10000` for every `n ≥ 0`** (first pass: `7349/61440 ≈ 0.1196`).  The previous record is **Dubickas's `5/48 ≈ 0.1042`** (Math. Nachr. 281 (2008), infinitely many `ξ` with `{ξ(3/2)^n} ∈ (5/48, 43/48)`), not Pollington's `4/65 ≈ 0.0615` (1981) as first written here.  The ladder brackets it: blind play (`k = 0`, 0.0861) falls short of 5/48 and `k = 2` beats it by about 18%.  Confidence it is unpublished: about 85%.  See *Literature check* below.
- Certificate: `experiments/arc_cert_beta_1227_k2.json` (`k = 2`, `l = 26411/300000`, residues with 4, 6, 6, 4 intervals), from `arc_trap_k.py certificate 2 1227/10000 480 OUT` in about 4 s.  First-pass certificate: `experiments/arc_cert_beta_k2.json` (`k = 2`, `l = 23371/230400`, four residues with at most six intervals each).  `arc_trap_k.py certificate 2 7349/61440 60 OUT` regenerates it.
- Independent check: an exact constructor that knows `m` completely ran 250 steps from five starts (`m₀ = 4, 8, ..., 20`), with random valid choices.  It never got stuck, and every `ξ` had `‖·‖ ≥ 0.124`.
- Blind play (`k = 0`) reaches `β ≈ 0.0861` (`arc_cert_beta_k0.json`).  Remembering 2 bits reaches 0.1196 on a 60-width grid.  On a 480-width grid, `k = 2, 3, 4` all win at 0.1227 and fail at 0.1228.  At 960 widths `k = 2` still fails at 0.1228, so the edge is the fixed-width game's value, not a grid artifact.  Constructed orbits sit near 0.124, so a **variable-width** game is the next lever.
- Not yet shown: uncountability (that needs a branching strategy with variable widths), and the sharp constant (the width grid is coarse; observed orbits sit near 0.124).

## The relaxed game: 0.1228, and the value looks like exactly 7/57

**Relaxation.**  The window `m + [a, a + l]` need not lie in the arc.  Only the sub-window `m + [u, u + 2l/3]` that the next step selects must, because every `ξ(3/2)^n` of the final `ξ` lands there.  The child window is `1.5` times that sub-window.  This game dominates the window-in-arc game (`test_relaxed_dominates_window_in_arc`).  Code: `solve_vw` in `experiments/arc_trap_k.py`.  The exact fixed point is only reached in the limit, so the solver rounds inward to a `2^-24` lattice each round and returns a post-fixed point (`P ⊆ step(P)`).  That is all soundness needs.

**Results** (symmetric arc `[β, 1 - β]`):
- Value `7/57 = 0.12280701…` to `1e-8`: wins at `7/57 - 1e-8`, fails at `7/57` and at `7/57 + 1e-8`.
- The same edge holds at `k = 0, 1, 2, 3`.  **Memory buys nothing in the relaxed game**, whereas the window-in-arc game needed 2 bits to pass 0.1.
- Two widths per game add nothing over one.
- Memoryless certificate at `β = 307/2500 = 0.1228`: `experiments/arc_cert_beta_1228_vw_k0.json`, one width `123/1000`, eleven intervals.  Exact 300-step orbits from `m₀ ∈ {1, 2, 3, 4, 5, 8, 13, 100, 1001}` all stay at least 0.12280 from the integers.
- Lean: `RelaxedStrategy`, `exists_trapped_of_relaxedStrategy`, `exists_farFromIntegers_1228` (all `sorry`), and the conjecture `RelaxedValueIsSevenFiftySevenths`.

**Why 7/57: the 3-cycle `4/19 → 6/19 → 9/19`.**  Under `x ↦ 3x/2 + d (mod 1)` with parities `d = 0, 0, 1/2` this is a cycle: `(27/8)(4/19) + 1/2 = 46/38 ≡ 4/19`.  The arc's right edge `1 - β` maps with `d = 0` to `1/2 - 3β/2`.  That equals `6/19` exactly at `β = 7/57`.  So the edge's image lands on the cycle at the measured threshold.  How the adversary turns this into a forced exit is not yet written down.

## Theorem: the memoryless adversarial-parity construction stops at 7/57

**Statement.**  For every `β > 7/57` there is no memoryless relaxed strategy for the arc `[β, 1 - β]`.  In Lean this is `relaxed_barrier` (`sorry`, with the proof route in its docstring), and the Maze row is "adversarial-parity arc trap past 7/57".  With the certificates below 7/57, the game's value is `7/57` up to `1e-8` on the lower side.

**The game it rests on.**  A relaxed strategy is dominated by the *component game*: the adversary picks the parity `d` each step, the constructor keeps a whole component `C` of `W ∩ (arc lifts)`, and `W ← 1.5 C + d (mod 1)`.  Since `d` is fresh each step, integer shifts of `W` are irrelevant and a larger window is never worse.

**Proof.**
1. **Funnel (computer-assisted, exact).**  For `β ∈ (7/57, 0.1229]` an adaptive adversary forces every constructor branch, within 13 moves, either to die or to reach a window inside `[x₀, R₀]` with `x₀ > 10/19` and `R₀ = 1 - 9β/4`.  `experiments/arc_barrier.py verify` runs an AND-OR search whose window endpoints are affine in `β`.  Every comparison is decided on open `β`-pieces (3 pieces), and the 3 split points are checked exactly.  Teeth test: below 7/57 the same search finds no funnel.
2. **Runaway lemma (by hand).**  Let `β ∈ (4/35, 4/19)`, `g(x) = 27x/8 - 5/4`, and take a window `[x, R₀]` with `10/19 < x < R₀`.  The adversary plays `d = 0, 1/2, 1/2`.
   - Step 1: the window lies inside the arc, so `C = W` and `W ← [3x/2, 3/2 - 27β/8]`.
   - Step 2: `3R₀/2 < 1 + β` (since `β > 4/35`) and `3R₀/2 > 1 - β` (since `β < 4/19`), so the only component is `[3x/2, 1 - β]`.  It is empty, and the constructor dies, iff `3x/2 ≥ 1 - β`.  Otherwise `W ← [9x/4 - 1/2, 1 - 3β/2]`, which lies inside the arc.
   - Step 3: `W ← [g(x), R₀]`, where `g(x) < R₀` follows from step 2's non-emptiness.
   - Then `g(x) - x = (19/8)(x - 10/19)`, so `x_n - 10/19 = (27/8)^n (x₀ - 10/19)` grows until `3x_n/2 ≥ 1 - β` kills it.
3. **Monotonicity.**  For `β > 0.1229` the arc is smaller.  Shadow each window by its `β = 0.1229` counterpart and play that adversary; the shadow dies, so the real window dies.

**Where 7/57 comes from.**  The block `(0, 1/2, 1/2)` cycles `10/19 → 15/19 → 13/19`, the mirror image of `4/19 → 6/19 → 9/19` under `x ↦ 1 - x`, which swaps the parities.  The funnel parks the window's left end at the image of the arc's left edge under two `1/2`-steps, `9β/4 + 1/4`.  That lies past the repelling point `10/19` exactly when `β > 7/57`.

**Scope (corrected 2026-10-05).**  The theorem covers memoryless strategies, i.e. every parity treated as adversarial and seen only when it arrives.  It does **not** yet cover `k`-memory strategies.
- **Why not:** there the adversary commits a high bit `k - 1` steps ahead, and the constructor's later choice of integer lift `J` XORs into the eventual parity.  So the adversary cannot simply force a chosen parity sequence.
- **Evidence it still holds:** the `k = 1, 2, 3` relaxed games also stop at 7/57 (to `1e-6`).
- **Retracted:** an earlier line here said "lookahead does not rescue the constructor".  That was measured in a model where the adversary commits *parities* ahead, which is not the `k`-memory game.
- **Retracted:** a fixed-sequence version of the funnel ("one sequence kills against any lookahead").  It relied on pruning dominated windows, and that pruning is unsound once integer shifts matter.

**Reading.**  The literature window is `[5/48, 0.2857)`.  Adversarial-parity constructions top out at `7/57 ≈ 0.1228`.  Above that, a construction must use the integer arithmetic of `m`, i.e. the bits beyond the horizon, not treat them as noise.  The note's Mahler section is the same story: bounded lookahead buys nothing.

## Theorem: adversarial-parity constructions cannot reach Mahler's arc

**Statement.**  No memoryless relaxed strategy holds any arc of length at most `1/2`, at any position.  In particular none holds Mahler's `[0, 1/2]`.  Lean: `mahler_barrier` and `no_relaxedStrategy_mahler_arc` (`sorry`, proof route in the docstrings).  Maze row: "adversarial-parity construction of a Z-number".

**Proof.**
1. **Domination:** the component game dominates every memoryless relaxed strategy (see the 7/57 section).
2. **Containment:** any arc of length `≤ 1/2` lies in a closed arc `[s, s + 1/2]`, and a smaller arc only helps the adversary.
3. **Every position, exactly:** `experiments/arc_mahler.py verify` checks that for every `s ∈ [0, 1)` the adversary kills every path within 5 moves.  It runs the same exact AND-OR engine with the position `s` as the symbol: 22 open `s`-pieces plus 22 exact points.  Teeth test: the holdable arc `[0.12, 0.88]` is not reported killed.
4. **Hand proof for length `t < 1/2`:**
   - `A` and `A + 1/2` are disjoint, so of any window `1.5C` the adversary leaves at most half in the arc.  Hence `|C|` shrinks by at least `3/4` per move.
   - Once the window is shorter than the gap `1/2 - t`, it cannot meet both `A` and `A - 1/2`, so the adversary picks the parity that misses.

**What it means.**  This is the constructive side of the 2-adic horizon, made exact.  Seeing each parity only when it arrives, with every unseen parity treated as hostile, a construction cannot even hold an arc of Mahler's length, let alone produce a Z-number.  A Z-number construction must use the actual integer parts.

**Scope.**  Memoryless strategies only; the finite-memory section below removes that limit up to `13/20`.  For `k`-memory strategies the game-tree argument meets the same obstacle as in the 7/57 section applies: the constructor's lift choice feeds into later parities.  The old window-in-arc ladder supports the barrier there too: shortest winnable arc from 0 was 0.827 for `k = 2..6`.

## Theorem: no finite-memory construction holds an arc of length ≤ 13/20

**Statement.**  Fix any `k` and any residue `r`.  No construction that traps an orbit in an arc of length `≤ 13/20` near *every* start `m ≡ r (mod 2^k)` exists, at any position of the arc.  Every `k`-memory strategy in any of our games is such a construction, because it reads only `m mod 2^k`.  So memory of any finite size cannot reach Mahler's arc.  Lean: `finiteMemory_barrier`, with corollary `relaxed_barrier_13_20` (it extends `mahler_barrier` from `1/2` to `13/20`) and wiring lemma `trapsResidueClass_of_relaxedStrategy`.

**How it was found.**  The `k`-memory relaxed solver (`solve_vw`, `k = 0..5`) holds no arc of length `1/2` at 120 positions × 15 widths.  Bisecting the shortest holdable arc gave `≈ 0.683` (at `s ≈ 0.65`), *identical* for `k = 0, 1, 2, 3`.  Memory that never helps suggested a counting obstruction, not a game-tree one.

**Proof.**
1. **Digits:** write `g_n = ⌊ξ(3/2)^n⌋` and `f_n` for the fractional part.  Then `a_n = g_{n+1} − 3g_n/2 = 3f_n/2 − f_{n+1}` lies in `{−1/2, 0, 1/2, 1}`.
2. **Injectivity:** `3^N g_0 = 2^N g_N − Σ 3^{N−1−n} 2^{n+1} a_n`, so `N` digits fix `g_0 mod 2^N`.  Hence the number of trapped floors `g < 2^N` is at most `W_N(I)`, the number of length-`N` digit words with all `f_n ∈ I`.  (Flatto 1992 is the case `I = [0, 1/2)`, where `W_N ~ (3/2)^N`; `FlattoCeiling.lean` is that case.)
3. **Growth:** `experiments/arc_entropy.py cover 13/20 2000 320` covers every position by 2000 arcs of length `13/20 + 1/2000`.  For each it builds the transfer matrix on interval states, rounded outward to the grid `1/320` (an overcount), and checks exactly a rational `v > 0` with `Mv ≤ cv`.  The worst `c` is `999/500`, so `W_N ≤ C(1.998)^N`.
4. **Density:** a residue-class construction has at least `2^{N−k}/3 − 1` trapped floors below `2^N + 3`.  That beats `C(1.998)^N` for large `N`.

**Checks** (`arc_entropy.py test`, 4 tests):
- **Mahler's arc:** the bound sits between Flatto's `3/2` and the golden ratio (hand argument: on `[0, 1/2]` two odd floors in a row force `f ≥ 5/9`).
- **Soundness teeth:** arcs that a strategy provably holds must have growth `≥ 2`, and the certifier refuses all three: Pollington's arc, the 0.1228 arc, and the shortest-arc witness region.
- **Certify has teeth:** `c = 3/2` is refused on Mahler's arc.

**The edge is 2/3, and it is sharp at the best position.**  (This replaces a first reading at a coarse `1/60` position grid, which put the game edge at `0.683` and suggested a gap.)

| arc length | digit-word growth | meaning |
|---|---|---|
| `1/3` | `1` | FLP's edge: nothing shorter traps any orbit |
| `1/2` | `3/2` | Mahler's arc; Flatto's exponent `log₂(3/2)` (exact at *every* position: one digit fits per step) |
| `2/3` | `2` | counting stops excluding residue classes; the game starts winning |

- **Counting stops at 2/3 (hand proof, `two_pow_le_card_admissibleWord`).**  Take a non-wrapping arc `I` of length `2/3`.  `3I/2` has length exactly `1`, so almost every `y ∈ I` has exactly two digits leading into it, and Lebesgue measure is an eigenmeasure with eigenvalue `4/3`.  Cylinders are at most `(2/3)^N · 2/3` long, so at least `2^N` words are admissible.  Numerically the growth is `2` at length `2/3` for every position tested, wrapping arcs included, and `2.0000` on both bounds at the AFS position.  At length `0.6` it varies with position (`1.71`–`1.86`), so "growth `= 3t`" is false in general and exact only at these lengths.
- **The game reaches 2/3 (`relaxedStrategy_near_afs`).**  A memoryless strategy with one width `≈ 1/2` holds `[2/3 − 10⁻⁶, 4/3 + 10⁻⁶]`, i.e. `‖ξ(3/2)^n‖ ≤ 1/3 + 10⁻⁶`, from every integer part.  Removing the `10⁻⁶` from either end loses.  For `s ∈ [0.60, 0.66]` the game edge is pinned at right end `1/3`, and nothing holds once `s ≥ 0.67`: the AFS arc `{‖x‖ ≤ 1/3}` is the corner.  Memory `k = 2, 4` changes nothing.
- **Per position the two edges differ.**  The counting edge is `≈ 2/3` at every position (brackets at `s = 0, 0.1, …, 0.9` all contain `2/3`).  The game edge is `0.73`–`0.90` away from the AFS corner, `0.80` at Mahler's position.  So "the game wins exactly when words grow at least as fast as `2^N`" is false position by position, and true for the best arc.
- **Conjecture (`FiniteMemoryEdgeIsTwoThirds`):** no residue-class construction holds any arc shorter than `2/3`, and every neighbourhood of the AFS arc is held.  Proved part: every length `< 2/3` (hand proof, next section; certificate to `13/20`).
- **Reading:** the 2-adic horizon has an exact size.  Seeing finitely many bits buys a positive-density family of orbits, and positive density needs `2^N` digit words, which needs arc length `2/3`.  Mahler's `1/2` (growth `3/2`, Flatto's count) is a full `1/6` below that.  Seeing past the horizon means producing a zero-density set of orbits, which no finite-state rule can single out.  Maze row: "digit-word counting past arc length 2/3".

## Theorem: below 2/3, by hand

**Statement.**  On every arc of length `t < 2/3`, at any position, digit words grow like `C(N+1)λ^N` with `λ < 2`.  So no construction that works on a whole residue class mod `2^k` holds the arc, for any `k`.  This is the first half of `FiniteMemoryEdgeIsTwoThirds`.  The conjecture is now exactly its second half, that every neighbourhood of the AFS arc is held (`finiteMemoryEdgeIsTwoThirds_iff`).  Lean: `card_forward_le`, `card_backward_le`, `admissibleWord_growth_lt_two`, `finiteMemory_barrier_two_thirds`.

**Proof.**
1. **Split each word at an edge hit.**  Every component of a word's cylinder has a left endpoint `ℓ` where some `f_j(ℓ)` is a left edge `b` of the arc (`s`, or `0` if the arc wraps).  So the word is a backward path of length `j` into `b` followed by a forward path of length `N − j` from just right of `b`.  Hence `W_N ≤ 2 Σ_j B_j · M_{N−j}`.
2. **Forward paths are Fibonacci (`t < 3/4`).**  A point has at most two successors, `y` and `y + 1/2`.  If both branch, their four successors are the quarter points `z + {0, 1/4, 1/2, 3/4}` mod 1, which no arc shorter than `3/4` holds.  So `M_n ≤ M_{n−1} + M_{n−2}`, giving `M_n ≤ fib(n + 2)`.
3. **Backward paths lose a branch (`t < 2/3`).**  Use the coordinate `v = 3((f − s) mod 1) ∈ [0, 3t]`.  The predecessors of `v` are `w = frac(2v/3 − s)`, plus `w + 1` exactly when `w ≤ τ = 3t − 1`.  In a tree that is full to depth `j`, the depth-`j` values `w` are the images of one point under `j` rounds of the two maps `w ↦ frac(2w/3 − s)` and `w ↦ frac(2w/3 + 2/3 − s)`.  The two images of a set with circular gaps `≤ δ` interleave, with gaps `≤ 2δ/3` over a span longer than 1.  So the gaps are `≤ (2/3)^j`.  Once `(2/3)^j < 2 − 3t`, some node lands in `(τ, 1)` and has one predecessor.  Thus `B_K ≤ 2^K − 1` for `K = j + 1`, and `B_n ≤ C(2^K − 1)^{n/K}`.
4. **Conclude.**  `λ = max(φ, (2^K − 1)^{1/K}) < 2`.  Injectivity and density finish as in `finiteMemory_barrier`.

**Why `2/3` exactly:** at `t = 2/3` we have `τ = 1`, the forbidden arc `(τ, 1)` is empty, and every point has two predecessors.  That is the same fact as the Lebesgue eigenmeasure behind `two_pow_le_card_admissibleWord`.

**Checks** (`arc_entropy.py test`, 13 tests).  They use an independent implementation in actual fractional parts, not the `v` coordinate:
- **Lemma depth:** the bound `j₀` agrees with hand values (`2` at `1/2`, `8` at `13/20`).
- **Sampled trees:** backward trees never stay full past `j₀`, and they reach it, so the bound is tight.  At `2/3`, trees never break.
- **Forward counts:** they stay `≤ fib(N + 2)` at length `0.74`; at `0.8`, `4 > fib(4)` is reached.
- **Backward cap:** `≤ 2^11 − 1` backward paths at `t = 33/50`, `K = 11`.
- **Decomposition:** the split-sum dominates the exact word count.

**Status:** hand proof, confidence 85%; Lean statements with `sorry`.  The certificate route (`finiteMemory_barrier`, `13/20`) remains as independent evidence.

## Theorem: the finite-memory edge is exactly 2/3

**Statement** (`finiteMemoryEdgeIsTwoThirds`, a Lean proof term over two `sorry`ed hand proofs):
- **(i)** No construction that works on a whole residue class mod `2^k` holds any arc shorter than `2/3`, at any position (previous section).
- **(ii)** For every `ε > 0` a memoryless strategy holds `{‖x‖ ≤ 1/3 + ε}` from every integer part.  So for every `ε > 0`, a positive density of integer parts carry a `ξ` with `‖ξ(3/2)^n‖ ≤ 1/3 + ε` for all `n`.  AFS give countably many with `< 1/3`.

**The AFS half, by hand** (`relaxedStrategy_afs`).  Width `l = 1/2 + 3ε/2`; window starts `P = [1/2 − 3ε/2, 2/3) ∪ [5/6 − 3ε/2, 1)`; sub-windows `[u, u + 1/3 + ε]` fit the arc lift iff `u ∈ [2/3 − ε, 1]`.

| start `a` | parity `d = 0` | parity `d = 1/2` |
|---|---|---|
| `[1/2 − 3ε/2, 2/3)` | `u = max(a, 2/3 − ε) < 2/3` → `3u/2 ∈ [1 − 3ε/2, 1)` (second piece) | same `u` → `3u/2 − 1/2 ∈ [1/2 − 3ε/2, 1/2)` (first piece) |
| `[5/6 − 3ε/2, 1)` | `u = max(a, 1 − ε) ≤ 1` → `3u/2 − 1 ∈ [1/2 − 3ε/2, 1/2]` | `u = max(a, 8/9 − ε) < 1` → `3u/2 − 1/2 ∈ [5/6 − 3ε/2, 1)` |

**Where `ε > 0` is used:** once, in the top-left cell, which needs the sliver `[2/3 − ε, 2/3)`.  At `ε = 0` this `P` fails (`test_afs_strategy_needs_positive_eps`), but a different, degenerate `P` works (next section), so this table is superseded.

**How it was found:** the lattice solver's certificates at `ε = 10⁻³, 10⁻⁴, 10⁻⁶` had the same two-piece shape with endpoints affine in `ε`.  Read off, the shape is the strategy above.  `arc_entropy.py afs EPS` checks the witnesses against `RelaxedStrategy`'s exact conditions, endpoints included.

**What it says:** the 2-adic horizon has size exactly `2/3`.  Finite memory buys every arc longer than `2/3` around `{‖x‖ ≤ 1/3}`, and nothing shorter, anywhere.  Mahler's arc is `1/6` inside the line.  Any Z-number construction must produce a zero-density family of integer parts, which no finite-state rule can do.

## Theorem: the edge is attained, at the closed AFS arc (2026-10-06)

**Statement** (`relaxedStrategy_afs_closed`, proved in Lean, no `sorry`; `finiteMemory_min_arc_two_thirds`).  The closed arc `{‖x‖ ≤ 1/3}` is held by a memoryless strategy with window width `1/2` and only two window starts, `P = {0, 1/2}`:

| window | keep | lift | image | next start |
|---|---|---|---|---|
| `[0, 1/2]` | `[0, 1/3]` | `[−1/3, 1/3]` | `[0, 1/2] + d` | `d` |
| `[1/2, 1]` | `[2/3, 1]` | `[2/3, 4/3]` | `[1, 3/2] + d` | `d` |

Whatever the parity, the next window starts at `d ∈ {0, 1/2}`, so the two windows cycle forever.  So every positive integer `m` is the floor of some `ξ ∈ [m, m + 1/3]` with `‖ξ(3/2)^n‖ ≤ 1/3` for all `n` (`trapsResidueClass_afs_closed`; the start window is `m + [0, 1/2]`).  The shortest arc a finite-memory construction holds therefore has length exactly `2/3`, and the minimum is attained.  `finiteMemoryEdgeIsTwoThirds` now follows from monotonicity alone, and `relaxedStrategy_afs` is superseded.

**Why it was missed:** the strategy has no interior.  The lattice solver rounds inward and drops degenerate intervals, and the `ε > 0` table was read off its interval-shaped certificates.  Exact minimax of the component game (the constructor keeps a maximal piece, the adversary picks `d` fresh) at `s = t = 2/3` reached only 5 states from the window `[0, 3]`, and the winning core is exactly this cycle (`arc_entropy.py closed 2/3`).

**Novelty (cheap check):** the orbit-level fact is essentially Akiyama-Frougny-Sakarovitch 2008 (~60% that their rational-base tree already gives one `ξ` per integer).  What is ours is the sharp pairing: nothing shorter than `2/3` for any finite memory, and `2/3` attained.

**Conjecture `AfsArcIsolatedAtTwoThirds` (65%):** among arcs of length exactly `2/3`, only the AFS arc is held memorylessly.  The component game from `[0, 3]` survives depth 18 only at `s = 2/3`; it dies by depth 6 to 11 at `s = 0, 1/6, 1/3, 1/2, 3/5, 13/20, 7/10, 2/3 ± 1/100`.  Counting cannot see this (growth is exactly 2 at every position), so a proof needs the game.  Whether `k`-memory rescues other positions at length `2/3` is open.

## Conjecture: 2/3 is the true edge for every ξ (2026-10-06)

**Statement** (`StrongMahlerConjecture`, 60%): no orbit `{ξ(3/2)^n}` fits in an arc shorter than `2/3`.  It implies Mahler's conjecture (`strongMahler_no_zNumber`, proved from it) and `E(3/2) ≤ 1/6` (`strongMahler_far_le_one_sixth`; Dubickas 2006 has `0.2857`).  Read this way, the finite-memory theorem is the positive-density shadow of the conjecture.

**Heuristic, made quantitative.**  `N` digits fix `⌊ξ⌋ mod 2^N`, and the arc admits `~λ^N` words.  If integer parts behaved like random 2-adic integers, each would survive `N` steps with probability `(λ/2)^N`.  `experiments/arc_survival.py` measures the survivor decay exactly, over all integer parts below `2^K`:

| arc | `2 × decay rate` | entropy `λ` (`arc_entropy.py`, inner/outer) |
|---|---|---|
| `[0, 1/2]` (Mahler) | 1.5012 (`m < 2^15`, depths 10–25) | [1.4986, 1.5079] |
| `[1/6, 23/30]` | 1.7279 (`2^14`, 15–45) | [1.7183, 1.7270] |
| `[7/10, 13/10]` | 1.9326 (`2^13`, 30–150) | [1.9223, 1.9281] |

The two independent numbers agree to within 0.5%.  No integer part outlives its random-model lifetime: the best below `2^13` on `[7/10, 13/10]` reaches depth 226, against a predicted ~260.  At the critical length (`[0, 2/3]`, `λ = 2`) survivors decay slowly, roughly like `N^{-0.7}`, as a critical branching process would.  Only the AFS position shows no decay at all: exact alignment of `3I/2` with the parity lattice `Z/2` beats randomness there, and nowhere else we looked.

**Where the difficulty sits:** proving the random model on short intervals (the residues of admissible words equidistributed in `[0, X) ⊂ Z/2^N` for fixed `X`) would prove the conjecture, and with it Mahler's.  It is exactly as hard.  What the probe adds is that the integers show no hidden structure for a construction to exploit, at any of the lengths tested.

**Reformulation used along the way:** with digits `b_n = 2a_n ∈ {−1, 0, 1, 2}`, the same series `S(b) = Σ b_n 2^n / 3^{n+1}` gives `{ξ} = S(b)` at the real place and `⌊ξ⌋ = −S(b)` at the 2-adic place.  So a trapped `ξ` is a digit sequence whose real tails stay in the arc and whose 2-adic sum is a nonpositive integer.  This is probably AFS's rational-base numeration in other clothes.

## The critical length: only AFS survives (2026-10-06)

At length exactly `2/3` the growth is `λ = 2`, so the random model is a *critical* branching process: survival probability `~1/(cN)`, and every integer part eventually dies.  Measured with `arc_survival.py profile S 2/3 10 400`, every integer part below `2^10` to depth 400, at 18 positions:

| s | S(50) | S(100) | S(200) | S(400) | c in `S/S0 ≈ 1/(1+cN)` |
|---|---|---|---|---|---|
| 0 | 385 | 228 | 121 | 72 | 0.033 |
| 1/2 | 441 | 234 | 122 | 66 | 0.036 |
| 3/4 | 475 | 269 | 173 | 120 | 0.019 |
| 19/30 | 855 | 676 | 512 | 311 | 0.0057 |
| 13/20 | 1000 | 918 | 803 | 568 | 0.002 |
| **2/3** | **1023** | **1023** | **1023** | **1023** | **0** |
| 61/90 | 1014 | 976 | 882 | 800 | 0.0007 |
| 7/10 | 807 | 598 | 421 | 221 | 0.0091 |

The other ten positions look like the generic rows.  At generic positions `1/S − 1` doubles each time `N` doubles, which is the critical-branching signature.  Near the AFS arc the constant `c(s)` falls toward `0`, but no position plateaus: only `s = 2/3` keeps everyone alive.  Read as a branching process, the AFS arc has offspring variance exactly zero (each window keeps exactly one piece, `relaxedStrategy_afs_closed`).  Everywhere else the variance is positive and the process dies.

**Conjecture `AfsArcIsUniqueMinimal` (35%):** an orbit fits in an arc of length `≤ 2/3` only if the arc is `{‖x‖ ≤ 1/3}` itself.  It implies `StrongMahlerConjecture` (`afsArcIsUniqueMinimal_strongMahler`, proved).  If true, the AFS arc is a rigid minimum, with no slack in any direction.  The confidence is lower than for the strong conjecture because the critical case is exactly where infinitely many integer parts could beat probability 1.

## Near the AFS arc: the decay rate is |δ|^{1/log₂(3/2)} (2026-10-06)

**Mechanism (exact).**  Shift the AFS arc by `δ`.  A piece anchored at an integer `k` is `k + [e_L, 1/3 + e_R]` or `k + [2/3 + e_L, 1 + e_R]`.  One step of `×3/2` and cutting by the arc's lifts gives:

- anchor parity 0: `(e_L, e_R) ↦ (3e_L/2, δ)`
- anchor parity 1: `(e_L, e_R) ↦ (δ, 3e_R/2)`

The new anchor is `(3k − p)/2 + (previous parity)`, which is the AFS integer map.  So an endpoint error grows by `3/2` along a run of equal parities and resets to `δ` when the parity flips.  A run of length `R` costs `(3/2)^R |δ|`, and it breaks the piece (death or branching) once that reaches a constant.  The recursion was checked exactly against the lift cuts while its conditions hold: 0 mismatches over ~800 orbits, and a wrong growth factor is caught (`test_endpoint_error_recursion_is_exact`).

**Consequences.**
- **Worst case:** every integer part survives `~log_{3/2}(1/|δ|)` steps (`near_afs_every_floor`), and that is the right order.  The adversary kills at exactly `8 + k` steps at `δ = ±(1/30)(2/3)^k`, `k = 0..8`, from the window `[0, 3]` (`test_adversarial_depth_ladder`).
- **Typical case:** the anchor parities of `g < 2^N` run through `{0,1}^N` bijectively.  So the density of integer parts trapped to depth `N` is at least the density of words with runs `≤ R(δ)`, which is at least `(1 − 2^{−R})^N` (`near_afs_density`, `run_bounded_count_ge`).  Since `2^{−R(δ)} ≍ |δ|^{1/log₂(3/2)} = |δ|^{1.7095…}`, a typical integer part lives at least `~|δ|^{−1.71}` steps.  That is exponentially longer than the worst case, and the exponent is the reciprocal of Flatto's `log₂(3/2)`.

**Conjecture `NearAfsDecayExponent` (55%):** the critical decay constant is `c(δ) = Θ(|δ|^{1/log₂(3/2)})`.  Inside the horizon (1023 integer parts drawn uniformly below `2^N`, so the parities are exactly uniform), `c = 0.0070` at `δ = 1/30` and `0.0036` at `δ = 1/45`.  That is a ratio of `1.94` per rung, against a predicted `2`.  Beyond the horizon (all integer parts below `2^10`) the law looks the same, with `c` about 1.3–1.45 times larger.  The rung `δ = 1/30, 1/45, 2/135, 4/405` gives `0.0102, 0.0047, 0.0025, 0.0014`.  The matching upper bound concerns the transfer operator only, so it is on the provable side of the horizon.

## The upper bound: event rate pinned, decay constant still open (2026-10-06)

**Proved by hand, with sorried Lean statements:** the AFS piece breaks at rate `Θ(|δ|^{1/log₂(3/2)})`, up to a logarithm.
- Words with runs `≤ R` keep the piece unbroken (`afsUnbroken_of_noRunLonger`).
- A flip followed by `m` equal letters always breaks it once `|δ|((3/2)^m − 1) > 1/3` (`not_afsUnbroken_of_long_run`).  Cutting the word into disjoint blocks of length `m + 1` gives at most `2^N (1 − 2^{−m})^{⌊N/(m+1)⌋}` unbroken words (`card_afsUnbroken_le`).
- `R` and `m` are both `log_{3/2}(1/|δ|) + O(1)`.
- Checked exhaustively at `δ = 1/30` (`R = 2`, `m = 6`): the unbroken words number 200/256, 2304/4096 and 26384/65536 at `N = 8, 12, 16`, between the bounds (`test_afs_event_rate_bounds`).

**Not proved: `c(δ) ≍ |δ|^{1.71}` (`NearAfsDecayExponent`).**  I put the full proof at ~50% earlier, and that was too high: it is now ~20%.  Two obstacles:
1. **Breaks are not deaths.**  At `δ = 1/30` the piece breaks about `0.08` times per step, while the decay constant is `c ≈ 0.007`.  Most breaks are shape changes the piece survives.  The rate of *fatal* events has the same exponent heuristically, but proving that needs a classification of what a broken piece becomes.
2. **The pieces are coupled.**  All pieces of one integer part draw their parities from the same bits.  Two anchors differing by `D` have parities differing by `D mod 2`, deterministically.  So the process is not a Galton–Watson process, and Kolmogorov's `1/(σ²N)` survival theorem does not apply.  A proof would need a martingale (piece count weighted by an eigenfunction) with conditional variance proportional to its size, and the coupling makes that variance hard to bound below.

No mechanism is known for either.  This is a dead end for now.

## Novelty against Flatto 1992 (read 2026-10-05)

Flatto (`papers/flatto-1992-z-numbers-beta-transformations.md`, Lean `Literature.Flatto1992`) treats only arcs `[0, t)`.  For 3/2 his results are:
- **Thm 6.1:** `|Z(x)| = O(x^{log₂(3/2)})` on `[0, 1/2)`.
- **Thm 7.2:** the general `p/q` version, for `t ≤ 1/q` only, and with no gain for smaller `t`.

There are no general positions, no entropy as a function of arc length, no `2/3` and no growth `2`.

Against our results:
- **Growth below 2 under 2/3, and the density-zero barrier:** new.
- **At least `2^N` words at length 2/3:** new.
- **Growth exactly `3/2` at length 1/2:** his case at position 0; other positions are new.
- **The AFS-neighbourhood strategy, and the edge theorem:** not his subject.

Novelty of the edge theorem: ~80% (unread risk: Bugeaud 2012 ch. 3, and later β-transformation papers on "open dynamical systems / holes", where entropy of a map restricted to avoid a hole is a known theme).

## What the ladder says about Mahler

For arcs `[0, t]` (Mahler's position) the shortest winnable `t` is 0.857 at `k = 0, 1` and 0.827 at `k = 2..6`.  Bounded 2-adic memory saturates after two bits, far above Mahler's 1/2.  Every Z-number construction would have to sit in FLP's decoupled regime (`t ≤ 1/2`).  There the integer parts are forced (at most one `ξ` per unit interval), so a finite-memory strategy has nothing to steer.
- **Now a theorem (up to length `13/20`):** see `finiteMemory_barrier` above.  The first proof attempt ("the child's integer offset `j` is forced") was incomplete; counting digit words replaced it.
- **Reading:** this is the horizon in constructive form.  Seeing `k` bits further helps only while the arc has slack (length `> 1/2`).  Mahler's arc has none, so the only way past is to know *all* the bits, i.e. the integer itself.  That is the countable, rigid regime where Z-numbers would have to live.

## Literature check (2026-10-05, second pass)

- **Forward citations** (`papers followups`) of FLP 1995 (74 papers) and of Dubickas 2008 (19): no constant above 5/48 for `ξ(3/2)^n`.
- **Direction trap:** Dubickas, JNT 117 (2006), and the multiplicative Markoff–Lagrange papers (Akiyama–Kaneko 2021, Akiyama–Kamae–Kaneko 2022, Kaneko–Steiner 2023) bound `lim sup ‖ξα^n‖` **from below** for every `ξ`, e.g. a limit point in `[0.238, 0.762]`.  That is the opposite quantity: how close to the integers an orbit can stay, not how far.  None competes.
- **Same direction, other bases:** Dubickas, Results Math. 57 (2010): `‖ζ(5/3)^n‖ > 1/10` and `‖τ(9/4)^n‖ < 14/45` for some `ζ`, `τ` (abstract only; full text paywalled).
- **Full texts read** (`papers/dubickas-2006-…`, `-2008-…`, `-2010-…`):
  - **2008, Thm 1.3:** every `(k, k + 1)` holds a `ξ` with `‖ξ(3/2)^n‖ > 5/48`.  Dubickas notes Pollington *announced* 0.088.  The proof is a two-player game (Lemma 1.4): an adversary offers `{3, -1}` or `{1, -3}`, the player picks a digit, and the tail `|Σ u_{n+j}(2/3)^j|` must stay below 2.3745.  That is the same shape as our game with an adversarial parity bit.  Ours adds the arc geometry and the memory ladder.
  - **2006, Cor. 1:** every `ξ ≠ 0` has a limit point of `‖ξ(3/2)^n‖` at most `(1 + T(2/3))/4 ≈ 0.2856`.  So `β* := sup_ξ inf_n ‖ξ(3/2)^n‖` lies in `[5/48, 0.2857)` in the literature, and in `[0.1227, 0.2857)` with our certificate.  Lean: `Literature.Dubickas2006`, `Literature.Dubickas2008`.
  - **2010:** new bounds only for `p = 2q - 1` with `q ≥ 3` and for `p ≥ 2q + 1`.  Nothing new for `3/2`.
- **Unread:** Bugeaud 2012, ch. 3 (§3.6, "constructions of pairs `(ξ, α)`… in a prescribed interval").  It postdates Dubickas 2008, and no later paper citing 2008 improves 5/48, so the risk is that the book itself carries an unpublished improvement.
- **Cardinality:** every start `m₀ ≥ 1` in a winning residue class gives a `ξ` in `[m₀, m₀ + 1)`, so the certificate already yields infinitely many `ξ`, matching Dubickas's statement.  Uncountability (Pollington's form) still needs the branching game.

## Next

1. Lean: prove `exists_trapped_of_winningStrategy` and instantiate the certificate (finite rational checks).  Treadmill-ready.
2. Uncountability: a variable-width game (widths `l, l/2, ...`) with a branching state.  A positive Hausdorff dimension bound would follow from the branching rate.
3. Sharpen β: a finer width grid and larger `k`.  The observed `≈ 0.124` suggests room.
4. Outward: written 2026-10-06, [`docs/notes/arc-traps-two-thirds-edge.md`](docs/notes/arc-traps-two-thirds-edge.md) (Trevor writes the pointer).
