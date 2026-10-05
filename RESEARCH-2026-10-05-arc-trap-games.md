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

**Exact barrier evidence (complete minimax, exact rationals).**  Bigger windows dominate, so the constructor's best move is a whole component of `W ∩ (arc lifts)`.  Starting from the full arc dominates every start.  The game is: the adversary reveals the current parity, the constructor picks a component, and the window becomes `1.5 · component + d`.  At `β = 0.1229, 0.124, 0.13, 0.15` the constructor is forced out at depths 26, 19, 14, 9.  At 0.1200 and 0.1228 it survives until the 300 s timeout.  This is a proof, for those `β`, that just-in-time adversarial parity loses.  It does not yet cover strategies that know parities several steps ahead (the `k`-memory games).  Scratch scripts are `minimax.py` and `pv.py` in the session scratchpad; promote them into `experiments/` when the barrier is pursued.  That theorem would be a **barrier: no strategy that treats unseen parity bits as adversarial beats 7/57.**  It would cover Dubickas's Lemma 1.4 game as well (5/48 < 7/57).

**Reading.**  The literature window is `[5/48, 0.2857)`.  Adversarial-parity constructions top out at `7/57 ≈ 0.1228`.  Above that, a construction must use the integer arithmetic of `m`, i.e. the bits beyond the horizon, not treat them as noise.  The note's Mahler section is the same story: bounded lookahead buys nothing.

## What the ladder says about Mahler

For arcs `[0, t]` (Mahler's position) the shortest winnable `t` is 0.857 at `k = 0, 1` and 0.827 at `k = 2..6`.  Bounded 2-adic memory saturates after two bits, far above Mahler's 1/2.  Every Z-number construction would have to sit in FLP's decoupled regime (`t ≤ 1/2`).  There the integer parts are forced (at most one `ξ` per unit interval), so a finite-memory strategy has nothing to steer.
- **Observation, not theorem:** no `k`-memory strategy wins any arc of length `≤ 1/2`.  A first proof attempt ("the child's integer offset `j` is forced") is incomplete, because the continuous choice of `a` can still move later `j`s.  A Lean `sorry` statement waits on a real argument.
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
4. Outward: a standalone `docs/notes/` result file once the Lean proof lands (Trevor writes the pointer).
