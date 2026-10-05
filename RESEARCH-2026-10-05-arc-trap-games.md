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

**There is `ξ > 0` with `‖ξ (3/2)^n‖ ≥ 7349/61440 ≈ 0.1196` for every `n ≥ 0`.**  The previous record is Pollington's `4/65 ≈ 0.0615` (1981).  A literature check (FLP 1995, AFS, Akiyama 2008, Schleischitz 2017, Dubickas 2009) found nothing better; confidence it is unpublished is about 85%.
- Certificate: `experiments/arc_cert_beta_k2.json` (`k = 2`, `l = 23371/230400`, four residues with at most six intervals each).  `arc_trap_k.py certificate 2 7349/61440 60 OUT` regenerates it.
- Independent check: an exact constructor that knows `m` completely ran 250 steps from five starts (`m₀ = 4, 8, ..., 20`), with random valid choices.  It never got stuck, and every `ξ` had `‖·‖ ≥ 0.124`.
- Blind play (`k = 0`) reaches `β ≈ 0.0861` (`arc_cert_beta_k0.json`).  Remembering 2 bits reaches 0.1196, and `k = 3, 4` add nothing on the 60-width grid.
- Not yet shown: uncountability (that needs a branching strategy with variable widths), and the sharp constant (the width grid is coarse; observed orbits sit near 0.124).

## What the ladder says about Mahler

For arcs `[0, t]` (Mahler's position) the shortest winnable `t` is 0.857 at `k = 0, 1` and 0.827 at `k = 2..6`.  Bounded 2-adic memory saturates after two bits, far above Mahler's 1/2.  Every Z-number construction would have to sit in FLP's decoupled regime (`t ≤ 1/2`).  There the integer parts are forced (at most one `ξ` per unit interval), so a finite-memory strategy has nothing to steer.
- **Observation, not theorem:** no `k`-memory strategy wins any arc of length `≤ 1/2`.  A first proof attempt ("the child's integer offset `j` is forced") is incomplete, because the continuous choice of `a` can still move later `j`s.  A Lean `sorry` statement waits on a real argument.
- **Reading:** this is the horizon in constructive form.  Seeing `k` bits further helps only while the arc has slack (length `> 1/2`).  Mahler's arc has none, so the only way past is to know *all* the bits, i.e. the integer itself.  That is the countable, rigid regime where Z-numbers would have to live.

## Next

1. Lean: prove `exists_trapped_of_winningStrategy` and instantiate the certificate (finite rational checks).  Treadmill-ready.
2. Uncountability: a variable-width game (widths `l, l/2, ...`) with a branching state.  A positive Hausdorff dimension bound would follow from the branching rate.
3. Sharpen β: a finer width grid and larger `k`.  The observed `≈ 0.124` suggests room.
4. Outward: a standalone `docs/notes/` result file once the Lean proof lands (Trevor writes the pointer).
