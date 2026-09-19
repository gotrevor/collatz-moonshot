# HANDOFF 2026-09-19 — adjacent-swap numerator law, residue transport, antitonicity refuted

Bounded helper lap per the newest attended override in `DIRECTION.md` (2026-09-18 late).
Done; **no successor lap**.

## Checkpoint
* Branch `main`; `lake build` green (full build, exit 0). No push.
* Only new files: `CollatzMoonshot/FrontA/FirstCrossingSwaps.lean`, its root import
  (`CollatzMoonshot.lean` line 57), and this handoff. No existing statement or
  definition touched; experiments untouched.

## What landed (all three frozen targets, verbatim)
```
numer_adjacent_swap (u w : List Bool) :
  numer (u ++ [false,true] ++ w) = numer (u ++ [true,false] ++ w) + 2^u.length * 3^ones w
residue_adjacent_swap {x y m} (u w) (hx : traceWord x m = u ++ [true,false] ++ w)
    (hy : traceWord y m = u ++ [false,true] ++ w) :
  3^(ones u + 1) * y + 2^u.length ≡ 3^(ones u + 1) * x [MOD 2^m]
numeratorAntitoneResidue_false : ¬ NumeratorAntitoneResidue
```
`#print axioms`:
* `numer_adjacent_swap` → `[propext, Quot.sound]`
* `residue_adjacent_swap` → `[propext, Classical.choice, Quot.sound]`
* `numeratorAntitoneResidue_false` → `[propext, Classical.choice, Quot.sound]`

No `sorry`, no citation axiom, no `native_decide` (the counterexample uses kernel
`decide` after `unfold At`).

## Mathematical content
The swap law needs **no induction**: `numer_append` splits off the prefix `u`, and the
two blocks `01`/`10` have equal `ones`, so the `3 ^ ones` weight on `numer u` is common.
Locally `numer ([false,true] ++ w) = 4·numer w + 2·3^ones w` and
`numer ([true,false] ++ w) = 4·numer w + 3^ones w`, a gap of exactly `3^ones w`, lifted
by `2^u.length`.

For transport: both iterate identities give `3^a·· + numer ≡ 0 [MOD 2^m]` with
`a = (ones u + 1) + ones w`. Substituting the swap law and cancelling the common
numerator (`Nat.ModEq.add_right_cancel'`) yields
`3^a·y + 2^|u|·3^ones w ≡ 3^a·x`, which factors as `3^ones w · (…)` on both sides;
`3^ones w` is a unit mod `2^m` (`Nat.ModEq.cancel_left_of_coprime`). The suffix `w`
drops out entirely — the relation depends only on the prefix.

Counterexample: `x = 95`, `y = 175`, `m = 8`; traces `11111000` and `11110100` (one
adjacent swap apart), numerators `211` and `227`. Both are first crossings (`At _ 8`),
`211 ≤ 227`, yet `175 > 95`. So the first-crossing numerator carries no order
information about the starts, and `residue_adjacent_swap` is genuinely only a
congruence, not an inequality.

This does **not** prove CST. The two open inputs remain `StoppingCorrect` and
`CrossingExists`.
