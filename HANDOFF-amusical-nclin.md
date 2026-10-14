# HANDOFF: amusical near-cycle law (ncnull, research §37)

- Branch: `wip/amusical-nclin`.  Kickoff: `KICKOFF-2026-10-14-amusical-nclin.md`.
- Target file `CollatzMoonshot/AmusicalNearCycleLaw.lean`: 0 sorries.  `NearCycleAt`,
  `LinearNearCycleLaw` and the five statements unchanged (import line, proof bodies and
  docstrings only).  The only edit outside the new files: `amusical_iterate_affine` in
  `AmusicalGlobal.lean` is no longer `private` (as the kickoff allowed).
- All five (`nearCycleStart_mono`, `nearCycleAt_equation`, `finite_nearCycleAt`,
  `card_fwdSurvivor_block_le`, `infinitelyManyOrbits_of_linearNearCycleLaw`) depend only on
  `[propext, Classical.choice, Quot.sound]`.

## How

Helpers in `CollatzMoonshot/AmusicalNearCycleLaw/Block.lean`, namespace
`CollatzMoonshot.Amusical.NearCycleLaw`.

- `nearCycleStart_mono_aux`: `Nat.find` on the first re-entry of `[0, p + D']`, as in the kickoff.
- T1: `amusical_iterate_affine` and `linear_combination -heq`.
- T2: **deviation**, simpler than the kickoff: Lemma K (`abs_le_four_pow_mul_iterate_sub`, already
  public) gives `p ≤ 4ᵍ (|Uᵍ p − p| + 1) ≤ 4ᵍ (D + 1)` directly; T1 is not needed.
- NCU (`card_fwdSurvivor_block_le_nat`): adapted from `NearCycle.card_fwdSurvivor_le`.  Split the
  block's survivors into orbit minima (`≤ r`), rungs whose predecessor `p` is in `(Y, 2Y)` with gap
  `≤ D` (injectively near-cycle starts in `Ioo Y (2Y)`), and the rest (gap `> D` or `p ≤ Y`).
  **Deviation:** the "rest" is `D`-separated on each orbit even with the `p ≤ Y` rungs included
  (for `a < b` on one orbit, `a ≤ p_b` by P′, and `p_b ≤ Y < a` is impossible), so no separate
  count of first-in-block survivors is needed.  `card_le_of_sep` with `X = 2Y + 1` gives
  `2r + r⌊(2Y+1)/D⌋ + #NC`, then `N = 3r`.
- LIN corollary: `exists_card_nearCycleStart_le` (eventually `< (κ+1) D` from the limit; below the
  threshold `D₀ + 1` by monotonicity, so `K = max ⌈κ+1⌉ #NC_{D₀+1}`), then NCU at `D = ⌈√Y⌉`,
  `C = 3N + 2K`.

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-nclin`.
