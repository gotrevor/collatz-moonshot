# HANDOFF 2026-10-14: powers of 3 separate orbits (Theorem P3 / P3′), DONE

- Branch: `wip/amusical-powers`.  Scope: `sorry-free:CollatzMoonshot/AmusicalPowers.lean`, met
  with a green scoped build.  The five ratified statements are unchanged (the only diff to them is
  `:= by` → `:=` on `powers_orbit_ne`).  `#print axioms` on all five targets:
  `[propext, Classical.choice, Quot.sound]`.
- Proved (all in `CollatzMoonshot/AmusicalPowers.lean`):
  - `powerAdmissible_window_point`: `Nat.find` on the least staircase point `≥ 2^L y`; that point
    has `b ≥ 2`, and its predecessor is below `2^L y`.
  - `powerAdmissible_survivor` (helper): that point is a forward survivor, divisible by `3`, and
    lies `s − b` steps below `3^s y`.
  - `powers_orbit_ne_of_pos` (P3 without `¬2 ∣ y`, `¬3 ∣ y`), with the ratified `powers_orbit_ne`
    as a wrapper.  `y` cancels before unique factorization is used
    (`two_pow_mul_three_pow_inj`, via `Nat.factorization`), so coprimality to `6` is not needed.
    The ratified statements therefore show unused-variable warnings for `hy2`/`hy3`.
  - `powers_not_periodic`, `infinitelyManyOrbits_of_powers`.
  - `PowerAdmissible.mono` and `card_le_of_powerAdmissible` (finitely many orbits ⇒ each window
    holds at most `#orbits` admissible exponents).
  - `infinitelyManyOrbits_of_powers_log` (P3′): the dyadic partition from the kickoff,
    `s ↦ (log₂ s, (s − 2^m) / (2^m / k + 1))` into `range (log₂ S + 1) × range k`.  Every block is
    admissible for the common `L = 2^m + (j + 1)(2^m / k + 1)`.  The constant is `C = r · k`.

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-powers`.  As the module docstring
says, P3/P3′ are reductions.  One admissible `s` already exhibits an infinite orbit, which is
Conway's open question, so the logarithmic count is no easier than that.
