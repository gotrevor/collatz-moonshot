# KICKOFF 2026-10-14: forward survivors on the powers of 2 (amusical, rayfs)

Repo `collatz-moonshot-amusical-ray`: close every `sorry` in `CollatzMoonshot/AmusicalRay.lean`.

## Ratified, do not change

`ConjP2` and the eight theorem statements.  `ConjP2` is an open conjecture: do not try to prove
it.  Everything else is read-only (you may remove `private` from a helper if needed).  No
`native_decide`, no new axioms, no `decide` over more than a few thousand cases.  Lean lines ≤ 100
characters.  **Commit after every proved target.**  Do **not** edit `RESEARCH-*.md` (another
branch is appending to it).

## Paper proofs (agent "rayfs", research §34)

* `amusical_lt_of_odd`: `y = 4n + 1` gives `3n + 1 < 4n + 1` (`n ≥ 1`); `y = 4n + 3` gives
  `3n + 2 < 4n + 3`.  Use `amusical_four_mul_add_one`, `amusical_four_mul_add_three`.
* `not_fwdSurvivor_of_odd`: `t = 1`.
* `staircase_fwdSurvivor_iff`: `amusical_iterate_staircase` gives `U^(s−b) p_b = 3^s y` with
  `s − b ≥ 1`.  ⇒: `t ↦ s − b + t`.  ⇐: for `t ≤ s − b` the staircase points are `≥ p_b` (as in
  `staircase_fwdSurvivor`, which is this direction with `a = s − b`); beyond, the hypothesis.
* `threeSmooth_fwdSurvivor_infinite_iff`: ⇐ is the subset `n = 2^s`.  ⇒: a `3`-smooth forward
  survivor `2^a 3^b` gives `FwdSurvivor (2^(a+b))`.  If `a ≥ 1`, use the iff with `s = a + b`,
  `y = 1` (the point `2^a 3^b` survives, so `2^(a+b) = p_0 ≤ p_b ≤ U^t(3^s)`, and ⇐ again).  If
  `a = 0`, `3^b` survives and `2^b < 3^b`, the same argument.  Each `s` comes from at most `s + 1`
  pairs `(a, b)`, so infinitely many `n` give infinitely many `s` (`Set.Infinite` via a finite-fiber
  map `n ↦ a + b`, or contrapose with `Set.Finite.biUnion`).
* `amusical_iterate_add_one_ge`: one step `4 (U y + 1) ≥ 3 (y + 1)` for `y ≥ 0` (three branches:
  `3n + 1 ≥ (6n + 3)/4`, `3n + 2 ≥ 3n + 3/2`, `3n + 3 = 3n + 3`), and `U` keeps `y ≥ 0`
  (`amusical_nonneg` or similar; else prove it).  Induct on `t`.
* `pow_two_drop_bound`: `Function.iterate_add_apply`, `amusical_iterate_staircase` with `a = s`,
  `b = 0`, `y = m` (`U^s (2^s m) = 3^s m`), then the previous lemma at `3^s m ≥ 0`.
* `infinitelyManyOrbits_of_pow_two_orbitMin`: two orbit minima on one orbit are equal (each is `≤`
  the other), so `s ↦ amusicalOrbit (2^s)` is injective on the set; copy the bookkeeping of
  `infinitelyManyOrbits_of_powers` (`AmusicalPowers.lean`).
* `ray_two_of_conjP2`: the set is `Set.univ`.

Notes for the next lap go in `HANDOFF-amusical-ray.md`.
