# KICKOFF 2026-10-13: global mechanisms (amusical)

Repo `collatz-moonshot-amusical-global`: close every `sorry` in `CollatzMoonshot/AmusicalGlobal.lean`.

## Ratified, do not change

All statements and definitions in that file.  Everything else in the repo is read-only.  In particular,
`AmusicalWindowThree.lean` and `AmusicalEscape.lean` are owned by other treadmills: use their statements
(e.g. `amusical_periodic_mem`, `abs_amusical_le`), never edit them.  A `sorry` inherited through them
is fine.  Helpers go in your own file or in `CollatzMoonshot/AmusicalGlobal/*.lean`.  No
`native_decide`, no new axioms; `decide +kernel` is fine.  Lean lines ≤ 100 characters.

## Paper proofs (agent report global.md; docstrings carry the outlines)

Order: Lemma K first, then the finite-solutions lemma, then the commuting mechanism, then
`commuting_window_two`, Proposition S, and Proposition P.

1. **`abs_le_four_pow_mul_iterate_sub`.**  Induct on ℓ with the cylinder affine form:
   `2^(B_ℓ) Uˡ x = 3ˡ x + c_ℓ` with `|c_ℓ| ≤ ∑_{j<ℓ} 3^(ℓ−1−j) 4^j < 4^ℓ` and `B_ℓ ≤ 2ℓ`.
   * Then `2^B (Uˡ x − x) = (3ˡ − 2^B) x + c`, with `|3ˡ − 2^B| ≥ 1` (parity).
   * Backward: `3ˡ U⁻ˡ y = 2^B y − c'`, same bound.
   * `fwdBits` and `bwdBits` in `AmusicalEscape.lean` are the bit counts, if useful.
2. **`amusical_iterate_eq_add_finite`.**  Lemma K bounds every solution by `4^ℓ (|d| + 1)`.
3. **`infinitelyManyOrbits_of_commuting`.**
   * `g` commutes with `U⁻¹`: apply `amusical_injective` to `U (g (U⁻¹ n)) = g n`.
   * So `g '' amusicalOrbit m = amusicalOrbit (g m)`, and strict monotonicity makes `g m` the minimum
     of the image orbit.
   * The orbits of `gᵏ m` are pairwise distinct: their minima strictly increase.
4. **`commuting_window_two`.**
   * Reduce to a decidable table check: `g` maps each of the nine cycle representatives
     (`0, ±1, ±2, ±4, ±44`) to an integer `y` with `amusical^[p] y = y`.
   * `amusical_periodic_mem` then gives `|y| ∈ knownCycleMembers`.
   * The forward itinerary of `y` is the block code of the cycle's.  Of the `3⁹` tables, exactly
     seven are consistent (`scripts/amusical/central_w2.py`).
   * The table then determines `g`, by the `reversor_eq_of_stepSym_eq` argument with `U` in place
     of `U⁻¹`: the forward itinerary of `g n` is computable from `n`.
5. **`infinitelyManyOrbits_of_survival`.**  First prove the forward one-sided window density.
   * `{n : ∀ t ∈ [1, L], n ≤ Uᵗ n}` has natural density `fwdSurv L`; this is the forward half of
     the `windowMinDensity` proof, and likewise backward.
   * Then do the set algebra in the docstring.
   * Conclude with `amusicalInfinitelyManyOrbits_of_minima`: survivors in both directions are orbit
     minima, and a positive lower density makes the set infinite.
6. **`exists_many_returns`.**  The docstring sketch.  The transitivity step: in `ℤ/M₀`, the branch
   maps `z ↦ 3z/2, (3z+1)/4, (3z−1)/4` generate all translations, since `g_A⁻¹ ∘ g_B` is
   translation by `−2/3`.  Simpler routes are welcome.  For example, for `x` in a class mod
   `2^e 3^f M₀` with prescribed itinerary, choose the word greedily.

Notes for the next lap go in `HANDOFF-amusical-global.md`.
