# KICKOFF 2026-10-14: the tail threshold and τ_odd (amusical, Theorem TT / T1★)

Repo `collatz-moonshot-amusical-oddrewire`: close every `sorry` in `CollatzMoonshot/AmusicalOddRewire.lean`.

## Ratified, do not change

`FwdSurvivorOf` and the three theorem statements.  Everything else is read-only, except that you
may generalize (not weaken) the internals of `AmusicalSeventh/Rewire.lean` (`sparseOrbitCuts`,
`sparselyRewiredPerm`, …) or copy-and-generalize them into `CollatzMoonshot/AmusicalOddRewire/*.lean`.
Copying into new files is preferred, so `rewire_single_orbit` and its dependents keep building
unchanged.  No `native_decide`, no new axioms, no `decide` over more than a few thousand cases.
Lean lines ≤ 100 characters.  **Commit after every proved target.**

## Order

1. `fwdSurvivor_three_separation_of` (warm-up): copy `fwdSurvivor_three_separation`
   (`AmusicalSurvivorSeparation.lean`), replacing `amusical_two_mul` by `h2` and `amusicalInv` by
   `τ.symm` (`τ.symm (3m) = 2m` from `h2`).
2. The gluing lemma GL, as a parameterized `rewire_single_orbit`: for `σ : Equiv.Perm ℕ`, a set of
   infinite orbits `𝒢` and cut sets `S`, where every orbit in `𝒢` meets `S` at unboundedly late and
   early times, there is `τ` that equals `σ` off `S` and off the orbits in `𝒢`, and fuses `𝒢` into
   one orbit.  For T1★, also: every changed point is `≥ Y_k` at stage `k`, at most `2k` change at
   stage `k`.  Choose `Y_k` with `F N ≥ k(k+1)` for `N ≥ Y_k`.  The existing trail construction
   never looks at the cut predicate, so its connectivity proofs should transfer.
3. `exists_oddRewire` (T1★): GL with `S` = odd naturals and `𝒢` = all infinite orbits.  It needs
   "no `S`-free tail": forward, `∀ x ≠ 0, ∃ j ≤ v₂ x, Odd (amusical^[j] x)`; backward, the backward
   orbit of an infinite orbit is unbounded, and `amusicalInv (3q + r) = 4q + 2r − 1` is odd for
   `r ∈ {1, 2}`.  If `U` has at most one infinite orbit, `τ = U`.  `τ(2m) = 3m` holds because only
   odd points change.
4. `tail_threshold` (TT).  ⇐: an `S`-free forward tail `{Uʲ y}` is a forward `τ`-ray; two disjoint
   forward rays never lie in one `τ`-orbit (if `b = τ^j a`, the rays meet), and they are infinite.
   Backward tails are symmetric.  ⇒ by contraposition: if only finitely many orbits have `S`-free
   tails, glue all the others by GL; the result has finitely many infinite orbits.

## Lemma plan (agent "oddbranch", §A.5)

### A.5 Lean decomposition (each lemma ≤ 40 lines; staged names cited)

1. `fwdSurvivor_three_separation_of` (25 lines).  The statement of `fwdSurvivor_three_separation`
   for any `τ : Equiv.Perm ℤ` with `∀ m, τ (2*m) = 3*m`, and `FwdSurvivor` read for `τ`.  The proof
   is the staged one with `amusical_two_mul` replaced by the hypothesis.
2. `staircase_fwdSurvivor_of` (30 lines).  `amusical_iterate_staircase` and `staircase_fwdSurvivor`
   under the same hypothesis.
3. `exists_late_odd` (20 lines).  `∀ x ≠ 0, ∃ j ≤ v₂ x, Odd (amusical^[j] x)`.  Induct on `v₂`
   using `amusical_two_mul`.
4. `exists_early_odd` (35 lines).  For `x` with infinite orbit and every `T`, `∃ t ≥ T,
   Odd (amusicalInv^[t+1] x)`.
   * The backward orbit is unbounded by `iterate_orbit_injective_of_aperiodic` and
     `eventually_abs_ge_of_injective`.
   * So `amusicalInv` increases at some `t ≥ T`.  Case `x % 3`: an increase is not on `3ℤ`, and
     `amusicalInv (3q+r) = 4q+2r−1` is odd for `r ∈ {1, 2}`.
5. `orbit_ne_of_disjoint_rays` (30 lines).  If two forward `τ`-rays from `a` and `b` are disjoint,
   then `b ∉ τ`-orbit of `a`.  If `b = τ^j a` with `j ≥ 0`, the rays meet at `b`; if `j < 0`, they
   meet at `a`.  The backward version is symmetric.
6. **GL** `exists_glue_at` (the only large item).
   * Generalize `rewire_single_orbit`'s internals (`sparseOrbitCuts σ`, `sparselyRewiredPerm`,
     `sparselyRewiredPerm_connects_infinite_orbits`, `sparselyRewiredPerm_eq_of_finite_orbit`) from
     "cut at the first passage" to "cut at the first time `≥` the previous cut lying in
     `S_k ∩ [Y_k, ∞)`".
   * The trail and connectivity proofs never look at the cut predicate, so this is a parameter
     change.
   * New sub-lemmas: `cut_mono` (15 lines), `junction_same_stage` (6 cases, 6 × 8 lines),
     `support_card_le` (35 lines, by `Finset.card_biUnion_le` over stages).
7. `tail_threshold` (TT; 40 lines on GL, 3, 4 and 5).
   * `(∀ τ, (∀ n ∉ S, τ n = U n) → InfinitelyManyInfiniteOrbits τ) ↔
     ({O | ∃ x ∈ O, ∀ j, U^[j] x ∉ S}.Infinite ∨ {O | ∃ x ∈ O, ∀ j ≥ 1, V^[j] x ∉ S}.Infinite)`,
     with `O` ranging over infinite `amusicalOrbit`s.
8. `exists_oddRewire` (T1★; 25 lines): TT's ⇐ data with `S = {n | Odd n}`, using 3 and 4.
9. `ng_star` (NG★; 40 lines): GL with `S_k = {n | n ≡ 1 [ZMOD 6^max k 2]}` and `Int.ModEq`
   arithmetic.


Notes for the next lap go in `HANDOFF-amusical-oddrewire.md`.
