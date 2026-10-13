# KICKOFF 2026-10-13: window-3 reversors (amusical)

Repo `collatz-moonshot-amusical-w3`: close every `sorry` in `CollatzMoonshot/AmusicalWindowThree.lean`.

## Ratified, do not change

All statements in that file.  Everything else in the repo is read-only; in particular
`AmusicalEscape.lean` is owned by another treadmill (you may use its proved `abs_amusical_le`,
`abs_amusicalInv_le`, not its open targets).  Helpers go in your own file or in
`CollatzMoonshot/AmusicalWindowThree/*.lean`.  No `native_decide`, no new axioms; `decide +kernel` is
fine.  Lean lines ≤ 100 characters.

## Data

* `scripts/amusical/w3check.py`: independent re-derivation.  It finds the cycles, the 24 partial
  rules, and confirms none of the 216 completions is surjective.
* `scripts/amusical/w3certs.txt`: the 25 constrained blocks `(a,b,c) = (stepSym (U⁻¹ n), stepSym n,
  stepSym (U n))`, the 24 partial rules (values on those blocks), and per completion an orphan word.
  * The two free blocks are `112` and `221`.
  * Orphan convention: `u` of length `L` such that for every `s : Fin (L+2) → Fin 3` there is `j < L`
    with `f (s (j+2)) (s (j+1)) (s j) ≠ u j`.
* `scripts/amusical/perbound.py`: every rational periodic point of period `p ≤ 12` has `|x| ≤ 483`.

## Paper proofs

1. **`amusical_periodic_mem`.**
   * Bound `|y|` first.  Iterating `abs_amusical_le` along the orbit gives
     `2^e |y| ≤ 3^p |y| + K_p`.  Iterating `abs_amusicalInv_le` gives `3^p |y| ≤ 2^e |y| + K'_p`.
     Here `e` is the bit count of the cycle word.  Since `2^e ≠ 3^p`, `|y| ≤ max(K_p, K'_p)`.
   * Any explicit bound works, even a crude one, as long as the final `decide +kernel` range stays
     feasible.  Alternatively, get the exact affine form `Uᵖ y = (3ᵖ y + N_w)/2^e` on the cylinder.
   * Then `decide +kernel` over `y ∈ [−B, B]`: `amusical^[p] y = y → |y| ∈ knownCycleMembers`,
     for each `p ≤ 12`.  `amusical_neg` gives the negatives.
2. **`exists_forward_itinerary`.**  Strengthen the induction hypothesis: the set of `m` with prefix
   `u` contains a full residue class mod `2^(bits u)`.
   * For the inductive step `s :: u`, the integers `z` with `stepSym z = s` have `U z` ranging over
     one class mod `3`.
   * Intersect that class with the class for `u` by CRT (`gcd(2^e, 3) = 1`), and pull back through
     the branch.
3. **`no_window3_bijective_reversor`.**
   * **Reversor algebra.**  `ι (U n) = U⁻¹ (ι n)` gives `ι (U⁻ʲ n) = Uʲ (ι n)`, and
     `ι (Uʲ n) = U⁻ʲ (ι n)`.
   * **Cycles to cycles.**  If `Uᵖ x = x` then `U⁻ᵖ (ι x) = ι x`, so `Uᵖ (ι x) = ι x`.  So by
     `amusical_periodic_mem`, `|ι x| ∈ knownCycleMembers` for each of the 41 cycle points `x`.
     * Injectivity makes the image of each cycle a cycle of the same exact length.
     * If `U^q (ι x) = ι x`, then `ι (U^q x) = U⁻^q (ι x) = ι x`, so `U^q x = x`.
   * **Forced values.**  For each cycle point `x`, `stepSym (ι x) = f (window of x)`.  Matching the
     image cycles determines `f` on the 25 blocks occurring in cycle windows, as one of the 24
     partial rules in `w3certs.txt`.
     * Organize this as you like: by the image of `44`, which is one of 24 points on the two
       12-cycles, then the 5-cycles, and so on.
     * Or state the 24-rule list as a `Finset` and prove membership by a decidable check over the
       finitely many cycle-to-cycle assignments.
   * **Orphans.**  For each completion, take its orphan `u`.  Let `m` have forward symbols `u` at
     positions `1..L` (`exists_forward_itinerary` applied to `0 :: u`, or shift by one).
     * By surjectivity, `m = ι n`.
     * Then `stepSym (Uʲ m) = stepSym (ι (U⁻ʲ n)) = f (s (j+1)) (s j) (s (j−1))` with
       `s i = stepSym (U⁻ⁱ n)`, which contradicts the orphan property.
   * Prefer a decidable formulation of "u is an orphan of f" (`∀ s : Fin (L+2) → Fin 3, …`) so
     each certificate closes by `decide`.

Notes for the next lap go in `HANDOFF-amusical-w3.md`.
