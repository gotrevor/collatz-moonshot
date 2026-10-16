# KICKOFF 2026-10-15: residue traps, Theorem V, avoidance, sign-blind gate (research §55)

Repo `collatz-moonshot-amusical-zcore` (branch `wip/amusical-trap`): close every `sorry` in
`CollatzMoonshot/AmusicalTrap.lean`.

## Ratified, do not change

Every statement and definition in `AmusicalTrap.lean` (`permOrbit`, `InfinitelyManyInfiniteOrbits`,
`amusicalV`, `amusicalVInv`, `amusicalVPerm`, `signCollatz` and all theorem statements).  No
`native_decide`, no new axioms.  Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.
Commit after each proved lemma.  Notes as you go in `HANDOFF-amusical-trap.md`.  Helper lemmas are
welcome (put them above their first use).

## Paper proofs (Ren)

* **`permOrbit_injOn_entry`.**  Forward invariance: `σ^k x ∈ C` for `x ∈ C`, `k : ℕ`.  If entry
  points `x, y` share an orbit, `y = σ^j x` for some `j : ℤ`; by symmetry take `j ≥ 0`.  If `j > 0`
  then `y = σ (σ^{j-1} x)` with `σ^{j-1} x ∈ C`, so `y ∈ σ '' C`: contradiction.  So `j = 0`.
  (`permOrbit σ x = permOrbit σ y` gives `y ∈ permOrbit σ x` via `j = 0` membership.)
* **`permOrbit_infinite_of_entry`.**  If the orbit were finite, `x` is periodic: `σ^p x = x` with
  `p ≥ 1` (finite orbit of a permutation ⇒ some `σ^p x = x`, `p > 0`; e.g. pigeonhole on
  `k ↦ σ^k x`, `k : ℕ`, then cancel).  Then `x = σ (σ^{p-1} x) ∈ σ '' C`: contradiction.
* **`infinitelyManyInfiniteOrbits_of_trap`.**  The map `x ↦ permOrbit σ x` is injective on the
  infinite set of nonnegative entry points, and lands in the target set by the previous lemma.
  `Set.Infinite.image` + `Set.Infinite.mono`.
* **`amusicalV` inverse pair, `amusicalV_eq_amusical`, `amusicalV_even_trap`.**  Case on residues
  (`n % 8`, `m % 6`) and `omega` (expand `Int.emod_emod_of_dvd`, `Int.ediv_add_emod`).  Python-checked
  on `[-10^5, 10^5)`.
* **`amusicalV_entry_iff`.**  `V(2e) = 6e + 2`, so `V(evens) = 2 (mod 6)`: `x = 6m + 2` is
  `V (2m)`, and nothing `≢ 2 (mod 6)` is an image of an even.  Even and `≢ 2 (mod 6)` is
  `x % 6 = 0 ∨ x % 6 = 4`.
* **`amusicalV_infinitelyManyInfiniteOrbits`.**  Trap theorem with `C` = evens; the entry points
  `{x ≥ 0 | x % 6 = 0}` are infinite (e.g. `Set.infinite_of_not_bddAbove`, or the image of `ℕ`
  under `n ↦ 6n`).
* **`amusical_visits_zero_three_five`.**  Suppose `U^k x % 8 ∈ {1, 2, 4, 6, 7}` for all `k ≥ k₀`.
  Residue dynamics (`amusical` in `Amusical.lean`: `2m ↦ 3m`, `4m+1 ↦ 3m+1`, `4m+3 ↦ 3m+2`): an odd
  `n ≡ 1, 7 (mod 8)` maps to an odd number (`n = 4m+1`, `m` even ⇒ `3m+1` odd; `n = 4m+3`, `m` odd ⇒
  `3m+2` odd); `4 (mod 8)` maps to an even `≡ 2, 6`; `2, 6 (mod 8)` map to odds.  So from `k₀ + 2`
  on, every iterate is odd and `|U y| ≤ |y|` with `|U y| < |y|` unless `|y| ≤ 1` (`|3m+1| ≤ |4m+1|`,
  `|3m+2| ≤ |4m+3|`).  So the forward orbit is bounded, takes finitely many values, two iterates
  coincide, and injectivity (`amusical_injective`) makes `x` periodic, so `amusicalOrbit x` is finite
  (it is the finite set of forward iterates: for a periodic point `(amusicalPerm ^ j) x` depends on
  `j mod p`).  Contradiction with `hx`.
* **`signBlind_gate`.**  `ε y := y < K ∨ y % 4 = 3` (as a `Bool` via `decide`).  Start
  `x := 4K + 3`.  Invariant: the iterate `y` is odd and `y ≥ x`.  If `y % 4 = 3`, `ε y`, and
  `(3y+1)/2` is odd; if `y % 4 = 1` then `y ≥ K` so `¬ ε y`, and `(3y−1)/2` is odd.  Either way the
  next value is `≥ (3y − 1)/2 ≥ y + 1`.  So `y_k ≥ x + k` and the orbit tends to `atTop`.
* **`signCollatz_minus_cycle`.**  `5 → 7 → 10 → 5`: `decide` or `simp [signCollatz]`.

Any cleaner route is fine as long as the ratified statements are unchanged.
