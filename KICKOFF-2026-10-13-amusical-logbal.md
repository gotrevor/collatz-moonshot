# KICKOFF 2026-10-13: log-weighted balance of unions of orbits (amusical)

Repo `collatz-moonshot-amusical-logbal`: close every `sorry` in
`CollatzMoonshot/AmusicalLogBalance.lean`.

## Ratified, do not change

All statements in that file and `logWeight`.  Everything else in the repo is read-only.  Helpers go
in your own file or `CollatzMoonshot/AmusicalLogBalance/*.lean`.  No `native_decide`, no new
axioms; `decide +kernel` is fine.  Lean lines ≤ 100 characters.

## Paper proofs

Write `e N = logWeight (S ∩ evens) N`, `o N = logWeight (S ∩ odds) N`, `W = e + o`.
`S` is `U`-invariant both ways (`hS`), and `U` maps positive integers to positive integers.

1. **Evens to multiples of 3.**  `n ↦ 3n/2` is a bijection from `{n ∈ S, 2 ∣ n, 1 ≤ n ≤ N}` onto
   `{m ∈ S, 3 ∣ m, 1 ≤ m ≤ 3⌊N/2⌋}` (use `amusical (2k) = 3k`, `hS`, and `amusicalInv`), and
   `1/m = (2/3)(1/n)`.  So `logWeight (S ∩ 3ℤ) (3⌊N/2⌋) = (2/3) e N` exactly.
2. **Odds to non-multiples of 3.**  `U (4k+1) = 3k+1`, `U (4k+3) = 3k+2` biject the odds of `S` in
   `[1, N]` onto the non-multiples of `3` of `S` in `[1, M]` for the matching `M ≈ 3N/4` (handle the
   cutoff with an explicit inequality: every odd `n ≤ N` maps to `≤ (3N+1)/4`, every non-multiple
   `m ≤ (3N−3)/4` comes from an odd `n ≤ N`).  Per term `|1/U n − 4/(3n)| ≤ 4/(3n(3n−1))`, total
   `≤ 1/2` (dominated by `n = 1`: `|1 − 4/3| = 1/3`, then `Σ_{n≥3} 4/(9n²−3n) < 1/6`).
3. **Cutoff shifts.**  Tails `Σ_{A < m ≤ B} 1/m ≤ log(B/A) + 1/A`; use crude bounds
   `log(3/2) < 1/2`, `log(4/3) < 1/3` (or bound the tails by `(B − A)/A` directly).
4. Combine: `W = (2/3) e + (4/3) o + E` with `|E| < 1`, and `W = e + o`, so `|e − o| < 3`; then
   `|e − W/2| = |e − o|/2 < 3/2 ≤ 3`.  For multiples of 3: `logWeight (S ∩ 3ℤ) N = (2/3) e − a`
   with `0 ≤ a ≤ 1`, so `|(2/3)e − a − W/3| ≤ |e − o|/3 + 1 ≤ 2 ≤ 3`.
5. **`amusicalInfinitelyManyOrbits_of_logDensityZero`.**  If the orbits of nonnegative integers
   form a finite set `{O_1, …, O_k}`, every `n ∈ [1, N]` lies in some `O_i`, so
   `Σ_i logWeight O_i N ≥ Σ_{n=1}^N 1/n ≥ log (N+1)`; dividing by `log N` and taking limits
   contradicts `Tendsto … (nhds 0)` for all `i` (finite sum of limits).  Mathlib: harmonic lower
   bound `Real.log_le_harmonic`-style lemmas (`log (n+1) ≤ harmonic n`).

Notes for the next lap go in `HANDOFF-amusical-logbal.md`.
