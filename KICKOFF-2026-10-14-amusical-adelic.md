# KICKOFF 2026-10-14: the adelic extension (amusical)

Repo `collatz-moonshot-amusical-adelic`: close every `sorry` in `CollatzMoonshot/AmusicalAdelic.lean`.

## Ratified, do not change

All statements and definitions in that file (`amusicalRat` and both theorems).  Everything else in the
repo is read-only.  Helpers go in `CollatzMoonshot/AmusicalAdelic/*.lean`.  No `native_decide`, no new
axioms.  Lean lines ≤ 100 characters.  **Commit after every proved target.**

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.

## Suggested order

1. **`amusicalRat_intCast`.**  `(n : ℚ).den = 1`, `(n : ℚ).num = n`; unfold `amusical`, split on
   `n % 2`, `n % 4`, and push casts (`Int.cast_div` needs divisibility: use `Int.emod_emod_of_dvd`,
   `Int.ediv_add_emod`; or prove `(3 * n + 1) / 4 = ((3 * (n / 4) + 1 : ℤ) : ℚ)` from `n = 4 m + 1`).
2. **`amusicalRat_subgroup_one_mem` (Proposition L).**  Pick `x ∈ Λ`, `x ≠ 0`.  Induct on
   `padicValInt 2 x.num` (the 2-adic valuation, since `x.den` is odd): when `x.num` is even,
   `amusicalRat x = 3x/2 ∈ Λ`, with smaller valuation and still odd denominator.  At odd `x.num`,
   `x.num * x.den` is odd and `4 * amusicalRat x - 3 * x = ±1` lies in `Λ` (`AddSubgroup` closure under
   `nsmul`/`sub`; `zsmul_mem`).  `1 ∈ Λ` from `-1 ∈ Λ` by `neg_mem`.  Note `3 * x / 2` has the same
   odd denominator when `x.num` is even (`Rat.den` lemmas, or work with `x = n / d` via `Rat.num_div_den`).

Notes for the next lap go in `HANDOFF-amusical-adelic.md`.
