# KICKOFF 2026-10-13: statistical twins (amusical)

Repo `collatz-moonshot-amusical-twin`: close every `sorry` in `CollatzMoonshot/AmusicalTwin.lean`.

## Ratified, do not change

All statements in that file, `twinW`, and the proved `twinW_eq`, `twinW_threeCycle`.  Everything
else in the repo is read-only.  Helpers in your own file or `CollatzMoonshot/AmusicalTwin/*.lean`.
No `native_decide`, no new axioms; `decide +kernel` is fine.  Lean lines ≤ 100 characters.

## Paper proofs

1. **`twinW_bijective`.**  Mirror `amusicalInv`: the inverse is `3m ↦ 2(m/3 − 1)` on multiples of
   3 (i.e. `m = 3k ↦ 2(k − 1)`), `3k+1 ↦ 4k+1`, `3k+2 ↦ 4k+3`.  Prove both compositions are the
   identity by `unfold; split_ifs; omega` as for `amusicalInv_amusical`.
2. **`amusical_no_threeCycle`.**  Bound first: if `U³ n = n` then `|n| ≤ 200` (each branch of
   `U³` is `n ↦ (27 n + b)/2^w` exactly on a class mod `2^w`, `3 ≤ w ≤ 6`, `|b| ≤ 40`; a fixed
   point satisfies `(2^w − 27) n = b`, and `2^w − 27 ∈ {−19, −11, 5, 37}` is nonzero).  A cheap
   route: `omega` after unfolding three times with case splits on residues mod 64, or prove
   `|U n − (3/2)n| ≤ 1`-style bounds.  Then `decide +kernel` over `n ∈ [−200, 200]`.
3. **`twinW_not_conj_amusical`.**  If `φ` is injective with `φ ∘ W = U ∘ φ`, then `x = φ 8`
   satisfies `U³ x = x` (`twinW_threeCycle`), so `U x = x` by item 2, i.e. `φ (W 8) = φ 8`, so
   `W 8 = 8` by injectivity, but `W 8 = 15`.

Notes for the next lap go in `HANDOFF-amusical-twin.md`.
