# HANDOFF amusical-rayjoin (2026-10-15)

Branch `wip/amusical-rayjoin`.  Target: every `sorry` in `CollatzMoonshot/AmusicalRayJoin.lean`.

## Done
* `ray_join_three`, `ray_join_four`: `decide +kernel` (no axioms at all).
* `no_early_ray_join` (Theorem J given `EllisonBound`): proved; `#print axioms` shows
  `propext, Classical.choice, Quot.sound` only.  Statements and `EllisonBound` unchanged.
* Route (tighter than the kickoff sketch, no `m ≥ 17` threshold needed):
  - `amusical_iterate_affine` gives `2^X = 3^Y + c`, `X = B + m'`, `Y = k + m`, `|c| < 4^k`.
  - `2·4^k ≤ 3^Y` (squares: `4·16^k ≤ 9·27^k ≤ 3^(2Y)`), so `2^(X+1) > 3^Y`.
  - `eight_mul_ge`: `8X ≥ 19k + 4`, from `27^4 = 531441 ≥ 2^19`.
  - Split on `Y ≤ 17`: `fin_check` (kernel `decide`, all `(m, k)` with `k + m ≤ 17`) shows
    `2^40 % U^k(3^m) ≠ 0`, while `m' ≤ 40` forces `2^m' ∣ 2^40`.
  - `Y ≥ 18`: `3^18 > 2^28` gives `X ≥ 28`, outside Ellison's set; logs give
    `X(log 2 − 1/10) < 2k log 2`, contradicting `8X ≥ 19k + 4` since `3 log 2 > 1.9`.
* Module added to the root `CollatzMoonshot.lean`; full `lake build` green.

## Next
* Host: push and merge.  Conjecture J (joins only from `3^1..3^4`) stays open; the margin
  `3 log 2 − 1.9` shows Theorem J's range `k ≤ 2m − 2` is near the limit of this method.
