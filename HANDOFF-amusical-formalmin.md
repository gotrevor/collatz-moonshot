# HANDOFF: Proposition G1 proved; AmusicalFormalMin.lean sorry-free (2026-10-14)

## Result

Every target in `CollatzMoonshot/AmusicalFormalMin.lean` is proved.  `#print axioms` is
`[propext, Classical.choice, Quot.sound]` for `coarse_quasiInvariant_bounded`,
`TwoVisit.exists_two_visit`, `formalMin_unique`, `not_formalMin_of_periodic`, `formalMin_neg`,
`infinitelyManyOrbits_of_formalMin_infinite` and `formal_walk_disagrees`.  The ratified
statements and definitions are unchanged; the only edits to the file are the new import, the G1
proof and the G1 docstrings.

**Proposition G1** (`coarse_quasiInvariant_bounded`) does **not** use
`amusical_no_periodic_cone` (still a `sorry` owned by the antikohl treadmill), and it does not
use the irrationality of `log(3/2)/log(4/3)`.  Helpers are in
`CollatzMoonshot/AmusicalFormalMin/TwoVisit.lean`:

- `exists_two_visit`: for every `M`, `r`, `r'` and every large `s`, some `x ∈ [2ˢ, 2ˢ⁺¹)` with
  `x ≡ r` has `Uᴸ x ∈ [2ˢ, 2ˢ⁺¹)` and `Uᴸ x ≡ r' (mod M)`.
- `exists_balanced_word`: the word `pre · Eᵉ · conn · suf`.
  - The connector has a fixed shape (`exists_fixed_connector`: `q` translation units padded by
    identity blocks `B^{m!}` to one length, all odd steps), so its length and bit count do not
    depend on the residues.
  - `e` is the least number of even steps with `3ᴸ ≥ 2ᴮ` (found with `Nat.find`), so the slope
    is in `[1, 3/2)`.  This replaces the paper's density argument.
- `level_return`: slope in `[1, 3/2)` plus `2ˢ + 4ᴸ ≤ x`, `3x + 2·4ᴸ ≤ 4·2ˢ` brings `Uᴸ x`
  back into the block.
- `orbit_visits_block`: a positive aperiodic forward orbit visits every block above its start.
- `two_visit_uniform`: the same, uniform over `ZMod M × ZMod M` (`Filter.eventually_all`).

The modular connector machinery (`act`, `connectorCore`, `exists_forward_itinerary_local`, …)
is copied from the `private` section of `AmusicalGlobal.lean`, which is owned elsewhere.
`TwoVisit` imports `AmusicalWindow`, not `AmusicalGlobal`.  Importing `AmusicalGlobal` forced a
rebuild of stale `AmusicalWindowThree.*` oleans in this worktree.

## Build environment note

The host was fd-starved this lap: every `lake env lean` and many `lake build` attempts died
with `Too many open files` while loading mathlib oleans from the virtiofs mount.  For iteration
I copied all `LEAN_PATH` dirs to `/tmp/ll/<n>` (VM-native overlay fs) and ran
`LEAN_PATH=$(cat /tmp/ll/LEAN_PATH) lean <file>` (`/tmp/ll/lean.sh`).  The commit gate was a
real `lake build CollatzMoonshot.AmusicalFormalMin`: it succeeded on the second retry, with no
`declaration uses sorry`, and `#print axioms` was then rerun under `lake env lean`.

## Next

Nothing is open in this file.  A natural sequel is Proposition G2 (growing modulus
`M(s) | 2^∞3^∞N₀`, `log₂ M(s) ≤ s/10`).  Its bookkeeping is the explicit length of the word
built here: about `a + b + N₀!·(N₀ + 2(a+b) + 1) + e`.  The factorial connector is far too long
for G2, so G2 would need a connector of length `O(log M)`.
