# KICKOFF 2026-10-15: no amusical itinerary is base-3 normal (research §54)

Repo `collatz-moonshot-amusical-zcore` (branch `wip/amusical-normal`): close the `sorry` in
`CollatzMoonshot/AmusicalNotNormal.lean`.

## Ratified, do not change

The statement `not_tendsto_evenFrequency_third`.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved lemma.  Notes as you go in
`HANDOFF-amusical-notnormal.md`.

## Paper proof (Ren)

Suppose the frequency tends to `1/3`.  Since `1/3 < 2 − log₂ 3` (`≈ 0.415`),
`periodic_of_evenFrequency_lt` (`AmusicalEscape.lean`) gives `p ≥ 1` with `U^p m = m`.  Then the
count over `k = q·p` steps is `q·E` with `E` the even count over one period, so the limit is `E/p`,
hence `3E = p`.  Contradiction from the cycle:

* **Cycle identity.**  For each step `x ↦ U x`: even `2·U x = 3x`; odd `4·U x = 3x + ε`, `ε = ±1`.  Multiply
  around the cycle (all `x ≥ 1`, positivity is preserved by `U` on positive integers):
  `2^{2p − E} · ∏ x = 3^p · ∏_{even} x · ∏_{odd} (x + ε/3)`, i.e. `2^{2p−E} = 3^p ∏_{odd}(1 + ε/(3x))`.
  An integer form avoids reals: `2^{2p−E} · 3^{p−E}... ` choose whichever form is easiest; e.g. work
  with `∏ (4 U x) over odd x · ∏ (2 U x) over even x = ∏ (3x + ε)` and `∏ U x = ∏ x` over the cycle.
* **Bound.**  With `E = p/3`, odd count `2p/3`: `2^{5p/3} = 3^p ∏_{odd}(1 + ε/(3x)) ≤ 3^p ∏ (1 + 1/(3x))`.
  If every odd cycle element is `≥ 5`, each factor `≤ 16/15`, so `2^{5p/3} ≤ 3^p (16/15)^{2p/3}`,
  i.e. `32 ≤ 27 · (16/15)^2 = 30.72`: false.  (Cube both sides to stay in ℕ: `2^{5p} ≤ 3^{3p}·(16/15)^{2p}`.)
* **Small odd elements.**  So some odd cycle element is `1` or `3`.  `U 1 = 1` (cycle `{1}`, `E = 0`,
  so `3E = p` fails); `3 → 2 → 3` (cycle `{2,3}`, `p = 2`, `E = 1`, fails).  A cycle through 1 or 3 is
  one of these (the orbit of `m` is the cycle, and it contains 1 or 3).
Any cleaner route is fine as long as the ratified statement is unchanged.
