# HANDOFF: Gaussian relative complete (2026-10-13)

Lane G's primary predicate, `sorry-free:CollatzMoonshot/GaussianRelative.lean`, is met. Both
ratified target statements are proved without new axioms or `native_decide`.

## Concrete advance

`gauss_infinitely_many_orbits` is proved independently of Lane R's unresolved
`orbit_inter_fixedPoints_ncard_le_two`. The proof uses a shorter infinite-fiber argument:

1. If the set of Gaussian orbits were finite, infinite pigeonhole gives one orbit containing
   infinitely many distinct real-axis points `(n, 0)`.
2. Two distinct such points are conjugation-fixed and differ by a nonzero Gaussian iterate `k`.
   The proved `Amusical.reversing_zpow_fixed` therefore gives return time `2*k` at the first point.
3. The local helper `zpow_orbit_finite_of_period` realizes an integer-power orbit with a nonzero
   return time as the image of the finite integer interval `uIcc 0 (2*k)`, so that orbit is finite.
4. The injected image of the infinite pigeonhole fiber is both infinite and contained in that
   finite orbit, a contradiction.

The involution and reversal identities used in step 2 are proved locally from `conjPerm`,
`gaussPerm`, and their definitions. Thus the theorem depends on the proved reversal lemma but
on none of Lane R's three `sorry`-bearing targets.

## Verification

* `lake env lean CollatzMoonshot/GaussianRelative.lean` — succeeds; no `sorry` warning in the
  owned file (two style-only `letI` suggestions).
* `rg -n '^\s*(sorry|admit)\b|:=\s*(sorry|by\s+sorry)\b'
  CollatzMoonshot/GaussianRelative.lean` — no matches.
* `~/personal/bin/lean-green . --target CollatzMoonshot.GaussianRelative --axioms
  CollatzMoonshot.GaussianRelative.gauss_infinitely_many_orbits` — FORMALIZE-TIER GREEN, 8711
  jobs; axiom list exactly `[Classical.choice, Quot.sound, propext]`.
* `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 8844 jobs.
* `git diff --check` — clean before the handoff update.

## Current blocker and next attack

No Lane G blocker or next proof obligation remains. The host predicate is complete. Other
amusical files are owned by separate treadmill lanes and were deliberately not edited.
