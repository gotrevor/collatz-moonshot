# HANDOFF: Gaussian relative, involution identity closed (2026-10-13)

Lane G owns only `CollatzMoonshot/GaussianRelative.lean`.  The primary host predicate remains
`sorry-free:CollatzMoonshot/GaussianRelative.lean`; it is not yet met.

## Concrete advance

`conj_gaussH_conj_gaussH` is proved without axioms or `native_decide`.  The proof freezes
`r = (a + 7*b) % 25`, derives `0 ≤ r < 25`, enumerates its 25 possible values, unfolds the two
applications of `gaussH`, and closes every exact-division branch with `norm_num` and `omega`.
The local `maxHeartbeats 2000000` is needed because the deliberately direct 25-class proof
normalizes the nested piecewise map; the checked run used about one minute.

The only remaining `sorry` in the owned file is `gauss_infinitely_many_orbits`.

## Verification

* `lake env lean CollatzMoonshot/GaussianRelative.lean` — succeeds; the sole owned-file warning
  is the remaining `sorry` at `gauss_infinitely_many_orbits`.
* `~/personal/bin/lean-green . --target CollatzMoonshot.GaussianRelative --axioms
  CollatzMoonshot.GaussianRelative.conj_gaussH_conj_gaussH` — FORMALIZE-TIER GREEN; axiom list
  exactly `[Classical.choice, Quot.sound, propext]`.  (A first attempt hit a transient filesystem
  `Too many open files`; the identical retry succeeded.)
* `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 8844 jobs.

## Current blocker and next attack

Do **not** use `Amusical.orbit_inter_fixedPoints_ncard_le_two`: Lane R has not proved it, and the
kickoff forbids importing its `sorry` as proof debt.  Prove the needed local specialization from
the already proved `Amusical.reversing_zpow_fixed`.

The route-decisive lemma is: for `σ = gaussPerm`, `ι = conjPerm`, any orbit contains at most two
`ι`-fixed points.  Parameterize three alleged fixed points by exponents `k₁,k₂,k₃`; translating
the base to the first point, `reversing_zpow_fixed` says both exponent differences have doubled
period.  In the stabilizer subgroup `{k : ℤ | (σ^k)x=x}`, either it is `{0}` (giving at most one)
or it is `pℤ`; the solutions of `2k ≡ 0 (mod p)` are the two residue classes `0` and `p/2`.
Once that finite-fiber lemma is in place, argue that a finite family of orbits would make its
union of intersections with `Fix(conjPerm)` finite, contradicting the infinite fixed subset
`{(n,0) | n : ℤ}`.  Establish the group identities from `conj_gaussH_conj_gaussH`; do not depend
on either of Lane R's unresolved target theorems.
