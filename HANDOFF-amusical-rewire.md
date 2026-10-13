# HANDOFF: bounded-ratio amusical rewiring

## 2026-10-13 — two-sided escape and first-passage infrastructure

The target still has its original `sorry`; the main-case construction remains open.  This lap
kernel-checked the load-bearing passage facts in
`CollatzMoonshot/AmusicalRewireRatio/Passage.lean`:

- `injective_eventually_abs_gt` proves that an injective `ℤ`-indexed sequence in `ℕ` eventually
  leaves every bounded interval in both time directions, by taking the finite preimage of an
  initial interval and bounding its `natAbs` image.
- `amusicalNatPerm_zpow_eventually_gt_of_infinite` specializes this to every infinite natural
  amusical orbit, using the existing integer-orbit injectivity theorem.
- `exists_forward_backward_above`, `forwardPassage`, and `backwardPassage` construct least
  passages above any height; `forwardPassage_before_le` and `backwardPassage_before_le` prove
  the required minimality on all earlier times.
- `amusical_step_bounds`, `amusicalInv_step_bounds`, and their natural-permutation versions prove
  the uniform affine one-step bounds needed to locate passage endpoints at a geometric scale.

Exact verification:

```text
lake env lean CollatzMoonshot/AmusicalRewireRatio/Passage.lean
# passes
git diff --check
# passes
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio
# Build completed successfully (8713 jobs).
# FORMALIZE-TIER GREEN; only the target declaration retains a sorry.
```

Current blocker: enumerate the infinite natural orbits and build the explicit segment successor
permutation.  Escape/existence is no longer part of that blocker.

Next attack: combine passage minimality with `amusicalNatPerm_step_bounds` and
`amusicalNatPerm_symm_step_bounds` to package forward/backward cut endpoints in one scale
interval (assuming the chosen orbit representative is below the scale).  Then define finite
segments between consecutive cuts and the Eulerian recursion from the kickoff.

## 2026-10-13 — nonnegative restriction and degenerate branch closed

The target `exists_boundedRatio_rewire` still has its original `sorry`.  This lap isolated and
kernel-checked the entire branch in which there is at most one infinite orbit on `ℕ`:

- `amusicalNatPerm` is the restriction of `amusicalPerm` to `ℕ`; both directions preserve
  nonnegativity, and its forward, inverse, and integer-power cast lemmas are proved.
- `exists_boundedRatio_rewire_of_connected` proves all four target conclusions with `τ = U|ℕ`
  when the infinite natural orbits are already connected.  The change set is empty (`C = 0`),
  so the quantitative and ratio conclusions are exact.
- `exists_boundedRatio_rewire_of_subsingleton_infiniteOrbits` derives that hypothesis from the
  paper proof's degenerate assumption (at most one infinite nonnegative orbit).

Files changed: `CollatzMoonshot/AmusicalRewireRatio/Restriction.lean` and the target module's
import.  The unrelated untracked `CLAUDE.local.md` was preserved.

Verification:

```text
lake build CollatzMoonshot.AmusicalRewireRatio.Restriction
Build completed successfully (8710 jobs).
/Users/gotrevor/personal/bin/lean-green \
  /Users/gotrevor/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio
Build completed successfully (8711 jobs).
FORMALIZE-TIER GREEN
```

Current blocker: the main case with at least two infinite orbits.  It needs the explicit sparse
cut-and-splice permutation; no theorem in mathlib or the repository supplies the quantitative
`O(log² N)` and factor-3 conclusions.

Next attack: formalize first-passage cuts at geometric scales.  Start with the load-bearing escape
lemma: an injective two-sided natural orbit eventually leaves every finite range in both time
directions.  Combine it with the elementary bounds on `U` and `U⁻¹` to put each first passage and
its adjacent image in the scale interval required by the ratio estimate.  Only then define the
segment enumeration and successor permutation.
