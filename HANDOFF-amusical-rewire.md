# HANDOFF: bounded-ratio amusical rewiring

## 2026-10-14 — source-permutation reduction

The target still has its original `sorry`; the global cut-source permutation remains open.  This
lap isolated and kernel-checked the algebraic interface in
`CollatzMoonshot/AmusicalRewireRatio/Splice.lean`:

- `rewireBySource σ p = σ * p` implements rewiring by permuting cut sources, so bijectivity is
  automatic and the new target at `n` is the old target at `p n`.
- `rewireBySource_changed_card_le` proves that changed values below `N` are bounded by moved
  sources below `N`.
- `rewireBySource_ratio` and `rewireBySource_eq_on_finiteOrbits` transfer the factor-three and
  finite-orbit clauses from pointwise properties of `p`.
- `BoundedRatioSourceRewire` is now the exact remaining combinatorial interface, and
  `BoundedRatioSourceRewire.realize` proves that any inhabitant supplies every conclusion of
  `exists_boundedRatio_rewire`.

Exact verification:

```text
lake env lean CollatzMoonshot/AmusicalRewireRatio/Splice.lean
# passes
awk 'length($0)>100 { ... }' CollatzMoonshot/AmusicalRewireRatio/Splice.lean
# no output
git diff --check
# passes
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio
# Build completed successfully (8714 jobs).
# FORMALIZE-TIER GREEN; only the target declaration retains a sorry.
```

Current blocker: construct `BoundedRatioSourceRewire.sourcePerm` from the scale cuts.  All
algebraic, cast, count-transfer, finite-orbit, and ratio plumbing is now discharged; the hard core
is exactly the Eulerian cut-source permutation plus its single-orbit proof.

Next attack: define the least representative of each infinite `amusicalNatPerm` orbit and enumerate
those representatives increasingly.  Use the scale cuts to define disjoint cycles of source
assignments at each scale; compose them using cross-scale separation.  Prove the four fields of
`BoundedRatioSourceRewire` directly, then close the target with `.realize`.

## 2026-10-14 — scale-cut windows and separation

The target still has its original `sorry`; the explicit global splicing permutation remains open.
This lap completed the local geometric layer in
`CollatzMoonshot/AmusicalRewireRatio/Passage.lean`:

- `forwardCutSource`/`forwardCutTarget` and their backward analogues identify the two oriented
  edges crossing a height for the first time, with exact `amusicalNatPerm` incidence.
- `AmusicalScaleCut`, `forwardScaleCut`, and `backwardScaleCut` package both endpoint windows in
  integral form.  In particular every cut target at height `B` lies between approximately
  `3B/4` and `3B/2`, exactly the interval needed when a splice replaces one cut image by another.
- `AmusicalScaleCut.target_ratio` proves the target theorem's factor-3 affine comparison for any
  two targets at one scale.
- `source_lt_of_eight_mul_le` and `target_lt_of_eight_mul_le` prove strict separation of cut
  endpoints at scales growing by eight.  This supplies the no-collision fact needed both for the
  permutation construction and the logarithmic change count.

Exact verification:

```text
lake env lean CollatzMoonshot/AmusicalRewireRatio/Passage.lean
# passes
awk 'length($0)>100 { ... }' CollatzMoonshot/AmusicalRewireRatio/Passage.lean
# no output
git diff --check
# passes
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio
# Build completed successfully (8713 jobs).
# FORMALIZE-TIER GREEN; only the target declaration retains a sorry.
```

Current blocker: enumerate the infinite natural orbits and define a bijective global successor
which splices their scale segments without endpoint collisions.  Escape, cut incidence, endpoint
geometry, factor-3 comparison, and cross-scale separation are now available.

Next attack: define the orbit equivalence relation of `amusicalNatPerm`, choose one least natural
representative per infinite class, and enumerate those representatives increasingly.  Define
geometric scales recursively above each representative.  Then express the Eulerian recursion as
a permutation of cut targets; `AmusicalScaleCut.target_ratio` should discharge the ratio clause
pointwise, while the separation lemmas support injectivity and counting.

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
