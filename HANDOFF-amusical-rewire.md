# HANDOFF: bounded-ratio amusical rewiring

## 2026-10-14 — objective complete: bounded-ratio rewiring proved

`CollatzMoonshot/AmusicalRewireRatio.lean` is sorry-free and its ratified theorem
`exists_boundedRatio_rewire` is proved unchanged.  The final construction replaces the earlier
one-orbit-at-a-time schedule with an all-active sweep at each scale:

- `CutDynamics.lean` identifies the exact structural successor of every canonical forward or
  backward cut, proves consecutive cut times have no intervening canonical source, and lifts one
  cut transition to a finite positive path of the rewired natural permutation.
- `Sweep.lean` cycles the base forward cut through both cuts of every non-base infinite
  representative active at a level.  The resulting global cut permutation is level-preserving,
  so all previously proved factor-three and `O(log² N)` bounds apply unchanged.
- `Connectivity.lean` proves the induced successor is a single cycle on all canonical cuts.  A
  first-hit lemma then proves every point of every infinite natural orbit reaches that cut cycle
  while following unchanged edges before its first cut.
- The target selects the least natural point on any infinite orbit (when one exists), proves it
  is its orbit representative, packages the sweep with `BoundedRatioSourceRewire`, and retains
  the existing no-infinite-orbit degenerate branch.

Exact verification:

```text
LEAN_NUM_THREADS=1 lake build CollatzMoonshot.AmusicalRewireRatio
# Build completed successfully (8720 jobs).
git diff --check
# passes
awk 'length($0)>100 { ... }' CollatzMoonshot/AmusicalRewireRatio.lean \
  CollatzMoonshot/AmusicalRewireRatio/{CutDynamics,Sweep,Connectivity}.lean
# no output
LEAN_NUM_THREADS=1 ~/personal/bin/lean-green \
  ~/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio \
  --import CollatzMoonshot.AmusicalRewireRatio \
  --axioms CollatzMoonshot.Amusical.exists_boundedRatio_rewire
# 8720 jobs; headline axioms exactly Classical.choice, Quot.sound, propext.
# FORMALIZE-TIER GREEN
```

Current blocker: none for this treadmill objective.  The scoped target is sorry-free.

Next attack: none in scope; return control to the host completion gate.

## 2026-10-14 — exact scheduled successor transitions formalized

The target still has its original `sorry`; global connectivity remains the sole obligation.  This
lap added the sorry-free module `CollatzMoonshot/AmusicalRewireRatio/Transitions.lean` and the
three exact action lemmas for `spliceCycle`:

- `spliceCycle_apply_baseForward`, `spliceCycle_apply_repBackward`, and
  `spliceCycle_apply_repForward` prove that the cycle is oriented
  `F(b,k) ↦ B(r,k) ↦ F(r,k) ↦ F(b,k)`.
- `scaleCut_rewired_apply` proves the key semantic bridge: rewiring by a cut permutation `p`
  sends the natural source of `i` exactly to the natural target of `p i`.
- `splice_rewired_baseForward`, `splice_rewired_repBackward`, and
  `splice_rewired_repForward` consequently prove the three exceptional successor edges at each
  nontrivial scheduled level.  The schedule's enter/cross/exit orientation is now kernel-checked,
  rather than inferred from permutation multiplication conventions.

Exact verification:

```text
LEAN_NUM_THREADS=1 lake build CollatzMoonshot.AmusicalRewireRatio.Schedule
# Build completed successfully (8714 jobs).
LEAN_NUM_THREADS=1 lake env lean CollatzMoonshot/AmusicalRewireRatio/Transitions.lean
# passes
LEAN_NUM_THREADS=1 ~/personal/bin/lean-green \
  ~/src/collatz-moonshot-amusical-rewire --target CollatzMoonshot.AmusicalRewireRatio
# FORMALIZE-tier green (see gate verdict below in this checkpoint's commit).
```

Current blocker: lift these local exceptional edges to a global path theorem.  One must also show
that all nonscheduled sources retain their original successor and that the finite original-orbit
segments between consecutive scale cuts are traversed unchanged.

Next attack: prove exact z-power coordinates for every cut target, then package interval traversal:
between consecutive forward cuts the successor follows increasing orbit coordinates, and between
consecutive backward cuts it follows toward the representative.  Combine those segment lemmas
with the three transition lemmas above and induct over consecutive levels `Nat.pair r t` to put
every representative on the base chain.

## 2026-10-14 — scheduled three-cut permutation formalized

The target still has its original `sorry`; the remaining obligation is the connectivity proof.
This lap added the sorry-free module `CollatzMoonshot/AmusicalRewireRatio/Schedule.lean`:

- `ScaleCutIndex.fiberwisePerm` assembles a family of level-preserving permutations into one
  global permutation, with its inverse checked fiberwise.
- `spliceCycle` is the concrete three-cycle on the base forward cut, the scheduled orbit's
  backward cut, and its forward cut.  `spliceCycle_level` proves it preserves scale.
- `scheduledLocal` decodes `r = (Nat.unpair k).1` at level `k`, performs the three-cycle exactly
  when `r` is a non-base infinite representative, and otherwise fixes the level.
- `scheduledCutPerm` assembles these local cycles.  `scheduledCutPerm_level` proves the exact
  hypothesis required by `BoundedRatioSourceRewire.ofScaleCutPerm`.  Thus the proposed schedule
  is no longer prose: only its orbit-connectivity consequence remains to establish.

Exact verification:

```text
LEAN_NUM_THREADS=1 lake env lean CollatzMoonshot/AmusicalRewireRatio/Schedule.lean
# passes
awk 'length($0)>100 { ... }' CollatzMoonshot/AmusicalRewireRatio/Schedule.lean
# no output
git diff --check
# passes
LEAN_NUM_THREADS=1 ~/personal/bin/lean-green \
  ~/src/collatz-moonshot-amusical-rewire --target CollatzMoonshot.AmusicalRewireRatio
# Build completed successfully (8716 jobs).
# FORMALIZE-TIER GREEN; only the ratified target declaration retains a sorry.
```

The box intermittently reported `Too many open files` while loading mathlib; serial Lean
(`LEAN_NUM_THREADS=1`) succeeded on retry.

Current blocker: prove that rewiring by `scheduledCutPerm` connects every pair of infinite
natural amusical orbits.  No arithmetic, bijectivity, scale preservation, or schedule-definition
work remains.

Next attack: state and prove the cut-incidence transition rules for the original successor:
successive backward cuts run toward the representative, and successive forward cuts run away
from it.  Compute the three exceptional transitions at each scheduled level.  Then induct between
consecutive levels `Nat.pair r t` to show the base chain makes a finite detour through every
segment of orbit `r`, including its central segment at the first scheduled level.  Feed that
connectivity theorem to `BoundedRatioSourceRewire.ofScaleCutPerm` and `.realize`.

## 2026-10-14 — quantitative cut permutation discharged

The target still has its original `sorry`; only the global connectivity construction remains.
This lap added the sorry-free module
`CollatzMoonshot/AmusicalRewireRatio/Cuts.lean` and strengthened the reduction in `Splice.lean`:

- `IsInfiniteOrbitRep` canonically represents every infinite natural orbit by `orbitMinNat`.
- `ScaleCutIndex` indexes the forward and backward cut for every representative `r ≤ k` at
  height `8^(k+1)`.  `ScaleCutIndex.source_injective` proves that all indexed sources are
  distinct: eightfold separation handles different levels, orbit minima handle different
  representatives, and the first-passage inequalities separate the two sides.
- `scaleCutSourcePerm` extends any permutation of these indices by the identity on all other
  naturals.  If the index permutation preserves `level`, then
  `scaleCutSourcePerm_fixed_finite` and `scaleCutSourcePerm_target_ratio` discharge the finite-
  orbit and factor-three clauses.
- `ScaleCutIndex.level_le_log_of_source_lt` proves that a cut source below `N` has
  `level ≤ log₂ N`.  Encoding an index by `(level, rep, side)` then gives the uniform bound
  `2 * (log₂ N + 1)^2` in `scaleCutSourcePerm_moved_card`, for every index permutation.
- `BoundedRatioSourceRewire.ofScaleCutPerm` packages those results.  A level-preserving index
  permutation and its connectivity proof now supply every field except no additional arithmetic
  or counting work.

Adversarial review also found a useful, simpler next construction than cycling every active
orbit at every level.  Let `b` be the least infinite representative.  At level `k`, decode
`r = (Nat.unpair k).1`; when `r` is an infinite representative distinct from `b`, use the
three-cycle `[F(b,k), B(r,k), F(r,k)]`, and otherwise use the identity.  `Nat.unpair_left_le`
makes the indices valid, while the levels `Nat.pair r t` schedule every `r` cofinally.  The
induced source-cut successor is `S * p`, where `S` is the original cut successor.  Consecutive
scheduled levels for `r` make one finite detour from the base orbit through the intervening
backward and forward segments; the first detour reaches the central segment.  This should be
substantially simpler to prove connected than the all-active Euler cycle, and even has constant
support per level.

Exact verification:

```text
lake env lean CollatzMoonshot/AmusicalRewireRatio/Cuts.lean
# passes
lake build CollatzMoonshot.AmusicalRewireRatio.Cuts
# Build completed successfully (8713 jobs).
lake build CollatzMoonshot.AmusicalRewireRatio.Splice
# Build completed successfully (8714 jobs).
git diff --check
# passes
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-rewire \
  --target CollatzMoonshot.AmusicalRewireRatio
# Build completed successfully (8715 jobs).
# FORMALIZE-TIER GREEN; only the ratified target declaration retains a sorry.
```

Current blocker: define that fiberwise three-cycle permutation and prove connectivity.  All
representative selection, cut existence, endpoint injectivity, finite-orbit preservation,
factor-three control, and `O(log² N)` counting are now kernel-checked.

Next attack: formalize the structural cut successor
`B(r,k+1) ↦ B(r,k)`, `B(r,r) ↦ F(r,r)`, `F(r,k) ↦ F(r,k+1)`, then the scheduled
three-cycle above.  Prove `S * p` has one orbit by decomposing its forward path into the finite
detours between consecutive `Nat.pair r t` levels.  Finally lift segment connectivity from cut
indices to natural points and close the target with `BoundedRatioSourceRewire.ofScaleCutPerm`
and `.realize` (retaining the existing subsingleton branch).

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
