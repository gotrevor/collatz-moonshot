# HANDOFF: amusical Sparre--Andersen limit (2026-10-13, complete)

## Current checkpoint: `windowDensityLimit` is proved and the scoped file is sorry-free

The kickoff objective is complete.  The finite cyclic inclusion--exclusion identities are now
connected to Mathlib's formal power-series logarithm.  The new coefficient lemmas identify
compositions of fixed length with coefficients of powers, sum those lengths through
`PowerSeries.log`, and use the logarithmic derivative identity to prove the exact renewal
recurrences

```text
(n+1) * fwdSurv (n+1) = Σ k < n+1, fwdSurv k * fwdPosTerm (n-k+1),
(n+1) * bwdSurv (n+1) = Σ k < n+1, bwdSurv k * bwdPosTerm (n-k+1).
```

The analytic half is also kernel-checked.  Prefix truncation proves both survival sequences are
antitone.  A general bounded-coefficient power-series argument turns either recurrence into a
derivative identity on `|x| < 1`; an integrating factor then gives

```text
(1-x) Q(x) * exp (Σ nonposTerm(k+1)/(k+1) * x^(k+1)) = 1.
```

Mathlib's Abel limit theorem identifies the boundary limit of `(1-x)Q(x)` with the limit of the
antitone coefficients.  The existing directional summability results allow the defect series to
converge at `x = 1`, yielding `tendsto_fwdSurv` and `tendsto_bwdSurv`.  Their product, together
with `minimaConstant_eq_directionalFactors`, proves `windowDensityLimit`.

No ratified statement changed, and no `native_decide` or new axiom was added.  A textual audit
finds no `sorry`, `admit`, or `axiom` in `CollatzMoonshot/AmusicalSpitzer.lean`.

## Verification

Exact checks run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
rg -n '\b(sorry|admit|axiom)\b' CollatzMoonshot/AmusicalSpitzer.lean
git diff --check
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.windowDensityLimit
```

The direct compile exited zero.  The textual debt audit returned no matches.  The focused gate
ended `FORMALIZE-TIER GREEN`, and the completed headline theorem's axiom audit is exactly
`[Classical.choice, Quot.sound, propext]`.

## Current blocker and next highest-value attack

There is no remaining in-scope blocker or proof obligation: the host predicate
`sorry-free:CollatzMoonshot/AmusicalSpitzer.lean` is met.  Any subsequent work is stretch work
and should begin with an altitude review rather than altering the now-complete ratified theorem.

## Previous checkpoint: marked cyclic subsets reindex exactly to compositions

This lap closed the genuinely cyclic set-counting step left by the preceding checkpoint.  The
new `anchorCyclicFinset` / `unanchorCyclicFinset` translate an arbitrary marked start to zero
and back.  They preserve membership and cardinality, and `markedCyclicFinsetEquiv` proves the
exact equivalence

```text
{(s,a) | a ∈ s}  ≃  Fin L × {t | 0 ∈ t}.
```

Together with the fiberwise enumeration of marks, this yields
`cyclicFinset_double_count`: every nonempty set `s` occurs `s.card` times on the marked side,
while every anchored set occurs `L` times on the absolute-anchor side.  The derived
`cyclicFinset_sum_eq_composition` combines that count with `compositionStartsEquiv`, giving the
load-bearing formula for every rotation-invariant contribution `G`:

```text
Σ (nonempty s), G(s)
  = L * Σ (c : Composition L), G(compositionStarts c) / c.length.
```

Thus the subset-cardinality sign and the reciprocal block count required by cyclic
inclusion--exclusion are now both kernel-checked.  No ratified statement changed, no axiom or
`native_decide` was added, and the scoped file still has exactly its one disclosed target
`sorry` at `windowDensityLimit`.

## Verification

Exact checks run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
git diff --check
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.cyclicFinset_sum_eq_composition
```

The focused gate ended `FORMALIZE-TIER GREEN`.  The new complete reindexing theorem's axiom
audit is exactly `[propext, Classical.choice, Quot.sound]`; the gate reports only the existing
`windowDensityLimit` proof debt.

## Current blocker and next highest-value attack

`windowDensityLimit` remains the scoped file's single `sorry`.  Instantiate the new abstract
reindexing with the actual inclusion--exclusion contribution

```text
(-1)^(s.card+1) * Σ_w 1[∀ r ∈ s, Good (rotateWord w r)] * wordWeight(w).
```

First prove this functional is invariant under `unanchorCyclicFinset`; the missing bridge is
the composition law for `rotateWord` modulo `L`, followed by reindexing words by the inverse
rotation and using `fwdWordWeight_rotateWord` / `bwdWordWeight_rotateWord`.  Then
`cyclicFinset_sum_eq_composition` and the already-proved
`fwdCompositionStartsIntersection_sum` / backward analogue produce the exact alternating
composition coefficient identity.  Package that identity as the renewal recurrence, derive
the two survival generating functions, and take the boundary limits with the already-proved
summability and `minimaConstant_eq_directionalFactors`.  Do not re-prove the marked-set count,
the anchored subset equivalence, or return to the refuted pointwise cut identity.

## Previous checkpoint: compositions are canonically anchored cyclic-start sets

This lap closed the linear-boundary half of the cyclic inclusion--exclusion reindexing.  The
new `compositionStarts c` is the finset of genuine block-boundary starts of a composition,
with the virtual endpoint removed.  The file now proves:

- `mem_compositionStarts_iff`: the marked starts are exactly the partial sums
  `c.sizeUpTo i` for `i < c.length`;
- `card_compositionStarts`: the number of starts is exactly the number of blocks;
- `compositionStarts_injective`: the anchored start set determines the composition;
- `compositionStartsEquiv`: for positive length `n+1`, compositions are canonically
  equivalent to finsets of `Fin (n+1)` containing zero, and its forward map is definitionally
  `compositionStarts`;
- `forall_mem_compositionStarts_iff`: quantifying over the anchored finset is exactly
  quantifying over the old block-boundary indices;
- `fwdCompositionStartsIntersection_sum` and
  `bwdCompositionStartsIntersection_sum`: the already-proved weighted intersection
  factorization now has the actual finite-set event shape consumed by Mathlib's
  `Finset.inclusion_exclusion_sum_biUnion`.

Thus anchored nonempty cyclic subsets no longer need an ad hoc enumeration, and the subset
cardinality/sign in inclusion--exclusion is already identified with `c.length`.  No ratified
statement changed, no axiom or `native_decide` was added, and the scoped file still has exactly
its one disclosed target `sorry` at `windowDensityLimit`.

## Verification

Exact checks run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
git diff --check
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.fwdCompositionStartsIntersection_sum
```

The focused gate ended `FORMALIZE-TIER GREEN`.  The new anchored intersection theorem's axiom
audit is exactly `[Classical.choice, Quot.sound, propext]`; the gate reports only the existing
`windowDensityLimit` proof debt.

## Current blocker and next highest-value attack

`windowDensityLimit` remains the scoped file's single `sorry`.  The remaining finite
reindexing is the genuinely cyclic anchor count.  For a nonempty subset `s : Finset (Fin L)`,
count pairs `(s, a)` with `a ∈ s`, rotate `s` so that `a` becomes zero, and transport the
result through `compositionStartsEquiv`.  Each `s` occurs `s.card` times on the marked-pair
side, while each anchored composition has `L` possible absolute anchors.  Prove the resulting
weighted double-counting identity, using rotation invariance of word weights/events, to turn
the inclusion--exclusion subset sum into

```text
positiveEndpoint L / L =
  sum over positive compositions c of L of
    (-1)^(c.length+1) / c.length * product_i (survive (c.blocksFun i)).
```

Then package that composition identity as the renewal recurrence, derive the two survival
generating functions, and take the boundary limits with the already-proved summability and
`minimaConstant_eq_directionalFactors`.  Do not re-prove the anchored subset equivalence or
return to the refuted pointwise cut identity.

## Previous checkpoint: every composition-indexed weighted intersection factors

This reflection lap audited the full remaining proof graph rather than extending the preceding
list interface mechanically.  The finite cyclic-union route is still faithful to the ratified
`WindowDensityLimit`: the already-proved Haar split identifies the desired constant, the exact
word computations support the same Sparre--Andersen coefficient recurrence through length 14,
and the earlier counterexample rules out only a pointwise same-word cut identity, not the
cyclic inclusion--exclusion argument.  The missing finite reindexing, rather than another score
lemma, is now the route-decisive crux.

The key source-level discovery is Mathlib's existing `Composition L` API.  The new
`wordBlocksEquiv` uses its canonical equivalence between `Fin L` and the disjoint union of the
positive composition blocks.  The file now proves:

- `wordBlockLists_eq_splitWrtComposition` and `wordBlockLists_flatten`: the canonical dependent
  block family is exactly Mathlib's list splitting and flattens back to the original word;
- `wordBlockLists_rotate_flatten`: rotating the block list by `r` is exactly `rotateWord` at the
  marked boundary `c.sizeUpTo r`;
- `wordTrueCount_eq_sum_blocks`, `fwdWordWeight_eq_prod_blocks`, and
  `bwdWordWeight_eq_prod_blocks`: counts and both probability weights factor across every
  positive composition;
- `fwdCompositionIntersection_sum` and `bwdCompositionIntersection_sum`: the weighted sum of
  simultaneous survival at all block boundaries is the product of the block survival masses;
- `fwdCompositionBoundaryIntersection_sum` and
  `bwdCompositionBoundaryIntersection_sum`: the same theorem in the original `rotateWord`
  event language needed by cyclic inclusion--exclusion.

This discharges the entire arbitrary-intersection probability calculation, including the
dependent finite-word reindexing that the previous handoff left open.  No ratified statement was
changed, no axiom or `native_decide` was added, and the scoped file still has exactly its one
disclosed target `sorry` at `windowDensityLimit`.

## Verification

Final exact checks run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
lake build CollatzMoonshot.AmusicalSpitzer
git diff --check
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.fwdCompositionBoundaryIntersection_sum
```

The focused gate ended `FORMALIZE-TIER GREEN`.  The new boundary-intersection theorem's axiom
audit is exactly `[Classical.choice, Quot.sound, propext]`; the gate reports only the existing
`windowDensityLimit` proof debt.

## Current blocker and next highest-value attack

`windowDensityLimit` remains the scoped file's single `sorry`.  The next load-bearing step is
the cyclic inclusion--exclusion reindexing itself.  For fixed `0 < L`, represent a nonempty
subset of cyclic starts by a chosen marked anchor and the positive cyclic-gap composition.
Mathlib's `CompositionAsSet` / `compositionAsSetEquiv` already handles the linear internal
boundaries; the remaining theorem must account for the choice of cyclic anchor, so a set of
cardinality `m` is counted `m` times.  Combining that exact finite count with
`fwdCompositionBoundaryIntersection_sum` (and its backward analogue) should yield the standard
coefficient identity

```text
positiveEndpoint L / L =
  sum over positive compositions c of L of
    (-1)^(c.length+1) / c.length * product_i (survive (c.blocksFun i)).
```

Then package it as the renewal recurrence, derive the two survival generating functions, and
take the boundary limits.  Mathlib's `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` is available
for the Abel step, while this file already supplies `summable_fwdNonposSeries`,
`summable_bwdNonposSeries`, and `minimaConstant_eq_directionalFactors`.  Do not return to the
refuted pointwise cut identity, and do not duplicate composition splitting by hand.

## Previous checkpoint: every cyclic intersection factors propositionally

This lap generalized the preceding two-mark result to an arbitrary nonempty ordered collection
of nonempty cyclic gaps.  The abstract theorem `cyclicBlocks_all_iff` proves that for any
list predicate which restricts to an initial block and is preserved by concatenation,
simultaneous survival from every cyclic block boundary is equivalent to separate survival of
every block.  Its proof rotates an arbitrary selected block to the front for the reverse
implication and folds append closure around every rotation for the forward implication.

The generic prefix facts `strictlyPositivePrefixes_of_append_left` and
`strictlyPositivePrefixes_append` instantiate this theorem on additive score lists.  The result
is connected back to both original walk predicates through `fwdListGood_iff` and
`bwdListGood_iff`; the final statements `fwdGood_cyclicBlockLists_iff` and
`bwdGood_cyclicBlockLists_iff` say directly that all marked cyclic starts survive iff all
positive-length gap words survive.  Thus the logical intersection identity required for every
term of cyclic inclusion--exclusion is now kernel-checked, rather than merely the two-mark base
case.

## Verification

Exact commands run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
lake build CollatzMoonshot.AmusicalSpitzer
git diff --check
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.fwdGood_cyclicBlockLists_iff
```

The target gate ended `FORMALIZE-TIER GREEN`; the arbitrary-mark forward theorem's axiom audit
is exactly `[propext, Classical.choice, Quot.sound]`.  The only proof-debt warning remains the
pre-existing `windowDensityLimit`.

## Current blocker and next highest-value attack

`windowDensityLimit` remains the scoped file's single `sorry`.  The proposition-level
arbitrary-intersection theorem now removes the main logical obstacle.  Next lift it to weighted
sums indexed by a positive composition of the total length: prove that the weight of the
flattened block list is the product of block weights and that the finite sum over block words
factors as the product of the corresponding `fwdSurv` or `bwdSurv` values.  Feed those terms to
`Finset.inclusion_exclusion_sum_biUnion` for the cyclic survival-event cover to derive the
verified renewal recurrence.  Then derive the two generating functions and take their boundary
limits using `summable_fwdNonposSeries`, `summable_bwdNonposSeries`, and
`minimaConstant_eq_directionalFactors`.  Do not return to the refuted pointwise cut identity.

## Previous checkpoint: the first cyclic intersection term factors exactly

This lap advanced the cyclic-union inclusion--exclusion route past the one-mark cover.  In
`CollatzMoonshot/AmusicalSpitzer.lean`, the new restriction lemmas
`FwdGood.of_append_left` and `BwdGood.of_append_left` show that the initial block of any
surviving concatenation survives.  Combining this with the existing append closure proves

```text
Good (u ++ v) ∧ Good (v ++ u)  ↔  Good u ∧ Good v
```

for positive-length blocks, in both directions (`fwdGood_append_and_swap_iff` and
`bwdGood_append_and_swap_iff`).  Thus simultaneous survival from two cyclic marks is exactly
separate survival on the two intervening arcs; there is no independence assumption hidden in
the factorization.

The weighted form is also proved.  `fwdTwoMarkIntersection_sum` and
`bwdTwoMarkIntersection_sum` sum over every pair of Boolean blocks, use product-weight
factorization, and identify the result exactly with
`fwdSurv m * fwdSurv n` and `bwdSurv m * bwdSurv n`.  This is the first genuinely nontrivial
intersection term required by the standard cyclic inclusion--exclusion proof.

## Verification

Exact commands run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
git diff --check
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.fwdTwoMarkIntersection_sum
```

The target gate ended `FORMALIZE-TIER GREEN`; the new weighted factorization's axiom audit is
exactly `[Classical.choice, Quot.sound, propext]`.  The only proof-debt warning remains the
pre-existing `windowDensityLimit`.

## Current blocker and next highest-value attack

`windowDensityLimit` is still the scoped file's single `sorry`.  Generalize the proved
two-block equivalence to an ordered nonempty composition of the circle: survival from every
marked boundary is equivalent to survival of every positive-length gap block.  The weighted
intersection then factors as the product of the corresponding `fwdSurv` or `bwdSurv` values.
Summing these composition-indexed intersection terms with finite inclusion--exclusion gives
the cyclic-union coefficient identity, from which the verified renewal recurrence follows.
After that, derive the two generating functions and take the boundary limit using the existing
summability and `minimaConstant_eq_directionalFactors`.  Do not return to the refuted pointwise
cut identity.

## Previous checkpoint: kernel-checked cyclic-minimum theorem and word-level cover

This review lap reconstructed the proposed recurrence route and closed its first genuinely
cyclic step.  The new generic module `CollatzMoonshot/CyclicMinimum.lean` proves:

- `prefixSums_ne_of_blocks_ne_zero`: nonzero sums for all nonempty contiguous blocks imply
  pairwise-distinct prefix sums;
- `exists_rotate_strictlyPositivePrefixes`: a positive-total, no-tie list has a rotation whose
  every nonempty prefix has positive sum;
- `sum_pos_iff_exists_rotate_strictlyPositivePrefixes`: the exact iff form used below.

`CollatzMoonshot/AmusicalSpitzer.lean` now instantiates this theorem for both walks.  The additive
log-score interface is proved equivalent to the existing multiplicative endpoint and survival
predicates.  In particular, every nonempty contiguous score block is proved nonzero from
`wordBlock_endpoint_lt_or_gt`, so the generic theorem's no-tie premise is discharged rather than
assumed.  The load-bearing conclusions are:

- `fwdEndpointPositive_iff_exists_goodRotation` and
  `bwdEndpointPositive_iff_exists_goodRotation`: a word has positive endpoint exactly when one
  of its concrete cyclic rotations survives;
- `fwdWordWeight_rotateWord` and `bwdWordWeight_rotateWord`: every such arbitrary rotation
  preserves its product weight.

No ratified statement changed, and no new axiom was introduced.

## Adversarial route finding

Exact `Fraction` enumeration of all Boolean words verified both weighted coefficient recurrences

```text
L * survive L = sum_{k=1}^L positiveEndpoint k * survive (L-k)
```

for every `1 <= L <= 14`.  It also refuted a tempting *pointwise same-word* proof: for the
forward word `(true, false, false, true)` there is one good cyclic rotation but two cuts whose
prefix has positive endpoint and whose suffix survives.  Therefore do not try to prove the
recurrence by equating those two statistics word by word.  A global marked-word bijection would
need a genuine reassembly map; the source-backed alternative is the standard cyclic-union
inclusion--exclusion proof.

## Verification

Exact commands run in this lap:

```text
lake build CollatzMoonshot.CyclicMinimum
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.fwdEndpointPositive_iff_exists_goodRotation
git diff --check
```

The target gate ended `FORMALIZE-TIER GREEN`.  Its only proof-debt warning is the pre-existing
`windowDensityLimit`; the headline cyclic-cover theorem's axiom audit is exactly
`[Classical.choice, Quot.sound, propext]`.  The checkpoint commit also passed the repository
pre-commit hook's full `lake build`.

## Current blocker and next highest-value attack

`windowDensityLimit` remains the scoped file's single disclosed `sorry`.  The cyclic cover,
block no-tie argument, arbitrary rotation invariance, concatenation factorization, finite-word
sum identities, and analytic summability are now kernel-checked.

Next formalize the intersection term in the cyclic-union inclusion--exclusion proof.  For ordered
cyclic marks, show that simultaneous survival from those starts factors into surviving blocks at
the cyclic gap lengths; transfer product weights with `*_rotateWord` and `*_append`.  Summing over
marks/compositions gives the verified coefficient recurrence above.  Then derive the two survival
generating functions and take the boundary limit using the existing summability results and
`minimaConstant_eq_directionalFactors`.  Do not repeat the log-score, no-tie, cyclic-cover, or
rotation-weight work, and do not revive the refuted pointwise cut identity.

## Previous checkpoint: prefix survival and concatenation

The survival predicates now use the same actual finite blocks as the cyclic decomposition,
rather than re-expanding an ad hoc filtered count at every use.  All additions are proved in
`CollatzMoonshot/AmusicalSpitzer.lean`:

- `wordTrueCount_take` identifies the marked-letter count of `Fin.take t w` with the filtered
  prefix count occurring in the ratified `FwdGood` and `BwdGood` definitions.
- `FwdEndpointPositive` and `BwdEndpointPositive` name the two strict endpoint signs.
- `fwdGood_iff_prefix_positive` and `bwdGood_iff_prefix_positive` prove that survival is exactly
  strict endpoint positivity of every nonempty prefix word.
- `FwdEndpointPositive.append` and `BwdEndpointPositive.append` prove that positive blocks remain
  positive under concatenation.
- `FwdGood.append` and `BwdGood.append` prove the survival factorization when the left block is
  nonempty, precisely the form needed after cutting off the first positive cyclic block.

No ratified statement changed.  That lap ran:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.FwdGood.append
git diff --check
```

Both target gates ended `FORMALIZE-TIER GREEN`; the axiom audit for `FwdGood.append` is exactly
`[propext, Classical.choice, Quot.sound]`.  The only proof-debt warning was `windowDensityLimit`.

## Previous checkpoint: cyclic weight interface

## Concrete advance

The weighted cyclic-decomposition hypotheses are now explicit, proved, and connected to the
existing probability sums in `CollatzMoonshot/AmusicalSpitzer.lean`:

- `fwdWordWeight` and `bwdWordWeight` name the two product weights.
- `wordTrueCount_comp_equiv`, `fwdWordWeight_comp_equiv`, and
  `bwdWordWeight_comp_equiv` prove invariance under every permutation; the corresponding
  `_rotate` theorems expose the cyclic-shift instances directly.
- `wordTrueCount_append`, `fwdWordWeight_append`, and `bwdWordWeight_append` prove that the
  count is additive and both weights multiply under concatenation.  This is the factorization
  needed on the right side of the renewal recurrence.
- `wordBlock_endpoint_ne` and `wordBlock_endpoint_lt_or_gt` prove that every nonempty block,
  regardless of its number of marked letters, has nonzero score and exactly one strict sign.
- `fwdPosTerm_eq_weighted_word_sum`, `bwdPosTerm_eq_weighted_word_sum`,
  `fwdSurv_cast_eq_weighted_word_sum`, and `bwdSurv_cast_eq_weighted_word_sum` restate all four
  ratified finite-word identities through those named weights.  The original statements were
  not changed.

Thus all walk-specific hypotheses listed in the previous handoff are now kernel-checked.  The
remaining hard step is purely combinatorial: construct the marked cyclic decomposition that
turns these hypotheses into the renewal coefficient identity.  The preceding lap's geometric
summability and final Haar-series factorization remain intact.

## Verification

Exact commands run in this lap:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer
lake env lean AxiomAudit.lean
git diff --check
```

The target gate ended `FORMALIZE-TIER GREEN`.  The only proof-debt warning is the pre-existing
target `windowDensityLimit`.  `AxiomAudit.lean` was a temporary probe containing `#print axioms`
for the new structural headline theorems and was removed after it passed.  `git diff --check`
was clean.

## Current blocker

`windowDensityLimit` still contains the repository's single disclosed `sorry`.  The sole
route-decisive missing theorem is the weighted Sparre--Andersen cyclic decomposition.  In the
common finite-word language now present, prove for each direction and `0 < L` the coefficient
recurrence

```text
L * survive L = sum_{k=1}^L positiveEndpoint k * survive (L-k).
```

Rotation invariance, concatenation factorization, and block tie-freeness no longer need to be
proved inside that theorem: use the named lemmas above.

Once the recurrences exist, the remaining analytic work is: derive the two survival generating
functions, pass to the boundary using the summability proved this lap, obtain the two directional
limits, multiply them, and rewrite with `minimaConstant_eq_directionalFactors`.

## Next highest-value attack

Define and prove the marked cyclic-decomposition bijection itself.  A productive concrete form
is a bijection between `(word : Fin L -> Bool, marked position : Fin L)` with the word surviving,
and the disjoint union over `1 <= k <= L` of a positive-endpoint word of length `k` and a
surviving word of length `L-k`.  State the underlying unweighted bijection first; its weighted
sum follows immediately from `*_comp_equiv` and `*_append`.  Then specialize it with the four
`*_eq_weighted_word_sum` lemmas.  Do not repeat the library search, walk-specific invariance,
tie-freeness, or summability arguments; those are now resolved.
