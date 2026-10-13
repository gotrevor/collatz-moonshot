# HANDOFF: amusical Sparre--Andersen limit (2026-10-13, prefix-word interface)

## Current checkpoint: prefix survival and concatenation

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

No ratified statement changed.  The current lap ran:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer --axioms CollatzMoonshot.Amusical.FwdGood.append
git diff --check
```

Both target gates ended `FORMALIZE-TIER GREEN`; the axiom audit for `FwdGood.append` is exactly
`[propext, Classical.choice, Quot.sound]`.  The only proof-debt warning is the pre-existing
`windowDensityLimit` target.  The checkpoint commit also passed the repository pre-commit hook's
full `lake build` (8840 jobs).

`windowDensityLimit` remains the scoped file's single disclosed `sorry`.  The route-decisive
blocker remains the weighted marked cyclic-decomposition bijection and its recurrence
`L * survive L = sum_{k=1}^L positiveEndpoint k * survive (L-k)`.  The next lap should prove the
unweighted bijection using `FwdEndpointPositive` / `BwdEndpointPositive` for the first block and
the new prefix equivalences plus `.append` lemmas for the surviving tail, then transfer weights
with the already-proved rotation invariance and weight factorization.  After the recurrences,
derive the generating functions and take the boundary limit using the proved summability and
`minimaConstant_eq_directionalFactors`.

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
