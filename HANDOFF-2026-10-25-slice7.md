# SliceSeven treadmill handoff — 2026-10-25

## Checkpoint 3: edge complete, scoped target sorry-free

The kickoff objective is complete.  `CollatzMoonshot/Conjugacy/SliceSeven.lean` is sorry-free, and
the frozen theorem
`sliceCharDecay_of_pascalDampingDecay : PascalDampingDecay → SliceCharDecay` is proved without
changing any frozen definition or statement.

- `sliceGapEquiv` gives an exact bijection between slice subsets and positive gap vectors with
  total at most `j`; `negativeSubsetChar_eq_sum_gapVector` reindexes the whole character sum.
- `gapBlockEquiv`, `splitGapVectorNat`, and `sum_gapFiberFinset_eq_splits` split each fixed
  pair-sum/tail fiber into independent positive split intervals.  `sum_gapFiberFinset` and
  `norm_sum_gapFiberFinset` perform all split cancellation exactly and recover the frozen
  `fPair` product, with the optional terminal factor proved to have norm one.
- `summable_pascalWeight`, `summable_fin_product_of_nonneg`, and
  `summable_pascalDampingTerm` prove the frozen infinite damping series is a legitimate majorant;
  `norm_fPair_le_one` supplies the domination.
- `weighted_pairFiberNorm_le_pascalDampingTerm` proves the geometric reweighting one admissible
  fiber at a time.  Summing fibers and overcounting the zero-or-one terminal coordinate gives
  `weighted_gapCharSum_le_pascalDamping`, with a single harmless factor `j+1`.
- `binomialSliceWeight_succ_balance` proves the adjacent binomial-mass identity;
  `one_div_succ_le_binomialSliceWeight_mode` proves that at `p=a/j` the target slice has mass at
  least `1/(j+1)`.  Thus `norm_sliceChar_le_mode_damping` loses only `(j+1)^2` after normalization.
- `succ_sq_mul_rpow_neg_add_three` absorbs those two polynomial losses using `j ≤ 5a`.  Applying
  `PascalDampingDecay` at exponent `A+3` completes the edge with the explicit constant
  `4 · 5^(A+3) · C`.

Exact completion gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier \
  --target CollatzMoonshot.Conjugacy.SliceSeven \
  --import CollatzMoonshot.Conjugacy.SliceSeven \
  --axioms CollatzMoonshot.Conjugacy.sliceCharDecay_of_pascalDampingDecay \
  --axioms CollatzMoonshot.Conjugacy.weighted_gapCharSum_le_pascalDamping \
  --axioms CollatzMoonshot.Conjugacy.one_div_succ_le_binomialSliceWeight_mode \
  --axioms CollatzMoonshot.Conjugacy.sliceGapEquiv

Build completed successfully (8725 jobs).
All four declarations: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also checked:

```text
lake env lean CollatzMoonshot/Conjugacy/SliceSeven.lean
git diff --check
rg -n '\bsorry\b|axiom|native_decide|set_option maxHeartbeats' \
  CollatzMoonshot/Conjugacy/SliceSeven.lean
```

The direct Lean check exits cleanly with no warnings, `git diff --check` passes, and the search has
no matches.  There is no remaining blocker in the scoped target.  The next campaign-level
objective, if explicitly assigned, is the open proof of `PascalDampingDecay` itself (the Sec7P
campaign) or the downstream `SliceDecay.lean` edge; neither was needed for this completed kickoff.

## Checkpoint 2: exact pair factor and reweighting foundations

The second lap formalized the load-bearing algebra underneath kickoff steps 2–5, without changing
any frozen statement.  The edge `sliceCharDecay_of_pascalDampingDecay` is still the sole sorry in
`SliceSeven.lean`; no sorry was moved or added.

- `charZ_eq_inv_stdAddChar`, `charZ_add`, and `charZ_sum` identify the hand-written negative
  exponential with mathlib's standard additive character and expose its multiplicativity.
  `subsetCharTerm_eq_stdAddChar` / `subsetCharTerm_eq_inv_charZ` close the sign bridge from the
  positive slice character.
- `wordNumer_eq_sum_orderEmbOfFin`, `wordNumer_mul_inv_eq_sum_reverseOddTime`, and
  `wordNumer_mul_inv_eq_sum_subsetGap` prove the complete formula
  `wordNumer(u)·2⁻ʲ = Σ_m 3^m·2⁻(g₀+⋯+g_m)` in `ZMod (3^a)`.  Thus kickoff step 1 is now fully
  expanded into the coordinates used by the pairing, not just reindexed onto subsets.
- `subsetGap_injective` proves these positive gaps are faithful coordinates on the slice.
  `gapPairSum`, `sum_gapPairSum_range`, `subsetPairSum`, and `subsetPairSum_two_le` set up the
  pair-sum vector and its prefixes.
- `two_residue_terms_eq_pairFactor` and `charZ_two_gap_terms` prove the decisive adjacent-pair
  identity: the two character factors at gaps `(g₀,g₁)` combine into exactly the
  `charZ (xArg · (2^g₁+3))` summand used by frozen `fPair`.
- `sum_charZ_splits_eq_mul_fPair` and `norm_sum_charZ_splits` prove that summing over all positive
  splits of a fixed `b≥2` yields exactly `(b-1)·fPair`, including the norm identity.  This closes
  the local finite-pairing calculation requested in kickoff step 3.
- `geom_split_weight_eq`, `pascalWeight_of_two_le`, and `pascalWeight_nonneg` formalize the
  split-independent geometric weight.  `card_levelSet_eq_choose` and
  `sum_binomialSliceWeight` formalize the binomial slice cardinality and total mass.

Exact scoped gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier \
  --target CollatzMoonshot.Conjugacy.SliceSeven \
  --import CollatzMoonshot.Conjugacy.SliceSeven \
  --axioms CollatzMoonshot.Conjugacy.charZ_two_gap_terms \
  --axioms CollatzMoonshot.Conjugacy.wordNumer_mul_inv_eq_sum_subsetGap \
  --axioms CollatzMoonshot.Conjugacy.subsetGap_injective \
  --axioms CollatzMoonshot.Conjugacy.norm_sum_charZ_splits \
  --axioms CollatzMoonshot.Conjugacy.sum_binomialSliceWeight

Build completed successfully (8725 jobs).
All five declarations: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also run repeatedly while iterating:

```text
lake env lean CollatzMoonshot/Conjugacy/SliceSeven.lean
git diff --check
```

Both pass; the Lean command reports only the pre-existing final edge sorry.

### Current blocker and next attack

The local pair identity is no longer the blocker.  The remaining route-decisive lemma is the
**global finite grouping inequality**: reindex `(range j).powersetCard a` by the faithful positive
gap vector, group the first `2*(a/2)` gaps by `subsetPairSum`, apply
`norm_sum_charZ_splits` independently to every pair, and discard the unit-norm final factor when
`a` is odd.  Its target should expose exactly

```text
‖sliceChar j a ξ‖ * binomialSliceWeight j a p
  ≤ (levelSet j a).card * pascalDamping a p ξ
```

for `0 < p < 1`.  Use `sum_gapPairSum_range` to identify the `xArg` prefix; do not reprove the
pair algebra.  The finite domain can be represented explicitly by positive functions
`Fin a → ℕ` with total `≤ j`; construct the inverse subset from reverse prefix sums to finish the
gap-coordinate bijection.  The trailing geometric factor is `(1-p)^(j-T_a) ≤ 1`.

After the master inequality, prove that `a` is a mode of `binomialSliceWeight j · (a/j)` by the
adjacent identity `Nat.choose_succ_right_eq`; `sum_binomialSliceWeight = 1` then gives the needed
`1/(j+1)` lower bound.  Apply the damping hypothesis at exponent `A+2` and absorb `j+1` using
`j≤5a`.

## Checkpoint 1: slice law and positive gaps

Kickoff step 1 is now formalized through the exact Terras reindexing and the positive-gap
coordinates, without changing any frozen statement.

- `tstep_iterate_cast_eq_wordNumer_inv` proves in `ZMod (3^a)` that the shortcut iterate is
  `wordNumer (onesSet r j) · 2⁻ʲ`.  It is the cast form of the existing iterate identity and
  cancels `2^j` using coprimality with `3^a`.
- `sliceChar_eq_subsetChar` reindexes the complete dynamical slice along the existing Terras
  bijection `r ↦ onesSet r j`.  Thus `sliceChar j a ξ` is exactly the residue character sum over
  `(range j).powersetCard a`; no cardinality or distribution assertion remains hidden in prose.
- `reverseOddTime` orders an `a`-subset backwards as `T_m = j - t_{a-1-m}`.
  `reverseOddTime_pos` and `reverseOddTime_strictMono` prove `1 ≤ T₁ < ⋯ < Tₐ`.
- `subsetGap` / `subsetGapNat` are the successive positive gaps.  `subsetGap_pos`,
  `sum_subsetGapNat_eq_reverseOddTime`, and `sum_subsetGapNat_le` prove that their prefixes are
  exactly the `T_m` and their total is at most `j`.  These are the coordinates needed for the
  geometric conditioning and pairing in kickoff steps 2–4.

The one original proof obligation remains
`sliceCharDecay_of_pascalDampingDecay`; no sorry was moved or added.  The frozen definitions
`charZ`, `fPair`, `xArg`, `pascalWeight`, `pascalDamping`, `PascalDampingDecay`, the edge, and
everything in `SliceDecay.lean` are unchanged.

## Verification

Exact scoped gate:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-fourier \
  --target CollatzMoonshot.Conjugacy.SliceSeven \
  --import CollatzMoonshot.Conjugacy.SliceSeven \
  --axioms CollatzMoonshot.Conjugacy.sliceChar_eq_subsetChar \
  --axioms CollatzMoonshot.Conjugacy.sum_subsetGapNat_le

Build completed successfully (8725 jobs).
sliceChar_eq_subsetChar: [Classical.choice, Quot.sound, propext]
sum_subsetGapNat_le: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also run repeatedly while iterating:

```text
lake env lean CollatzMoonshot/Conjugacy/SliceSeven.lean
git diff --check
```

Both pass; the Lean command reports only the pre-existing edge sorry.

## Checkpoint 1 next attack (local pair calculation now completed above)

The route-decisive remaining lemma is the finite pairing inequality.  Starting from
`sliceChar_eq_subsetChar`, reindex each `u` by `subsetGapNat`; group coordinates
`(g_{2i}, g_{2i+1})` by `b_i = g_{2i}+g_{2i+1}`.  Use
`sum_subsetGapNat_eq_reverseOddTime` to identify the prefix in `xArg`.  For fixed `b_i`, the
second gap ranges bijectively over `Icc 1 (b_i-1)`, so the complex inner sum is exactly
`(b_i-1) * fPair`.  An odd final gap contributes a unit-norm factor.

Then multiply the finite slice sum by `p^a (1-p)^(j-a)`.  Each admissible gap vector has this
constant weight after the trailing factor `(1-p)^(j-T_a)`; dropping that factor bounds the
result by `pascalDamping`.  The desired master estimate is

```text
‖sliceChar j a ξ‖ * (Nat.choose j a * p^a * (1-p)^(j-a))
  ≤ (levelSet j a).card * pascalDamping a p ξ.
```

Finally take `p=a/j`.  Prove the elementary mode bound
`1/(j+1) ≤ choose j a * p^a * (1-p)^(j-a)` by adjacent binomial ratios, apply the damping
hypothesis at exponent `A+2`, and absorb `j+1` using `j ≤5a`.

One Aristotle job (`503e31cb-a8ca-4d92-adfe-f1b1279b8272`) returned no changes: its service
environment could not build this Lean 4.33.1 project.  Do not resubmit the same whole-project
request unless the service toolchain changes.
