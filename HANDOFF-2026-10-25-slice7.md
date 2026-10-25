# SliceSeven treadmill handoff — 2026-10-25

## Checkpoint

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

## Current blocker and next attack

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
