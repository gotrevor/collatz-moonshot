# SliceFourier treadmill handoff — 2026-10-25

## Checkpoint 1: Pascal recursion, sub-slices, and Fourier identity

The scoped target is not yet complete: the frozen theorem
`biasDecays_of_sliceCharDecay` remains the sole `sorry` in
`CollatzMoonshot/Conjugacy/SliceFourier.lean`.  This lap proved the three exact structural inputs
at the start of `SLICE-FOURIER-NEXT.md`, without editing any frozen dependency or changing the
headline statement.

- `sliceChar_pascal` proves
  `sliceChar (j+1) (a+1) (3*ξ) = sliceChar j (a+1) (3*ξ) + sliceChar j a ξ`.
  The even starts are immediate.  For the odd starts, `affineThreeEquiv` proves that
  `s ↦ (3s+2) mod 2^j` is a permutation; `tstep_iterate_affineThree_mod` and character
  periodicity remove its carry.
- `sliceChar_eq_subsliceSum` iterates that recurrence through every `1 ≤ k ≤ a`:
  `sliceChar j a (3^k*u)` is the sum over `t<j` of
  `choose t (k-1) * sliceChar (j-1-t) (a-k) u`.  This is the proposed `Icc 1 j` formula after
  the exact substitution `t=s-1`, so the spurious `s=0` term at `k=1` is absent by construction.
- `zmod_fourier_inversion` proves normalized Fourier inversion on `ZMod (3^a)` from
  `AddChar.sum_mulShift`.  `levelSign_eq_fourier_slice` applies it to least-residue parity;
  `tstep_iterate_lt_three_pow` supplies the essential fact that the slice iterate is its own
  representative below `3^a`.

Exact scoped gate:

```text
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-slicefourier \
  --target CollatzMoonshot.Conjugacy.SliceFourier \
  --import CollatzMoonshot.Conjugacy.SliceFourier \
  --axioms CollatzMoonshot.Conjugacy.sliceChar_pascal \
  --axioms CollatzMoonshot.Conjugacy.sliceChar_eq_subsliceSum \
  --axioms CollatzMoonshot.Conjugacy.levelSign_eq_fourier_slice

Build completed successfully (8724 jobs).
All three declarations: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also checked:

```text
lake env lean CollatzMoonshot/Conjugacy/SliceFourier.lean
git diff --check
rg -n '\bnative_decide\b|\baxiom\b|set_option maxHeartbeats' \
  CollatzMoonshot/Conjugacy/SliceFourier.lean
```

The direct Lean check succeeds with only the original headline-sorry warning; the hygiene search
has no matches.  The operator-owned untracked `CLAUDE.local.md` was preserved and is not part of
this checkpoint.

## Checkpoint 2: exact Fourier weight and cosine norm

The Fourier coefficient analysis in step 2 is now exact through the pointwise norm formula.
No frozen dependency or headline statement was changed.

- `sum_zmod_eq_sum_range` reindexes a finite `ZMod M` sum by least representatives.
- `gHatZ_eq_geom` identifies the parity transform with the geometric sum of ratio
  `-stdAddChar (-ξ)`.  `stdAddChar_pow_card` and `stdAddChar_ne_neg_one` use the odd order `3^a`
  to prove that the ratio is never one and its `3^a`-th power is `-1`.
- `gHatZ_closed` proves
  `gHatZ a ξ = 2 / (3^a * (1 + stdAddChar (-ξ)))`.
- `stdAddChar_neg_eq_exp`, `one_add_exp_neg_two_mul_I`, and
  `norm_one_add_stdAddChar` supply the half-angle calculation.  Consequently
  `norm_gHatZ_cos` proves exactly
  `‖gHatZ a ξ‖ = 1 / (3^a * |cos (π * ξ.val / 3^a)|)`.
- `gHatZ_zero` isolates the zero frequency as `(3^a : ℂ)⁻¹`, ready to produce the
  `card / 3^a` term in the per-slice estimate.

Exact scoped gate:

```text
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-slicefourier \
  --target CollatzMoonshot.Conjugacy.SliceFourier \
  --import CollatzMoonshot.Conjugacy.SliceFourier \
  --axioms CollatzMoonshot.Conjugacy.gHatZ_closed \
  --axioms CollatzMoonshot.Conjugacy.norm_gHatZ_cos \
  --axioms CollatzMoonshot.Conjugacy.gHatZ_zero

Build completed successfully (8724 jobs).
All three declarations: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also checked `lake env lean CollatzMoonshot/Conjugacy/SliceFourier.lean`, `git diff --check`, and
the scoped `native_decide` / `axiom` / heartbeat hygiene search.  Only the frozen headline sorry
remains in this file.

## Checkpoint 3: harmonic weight bounds and direct sub-slice concentration

The two quantitative inputs that were still open after Checkpoint 2 are now proved.  The frozen
headline remains the sole `sorry` in `SliceFourier.lean`; no frozen dependency, owned file, or
headline statement was changed.

- `norm_gHatZ_le_inv_abs` proves the planned pointwise estimate
  `‖gHatZ a ξ‖ ≤ 1 / |2 * ξ.val - 3^a|`.  The supporting lemma
  `abs_two_mul_sub_le_pow_mul_abs_cos` applies Jordan's sine inequality after reflection about the
  midpoint of the odd modulus.
- `sum_inv_abs_two_mul_sub_le_two_harmonic` splits the odd denominators into two injective families,
  one on each side of the midpoint.  Together with `harmonic_le_one_add_log`, this gives
  `sum_norm_gHatZ_le`: the complete Fourier weight is at most `4 * (a + 1)`.
- `sum_filter_range_dvd_eq` reindexes multiples by their quotient.  Factoring the denominator then
  gives `sum_norm_gHatZ_dvd_le`: frequencies divisible by `3^K` have weight at most
  `3^(-K) * 4 * (a + 1)`.  The statement harmlessly includes frequency zero and is therefore
  stronger than needed for the high-valuation remainder.
- `sum_subsliceWeight` obtains the exact total sub-slice mass from the already-proved character
  decomposition at frequency zero.  This avoids developing a separate Vandermonde identity.
- `subsliceWeight_succ_le` proves that, once `t ≥ j/32` and `4096*k ≤ j`, each consecutive
  sub-slice weight contracts by at least `7/8`.  Iteration and the exact total-mass identity yield
  the required named theorem `subslice_tail_le`:
  `8^r * tail(j/16) ≤ j * 7^r * choose(j,a)`, where `r = j/16 - j/32`.
  This direct upper-tail proof replaces the more elaborate partial-Vandermonde route suggested in
  `SLICE-FOURIER-NEXT.md`.

Exact scoped gate:

```text
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-slicefourier \
  --target CollatzMoonshot.Conjugacy.SliceFourier \
  --import CollatzMoonshot.Conjugacy.SliceFourier \
  --axioms CollatzMoonshot.Conjugacy.subslice_tail_le \
  --axioms CollatzMoonshot.Conjugacy.norm_gHatZ_le_inv_abs \
  --axioms CollatzMoonshot.Conjugacy.sum_norm_gHatZ_le \
  --axioms CollatzMoonshot.Conjugacy.sum_norm_gHatZ_dvd_le

Build completed successfully (8726 jobs).
All four declarations: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also checked `lake env lean CollatzMoonshot/Conjugacy/SliceFourier.lean`, `git diff --check`, and
the scoped `native_decide` / `axiom` / heartbeat hygiene search.  The direct check reports only the
original headline-sorry warning.

## Current blocker and next attack

The remaining crux is step 7, the uniform per-slice estimate.  First turn `subslice_tail_le` into a
normalized real bound
`tail / choose(j,a) ≤ j * (7/8)^(j/16-j/32)` and prove this tends uniformly to zero.  For
`t < j/16`, verify the `SliceCharDecay` window for `(j-1-t, a-k)` under
`j ≤ 4a`, `a ≤ 11j/20`, and `4096k ≤ j`, then apply `h 2` termwise in
`sliceChar_eq_subsliceSum`.  Package this as a good/bad bound for
`sliceChar j a (3^k*u)` when `3 ∤ u`.  Finally split Fourier frequencies by 3-adic valuation,
use `sum_norm_gHatZ_dvd_le` for the high-valuation remainder, prove the suggested uniform
`levelSign` estimate, and copy the Bridge3 slice assembly into the frozen headline theorem.

## Checkpoint 4: uniform Fourier bound and headline complete

The scoped objective is complete: `CollatzMoonshot/Conjugacy/SliceFourier.lean` is sorry-free, and
the frozen theorem `biasDecays_of_sliceCharDecay` is proved with exactly
`[Classical.choice, Quot.sound, propext]`.  No frozen statement or definition was changed.  In
`Bridge3.lean`, the only edits are the explicitly permitted deletion of `private` from
`abs_levelSign_le_card`, `sum_out_levelSet_card`, `sum_levelSet_card`, and
`outOddSet_ratio_le` so the final assembly can reuse them.

- `norm_sliceChar_pow_le_good_add_tail` separates the exact sub-slice expansion into an early
  pointwise term and `subsliceTail`; `subslice_tail_real_le` normalizes the existing integral tail
  inequality to `j * (7/8)^(j/16-j/32)`.
- `exists_norm_sliceChar_pow_le` checks the full `SliceCharDecay` window for every early sub-slice,
  including valuation zero, and proves a uniform low-valuation character bound.
- `exists_abs_levelSign_le` splits Fourier frequencies at `K = j/4096`.  Below `K`, maximal
  powers of three and `divMaxPow` feed the sub-slice estimate; above `K`,
  `sum_norm_gHatZ_dvd_le` supplies the exponentially small weight.
- `tendsto_sliceFourierMajorant` proves the explicit one-variable error tends to zero, and
  `eventually_abs_levelSign_le` packages the uniform central-window estimate.
- `abs_bias_le_of_levelSign` sums the central slices and bounds the complement by `outOddSet`;
  the headline then follows from `outOddSet_ratio_le` exactly as in the Bridge3 assembly.

Exact scoped gate:

```text
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-slicefourier \
  --target CollatzMoonshot.Conjugacy.SliceFourier \
  --import CollatzMoonshot.Conjugacy.SliceFourier \
  --axioms CollatzMoonshot.Conjugacy.biasDecays_of_sliceCharDecay \
  --axioms CollatzMoonshot.Conjugacy.eventually_abs_levelSign_le \
  --axioms CollatzMoonshot.Conjugacy.exists_abs_levelSign_le

Build completed successfully (8726 jobs).
All three declarations: [Classical.choice, Quot.sound, propext]
✅ FORMALIZE-TIER GREEN
```

Also checked `lake env lean CollatzMoonshot/Conjugacy/Bridge3.lean`,
`lake env lean CollatzMoonshot/Conjugacy/SliceFourier.lean`, `git diff --check`, and the scoped
`sorry` / `native_decide` / `axiom` / heartbeat hygiene search.  The operator-owned untracked
`CLAUDE.local.md` remains untouched.  There is no remaining scoped blocker; the next action is the
host completion gate (`box done`).
