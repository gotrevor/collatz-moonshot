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

## Current blocker and next attack

The pointwise Fourier coefficient is no longer the blocker.  Next prove the planned comparison
`‖gHatZ a ξ‖ ≤ 1 / |2 * ξ.val - 3^a|` (with the integer/real subtraction represented without
natural truncation), using `Real.mul_le_sin` after reflecting around `3^a/2`.  Reindex by
`sum_zmod_eq_sum_range` to derive the total odd-harmonic bound and then the weight bound on nonzero
frequencies divisible by `3^K`.  After that, state the per-slice estimate with the concentration
tail isolated and attack `subslice_tail_le`.  Preserve all operator freeze/no-edit constraints.
