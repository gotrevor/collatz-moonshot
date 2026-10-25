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

## Current blocker and next attack

The structural identities are no longer the blocker.  The next highest-value attack is step 2 of
`SLICE-FOURIER-NEXT.md`: derive the closed form and norm of `gHatZ`, then prove its total-weight and
`3^K`-divisible-frequency bounds.  Keep the coefficient indexed by `ZMod (3^a)` while proving the
pointwise formula; reindex to `range (3^a)` only for the harmonic-sum estimates.  After that, state
the per-slice estimate with the concentration tail still isolated, then attack the named
`subslice_tail_le` combinatorial lemma.  Do not edit `Ladder.lean`, `Bridge3.lean`,
`SliceDecay.lean`, `SliceSeven.lean`, any `Fourier*.lean`, or §12/§13 files.
