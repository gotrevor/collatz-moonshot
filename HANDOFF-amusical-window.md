# HANDOFF: amusical window density (2026-10-13)

## Concrete advance

The Matthews--Watts affine slopes are now explicit and kernel-checked in
`CollatzMoonshot/AmusicalWindow.lean`.

- `amusicalForwardEvenCount` counts the `×3/2` (even) branches of a forward prefix;
  `amusicalBackwardFourCount` counts the `×4/3` branches of a backward prefix.
- `amusicalForwardMultiplier_eq` and `amusicalBackwardMultiplier_eq` identify the recursive
  integral translation multipliers as `3^t * 2^(#even)` and `2^(t + #four)`.
- `amusical_iterate_add_pow_four_mul_exact` and
  `amusicalInv_iterate_add_pow_three_mul_exact` strengthen the prior existential affinity
  lemmas to exact formulas.
- The public slope lemmas `amusical_iterate_add_pow_four_mul_slope` and
  `amusicalInv_iterate_add_pow_three_mul_slope` give slopes
  `4^(L-t) * 3^t * 2^(#even)` and `3^(L-t) * 2^(t + #four)`.

This discharges the explicit-slope blocker named by the preceding handoff, without changing
any ratified definition or target and without adding an axiom, certificate, or heartbeat
override.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalWindow.lean
git diff --check
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-window \
  --target CollatzMoonshot.AmusicalWindow
```

Verdict: `FORMALIZE-TIER GREEN` (8707 jobs). The gate reports the one pre-existing proof debt,
`windowMinDensity`; no new `sorry` was introduced.

## Current blocker

The recursive counters must be connected to the `Fin L → Bool` patterns occurring in
`fwdSurv` and `bwdSurv`, and those patterns must be counted over complete residue systems.
After that bridge, the displayed slopes give the threshold comparison on each class directly.
The final CRT product count and periodic-density squeeze remain downstream.

## Next highest-value attack

Define the forward and backward branch words of a residue, prove that their prefix-cardinality
expressions equal `t - amusicalForwardEvenCount t n` and `amusicalBackwardFourCount t n`, and
prove the exact fiber sizes: each forward word has `2^L` residues modulo `4^L`, while a backward
word with `b` marked positions has `2^b` residues modulo `3^L`. Then translate the two survival
tests literally to `fwdSurv`/`bwdSurv` before introducing CRT or asymptotic counting.
