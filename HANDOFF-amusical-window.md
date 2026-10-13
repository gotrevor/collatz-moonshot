# HANDOFF: amusical window density (2026-10-13)

## Concrete advance

The first load-bearing part of the Matthews--Watts residue argument is now kernel-checked in
`CollatzMoonshot/AmusicalWindow.lean`.

- `amusical_add_four_mul` and `amusicalInv_add_three_mul` give the exact one-step translation
  laws on residue classes.
- `amusical_iterate_add_pow_four_mul` proves that, for `t ≤ L`, the forward iterate on every
  class modulo `4^L` is affine in the class parameter, with a positive integral slope.
- `amusicalInv_iterate_add_pow_three_mul` proves the corresponding statement for inverse
  iterates on classes modulo `3^L`.

This discharges the branch-stability/affinity part of kickoff steps 1 and 2 without adding an
axiom, heartbeat override, or certificate. The ratified definitions and target statement are
unchanged.

## Exact verification

```text
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-window \
  --target CollatzMoonshot.AmusicalWindow
```

Verdict: `FORMALIZE-TIER GREEN` (8707 jobs). The gate reports the one pre-existing proof debt,
`windowMinDensity`; no new `sorry` was introduced. `git diff --check` also passes.

## Current blocker

`windowMinDensity` still needs the quantitative content suppressed by the existential slopes:
identify each forward slope as `3^t * 2^(2L-k)` and each backward slope as
`2^k * 3^(L-t)`, relate `k` to the Boolean prefix used by `fwdSurv`/`bwdSurv`, and count the
resulting good classes. The present affine lemmas are deliberately exact but do not yet expose
those exponents, so they alone cannot decide which comparisons stabilize above a threshold.

## Next highest-value attack

Refine the two iterate lemmas with an explicit branch counter (or a Boolean word plus its prefix
cardinality), proving the exact slopes. Then prove the threshold equivalences on each residue
representative. Keep forward and backward counting separate; combine only afterward via CRT for
modulus `4^L * 3^L`. Once the good-class cardinality is expressed as
`M * fwdSurv L * bwdSurv L`, reuse the squeeze shape of `windowMinDensity_one`.
