# HANDOFF: amusical cycle structure (2026-10-14)

## Concrete advance

The algebraic backbone of Theorem A-star is now proved in
`CollatzMoonshot/AmusicalCycleBound/Step.lean`:

- `stepDefect` packages the additive error in
  `2 ^ stepBits x * amusical x = 3 * x + stepDefect x`.
- `stepDefect_eq_zero_of_even`, `stepDefect_of_odd`, and `stepDefect_mem` prove that the defect
  is zero on even steps and is exactly `1` or `-1` on odd steps.
- `sum_stepBits_eq_add_filter_card` identifies `e - p` with the number of odd steps.
- `mul_prod_iterate_succ` and `prod_iterate_succ_eq_of_cycle` prove the orbit-product reindexing
  without a permutation construction.
- `amusical_cycle_product_identity` multiplies the cleared step identities and cancels the cyclic
  shift, giving the exact product identity needed for both inequalities in
  `amusical_cycle_min_bound`.

The ratified target statements are unchanged. Four target proofs remain:
`amusical_cycle_min_bound`, `noNewCycles_of_search`, `cycleMinBound_31866`, and
`amusical_noNewCycles_199`.

## Exact verification

```text
lake build CollatzMoonshot.AmusicalCycleBound.Step
# Build completed successfully (8715 jobs).

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-cycles \
  --target CollatzMoonshot.AmusicalCycleBound
# Build completed successfully (8717 jobs); FORMALIZE-TIER GREEN.
# Four disclosed target sorries remain.
```

## Current blocker

Theorem A-star now reduces to bounding the product's odd factors. For every orbit member
`z >= m >= 1`, cross-multiply `3m-1 <= 3z+d <= 3m+1` against `3z`, apply
`Finset.prod_le_prod` on the odd-step filter, and cancel the positive orbit product. The integer
sign/positivity bookkeeping and arranging the two products are the remaining formal burden.

## Next highest-value attack

Add lower and upper cross-multiplied factor lemmas to `Step.lean`, then apply them over the odd
filter. Rewrite the exponent with `sum_stepBits_eq_add_filter_card` and discharge
`amusical_cycle_min_bound` directly from `amusical_cycle_product_identity`.
