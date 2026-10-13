# HANDOFF: amusical Sparre--Andersen limit (2026-10-13)

## Concrete advance

An adversarial route review confirmed that the checked-in statements still match the kickoff:
`CollatzMoonshot/AmusicalSpitzer.lean` has exactly one proof obligation,
`windowDensityLimit`, and the proposed two directional renewal recurrences agree with exact
rational enumeration for every length through `7`.  No existing Sparre--Andersen/Spitzer
formalization was found in mathlib, the mounted Lean reference corpus, or sibling repositories.
`LeanPool/CriticalPortraits/CycleLemma.lean` proves the different Raney sum-one cycle lemma; it
is a useful implementation example, but does not discharge the exchangeable-word identity here.

Kickoff plan step 4's summability prerequisite and the final Haar-series assembly are now
formalized in `CollatzMoonshot/AmusicalSpitzer.lean`:

- `spitzerRate` is the square-root moment
  `sqrt (2/3) * (1 + sqrt 2) / 2`; `spitzerRate_nonneg` and
  `spitzerRate_lt_one` prove `0 <= spitzerRate < 1`.
- `spitzerTerm_le_rate_pow` proves the load-bearing geometric estimate
  `spitzerTerm k <= spitzerRate ^ k`.  It uses `min 1 x <= sqrt x`, factors the square root of
  the walk weight, and closes the binomial sum exactly.
- `summable_spitzerSeries` proves summability of the series defining `minimaConstant`.
- `summable_fwdNonposSeries` and `summable_bwdNonposSeries` prove summability of both directional
  endpoint series by Haar duality and nonnegativity.
- `tsum_spitzerSeries_eq_fwd_add_bwd` merges the directional series termwise, and
  `minimaConstant_eq_directionalFactors` factors `minimaConstant` into the two exponential
  limits that the forward and backward Sparre--Andersen arguments must produce.

This is a real analytic dependency of the target, not a change of route.  The finite-word
interface from the preceding lap remains the input to the still-missing combinatorial step.
All audited new headline theorems have axiom footprint exactly `propext`, `Classical.choice`,
and `Quot.sound`; no `native_decide` or new axiom was introduced.

## Verification

Exact commands run:

```text
/Users/gotrevor/personal/bin/lake-base status 4.33.1
/Users/gotrevor/personal/bin/relake plan --from /Users/gotrevor/.lake-base/4.33.1 /Users/gotrevor/src/collatz-moonshot-amusical-spitzer
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer
lake env lean AxiomAudit.lean
git diff --check
```

The cache preflight reported that `/Users/gotrevor/.lake-base/4.33.1` does not exist, so there
was no base store to relake from.  The target gate nevertheless built all 8715 jobs and ended
`FORMALIZE-TIER GREEN`.  The only proof-debt warning is the pre-existing target
`windowDensityLimit` (now at line 444).  `AxiomAudit.lean` was a temporary probe containing
`#print axioms` for the seven new headline theorems and was removed after it passed.

## Current blocker

`windowDensityLimit` still contains the repository's single disclosed `sorry`.  The
route-decisive missing theorem is the weighted Sparre--Andersen cyclic decomposition.  In the
common finite-word language already present, prove for each direction and `0 < L` the
coefficient recurrence

```text
L * survive L = sum_{k=1}^L positiveEndpoint k * survive (L-k).
```

The forward word weight is uniform; the backward word weight depends only on `wordTrueCount`,
so both weights are invariant under cyclic permutation.  Every nonempty contiguous block is
tie-free by the same `3^k != 2^m` argument as `walk_endpoint_ne`.  Those are precisely the two
hypotheses the generic weighted cyclic proof should expose.

Once the recurrences exist, the remaining analytic work is: derive the two survival generating
functions, pass to the boundary using the summability proved this lap, obtain the two directional
limits, multiply them, and rewrite with `minimaConstant_eq_directionalFactors`.

## Next highest-value attack

Prove one generic finite cyclic-decomposition lemma before specializing either walk.  A useful
interface is a finite word with (1) an additive or multiplicative prefix score, (2) no zero score
on any nonempty contiguous block, and (3) a word weight invariant under rotation.  Its weighted
sum statement should directly produce the recurrence above.  Then specialize it using
`fwdPosTerm_eq_word_sum` / `fwdSurv_cast_eq_word_sum` and the backward analogues.  Do not repeat
the library search or the summability argument; both have now been resolved or ruled out.
