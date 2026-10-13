# HANDOFF: amusical Sparre--Andersen limit (2026-10-13)

## Concrete advance

Kickoff plan step 2 is now formalized in `CollatzMoonshot/AmusicalSpitzer.lean`, and the exact
finite-word interface needed for step 3 is in place.

- `wordTrueCount`, `wordTrueCount_cons`, and `sum_boolWords_succ` set up first-letter
  decomposition of Boolean increment words.
- `sum_boolWords_by_trueCount` proves, for values in any additive commutative monoid, that a
  sum over length-`L` Boolean words depending only on the number of marked letters is the
  corresponding binomial sum.  Its induction is the finite Pascal recurrence.
- `fwdPosTerm_eq_word_sum` and `bwdPosTerm_eq_word_sum` rewrite both positive-endpoint
  probabilities as weighted sums on exactly the same Boolean-word spaces used by survival.
- `fwdSurv_cast_eq_word_sum` and `bwdSurv_cast_eq_word_sum` rewrite the rational survival
  quantities, after casting to reals, as those same finite weighted sums with `FwdGood` and
  `BwdGood` indicators.

Together with the previous lap's endpoint partition and Haar-duality lemmas, all four finite
probabilities entering Sparre--Andersen now share one explicit sample-space representation.
All five new headline theorems have axiom footprint exactly `propext`, `Classical.choice`, and
`Quot.sound`.  No `native_decide` or new axiom was introduced.

## Verification

Exact commands run:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer
lake env lean /dev/stdin   # #print axioms on the five new headline theorems
git diff --check
```

The target gate ended `FORMALIZE-TIER GREEN` (8715 jobs).  The only proof-debt warning is the
pre-existing target `windowDensityLimit` at line 253.

## Current blocker

`windowDensityLimit` still has its single disclosed `sorry`.  The route-decisive missing result
is the weighted cyclic decomposition behind Sparre--Andersen.  In the new common finite-word
language, prove for each walk the coefficient recurrence

```text
L * survive L = sum_{k=1}^L positiveEndpoint k * survive (L-k).
```

The common sample spaces and weights are now kernel-checked; what remains is the genuinely
combinatorial partition/cycle lemma, followed by the analytic boundary passage.  No usable
Sparre--Andersen or Spitzer formalization was found in the mounted Lean reference corpus or
sibling repositories.

## Next highest-value attack

Define word concatenation, cyclic rotation, and strict-positive partial sums for a generic
finite real-valued increment alphabet.  Prove the weighted finite cyclic-decomposition lemma
first (weights must be invariant under permutation), then specialize it using
`fwdPosTerm_eq_word_sum` / `fwdSurv_cast_eq_word_sum` and their backward counterparts.  Check
the recurrence at `L = 1,2` by kernel evaluation before beginning the generating-function and
Abel-limit layer.
