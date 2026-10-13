# HANDOFF: amusical Sparre--Andersen limit (2026-10-13)

## Concrete advance

Kickoff plan step 1 is now formalized in `CollatzMoonshot/AmusicalSpitzer.lean`.

- `fwdNonposTerm`, `bwdNonposTerm`, `fwdPosTerm`, and `bwdPosTerm` give the four exact
  binomial endpoint masses for the two multiplicative walks.
- `walk_endpoint_ne` proves that neither walk can tie its starting height at positive time,
  reusing the repository's proved `three_pow_ne_two_pow` parity lemma.
- `spitzerTerm_eq_fwdNonposTerm_add_bwdNonposTerm` proves the Haar-duality identity
  `spitzerTerm k = fwdNonposTerm k + bwdNonposTerm k` for `k > 0`, term by term across the
  binomial sum.  On the backward side the tilted mass is exactly
  `choose k o * 2^o / 3^k`.
- `fwdNonposTerm_add_fwdPosTerm` and `bwdNonposTerm_add_bwdPosTerm` prove that each walk's two
  endpoint masses sum to one.  The backward normalization is the binomial identity
  `(1 + 2)^k = 3^k`.

All four new theorems have axiom footprint exactly `propext`, `Classical.choice`, and
`Quot.sound`.  No `native_decide` or new axiom was introduced.

## Verification

Exact commands run:

```text
lake env lean CollatzMoonshot/AmusicalSpitzer.lean
/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-spitzer --target CollatzMoonshot.AmusicalSpitzer
lake env lean /dev/stdin   # #print axioms on the four new theorems
git diff --check
```

The target gate ended `FORMALIZE-TIER GREEN` (8715 jobs).  The only proof-debt warning is the
pre-existing target `windowDensityLimit` at line 124.

## Current blocker

`windowDensityLimit` still has its single disclosed `sorry`.  The route-decisive missing result
is now cleanly downstream of finite-time duality: prove Sparre--Andersen's generating-function
identity for the weighted finite Boolean words underlying `fwdSurv` and `bwdSurv`, then pass to
the boundary using exponential endpoint tails / Abel convergence.  No usable Sparre--Andersen or
Spitzer formalization was found in the mounted Lean reference corpus or sibling repositories.

## Next highest-value attack

State and prove a generic finite weighted cyclic-decomposition lemma for an i.i.d. finite-step
walk with no zero partial sums.  Specialize it first to the forward Boolean walk and derive the
coefficient recurrence

```text
L * survive L = sum_{k=1}^L positiveEndpoint k * survive (L-k)
```

(with the conventional indexing checked against `L = 1,2`).  This recurrence is the algebraic
core of the exponential generating-function identity and avoids measure theory.  Once it is
kernel-checked, repeat the same generic specialization for backward weights; the duality lemmas
landed here will then combine their limiting exponents into `minimaConstant`.
