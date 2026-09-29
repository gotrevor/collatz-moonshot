```sh
uv run --quiet --with pytest python3 -m pytest experiments/test_research_lifts.py experiments/test_catalytic_palette.py experiments/test_pair_denominators.py -q
```

# Three independent branches: delegated checkpoint

Trevor requested cheaper delegation while the main session develops mechanisms.  Three Sol workers handled the catalytic probe, pairwise audit, and operator proof specification.  A bounded Opus/low treadmill completed the operator formalization in one lap.  The main session reviewed the statements, developed the borrowing reduction, and integrated the disjoint files.

## Catalytic repair

The new constructive reduction is [integer relation witnesses plus borrowability witnesses](RESEARCH-2026-09-27-borrowable-catalysts.md).  Any finite integer combination of allowed rule differences supplies an explicitly computable common catalyst.  If the permitted unit rules can supply its factors, that catalyst can be inserted and removed legally.  This separates relation generation from factor availability.  The general argument has an independent paper review; it is not yet a Lean theorem.

The [palette probe](RESEARCH-2026-09-27-palette-delegation.md) proves a necessary count recipe for the published 71 certificate: net nine U8 insertions, three U13 removals, and three reverse essential cubics.  This is algebraic count bookkeeping, not a repair path.  Six bounded rounds of quadratic borrowability produce 526 labels up to 3077, with five labels on the known 71 path still absent.  The full derivations are saved in `experiments/borrowable_palette_71.json`; absence from this bounded search is not an obstruction.

Next bounded target: an integer relation witness for the remaining source-to-target difference, together with a legal source of its catalyst.  Even success at 71 would leave the independent general problem: a terminating procedure that reaches vertex balance without assuming a target trajectory is known.

## Pairwise cycle arithmetic

The [odd-prime ledger](RESEARCH-2026-09-27-pair-denominators.md) separates forced denominator deficit from deeper cancellation.  For each prime dividing the common denominator, the Vandermonde valuation is exactly excess minus deficit.  A real positive primitive cycle with denominator 35 has a pair gap of 15/7, refuting the tempting claim that every pair retains each denominator prime.  Its closure, positivity, distinctness, reduced denominators and gap are proved in `PairDenominatorControl.lean`.

The general valuation identity remains paper-side.  An inequality showing that some prime retains a net deficit is unproved; even proving it would only characterize integer admission, not exclude an integer cycle.  This branch still needs a cycle-excluding inequality combining arithmetic with closure and real ordering.

## Positive-series operator

`AnchoredCut.lean` now proves the exact finite-cut transfer identity for arbitrary real coefficients and the weighted anchored lower bound for nonnegative coefficients.  All three frozen theorem statements were preserved.  The [independent audit](RESEARCH-2026-09-27-anchored-audit.md) checks the even-anchor and eventual-cycle cases.

The full sharp infimum formula, including orbit-cut construction and dyadic-ray extremizers, remains paper-side.  The finite-cut proof is generic transport.  This branch's mathematical gap is an independent arithmetic bound on the anchored constant, together with periodic-state exclusion; changing the power weight merely changes the power of the same orbit-height quantity.

## Validation

The persistent CLI suites passed 49 tests: 38 existing controls, five catalytic controls, and six odd-prime controls.  Both new Lean modules were included in a successful root build.  No general Collatz convergence or cycle exclusion is claimed, and the general proof-campaign gate remains unchanged.
