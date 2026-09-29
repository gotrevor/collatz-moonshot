```sh
uv run --quiet --with pytest python3 -m pytest experiments/test_research_lifts.py experiments/test_catalytic_palette.py experiments/test_pair_denominators.py experiments/test_pair_ordering.py experiments/test_borrowability_descent.py -q
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

## Follow-through: the concrete 71 repair

The earlier next targets above describe the first checkpoint, and are superseded here.  The [restricted palette now repairs 71](RESEARCH-2026-09-28-palette-lattice.md): an exact integer relation supplies 254 quadratic applications, and a constructible value-one word supplies every needed factor.  Nine U8 insertions, three U13 removals and three reverse cubics complete the 269-move main sequence.  Building and returning the borrowed word expands the entire certificate to 3,281 allowed moves.  The saved Python witness is independently replayed, with every intermediate availability check enforced.  The theorem `seventyOne_repair_restricted` in `Repair71.lean` now proves this reachability.  Its frozen relation permits only the specified palette; the executable interpreter checks all intermediate removals and the exact final multiset, then its general soundness theorem turns acceptance into allowed reachability.

The [quadratic neighbor algorithm](RESEARCH-2026-09-28-quadratic-divisors.md) is now a complete divisor enumeration for a fixed input generator.  This removes an expensive search bottleneck without introducing a global label cutoff in the enumeration itself.

`OrbitPrefix.lean` proves the arbitrary dyadic-ray plus finite-prefix identity: all transfer defect is concentrated at the endpoint, even when orbit states repeat or overlap the ray.  This advances the sharp-constant proof independently of the catalytic result.  A nonperiodic starting state may enter a later cycle, so prefix distinctness needs a separate first-maximum or unbounded-orbit argument.

The three branches still have separate general gaps.  Catalytic repair needs a target-selection or decreasing measure that does not assume a known terminating path.  Pairwise transport needs an inequality using integer admission and actual ordering together.  The operator route needs an independent arithmetic estimate, because the transport extremizers encode the orbit's future height.  A finite repair of 71 does not settle any of those general gaps.

The [first-hit and norm audit](RESEARCH-2026-09-28-sharp-anchored-next.md) supplies the next precise operator theorem blueprint, including eventual-cycle cases and summability before real norm comparisons.

The [pair-ordering pass](RESEARCH-2026-09-28-pair-ordering.md) finds a primitive positive rational five-cycle with six inversions, refuting equality in the general `I≥m−1` bound.  Its actual cycle and inversion count are recorded in `PairOrderingControl.lean`.  The lower bound is automatic permutation theory; integer spacing adds only `I≤sum O`, which does not exclude a nontrivial cycle.  These observables alone no longer warrant an active proof lane.

The [borrowability height test](RESEARCH-2026-09-28-borrowability-height.md) rules out a simple induction from smaller factors.  The 23 obstruction is proved in Lean for an unbounded companion; the exact 85 control also prevents rescuing this particular one-step induction merely by supplying every factor up to the largest unit seed, 83.  An enlarged finite base beyond 85, a multi-step descent, or a nonmonotone construction remain outside this negative result.

Follow-through validation: the research-lifts, catalytic-palette, pair-denominator, pair-ordering and borrowability CLI suites contain 43, 10, 6, 7 and 3 passing tests respectively.  The new Lean statements preserve restricted reachability, the actual transfer operator and actual rational shortcut dynamics.  The full root build includes all new formal results.  No result here proves general Collatz convergence or excludes a nontrivial integer cycle.
