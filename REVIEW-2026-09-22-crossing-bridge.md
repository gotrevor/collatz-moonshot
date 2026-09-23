# Independent operator review: summability to crossing

Reviewed the completed source chain through CrossingEquivalence.lean on
2026-09-22, following the separate OrbitPacking review.  No mathematical
defect found.  This records source review, not a new theorem or a claim
of independent foundational verification.

The critical transitions check:

1. The reciprocal majorant sums over distinct orbit values.  Divergence
   supplies time injectivity; the two cannot be interchanged for cycles.
2. The shell ratios 27/32 and 243/256 are below one.  The uniform bounded
   finite sums suffice for the exponential correction bound; an explicit
   Summable declaration is not needed by the downstream proof.
3. The correction estimate includes reciprocals at even times too, a
   harmless upper bound.  Its fixed positive multiplier lets an eventual
   floor on actual orbit values give an eventual floor on the coefficient.
4. Unboundedness is upgraded to eventual escape using the existing
   exists_floor_of_diverges, not incorrectly identified with it by definition.
5. A minimum is chosen on a finite interval of a coefficient tail; all
   later coefficients exceed the interval's first one.  This correctly
   supplies a true minimum on the infinite tail without compactness.
6. The resulting no-crossing start may differ from the original seed.
   The equivalence is global, as its statement requires, not pointwise.
7. In the reverse implication, positivity of a cycle yields strict
   coefficient contraction.  Repeating the period overcomes any preperiod;
   neither triviality of the cycle nor StoppingCorrect is assumed.

The existing guarded audit in CrossingEquivalence.lean is the persistent
executable check for the chain.  The review also exposes a useful finite
version of the packing argument, developed separately in
RESEARCH-2026-09-22-finite-packing-christoffel.md.

Host replay of `lake env lean CollatzMoonshot/FrontA/CrossingEquivalence.lean`
completed successfully, including the persistent guarded assumption checks.
