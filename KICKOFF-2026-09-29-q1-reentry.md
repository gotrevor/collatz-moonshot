# Q1 exit and reset: bounded formalization

Own only `CollatzMoonshot/Obstructions/Q1Reentry.lean` and
`HANDOFF-2026-09-29-q1-reentry.md`.  Preserve all three definitions and all
eight frozen theorem statements exactly.  Parent owns root import, research,
CLI, and CI consumers.  Helpers may be added in this module.  No convergence
assumption, theorem weakening, unrelated refactoring, or successor task.

This records specific obstructions discovered while looking for a variable-depth
repair: direct re-entry fails, a completed target run can expand its proposed
parameter, and resetting the auxiliary to the original normalized form charges
ordinary numerical size again.  It does not exclude all adaptive repair.

The module imports Q1Coalescence, hence actual FrontB.tstep and its parity
lemmas.  Local private parity lemmas may be repeated.  Keep powers and large
products opaque in omega; use ring for polynomial equalities.  The prior worker
hit long omega timeouts after indiscriminate unfolding.

## Proof route

Put `v=3^r*u`, `M=8*3^r`.  For odd positive u, v is odd and positive.
The pre-exit pair is `(16*9^r*u−1, 1+2*v)`.  Both take two odd shortcut steps;
the outputs are `A=36*9^r*u−1`, `B=(9*v+7)/2`.  Derive `2B=9v+7`
from oddness and eliminate division with this identity.  Then
`2(A+1)=M*(2B−7)` and `B≥8`.

For no canonical re-entry, prove the integer inequalities
`A+1<M*(B−1)` and `M*(B−1)<3*(A+1)`.
If `A+1=8*3^j*(B−1)`, the first forces `j<r` by monotonicity of
powers, and then `3*(8*3^j)≤8*3^r` contradicts the second.  Handle r=0
automatically by the same inequality.  This avoids rational division.

`A+1=4*3^(2r+2)*u`, so the next two target steps are odd, giving
`3^(2r+4)*u−1`.  Prove `T^[k](2^k*x)=x` by induction for the
halving theorem.  For u=3 mod4 the latter numerator is 2 mod4 because
`3^(2r+4)=9^(r+2)=1 mod4`; the next step is even and its value exceeds u
since this coefficient is at least81.  Only the exact endpoint and expansion
are frozen, not a valuation API lemma.

For the rank, `phaseWeight(8d−1,d+1)=8*d^4` for positive d, by ring after
eliminating natural subtraction.  Positive powers preserve and reflect strict
order, giving the reset equivalence.  This is a calibration of this rank,
not an impossibility theorem for other ranks.

Hand anchors for the actual map: r=1,u=1 gives `(143,7)→(323,17)` across
the exit.  r=0,u=3 gives `oddExitA=107→161→242→121>3` after exit.
r=0,u=1 gives `35→53→80→40→20→10→5`, so k=4 and x=5.

Run a module build and root build, commit green, then `box done --green`.
Only claim validation after the process exits successfully.  At most three
Opus/low laps with a 35-minute supervisor limit, no Aristotle.  No successor.
