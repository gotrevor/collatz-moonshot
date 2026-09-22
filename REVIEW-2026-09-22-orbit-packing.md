# Operator review of the first summability checkpoint

Reviewed source at 774843c, independently of the treadmill's report.
Scope: OrbitPacking.lean and the consumed endpoint bound in
ParityReconstruction.lean.  No defect found in the counting argument.
This does not review the still-in-progress OrbitSummability.lean.

The worker uses weight 2 instead of the paper's 3/2.  The one-step odd
branch t -> (3t+2) modulo 2^k is injective because 3 is coprime to 2^k;
together with the even branch this bounds total weight by 3^m.  No random
parity assumption on the orbit enters.  Translation of the parity trace
and the exact affine identity correctly handle every aligned block.

For the good fibres the pre-existing endpoint bound is sharper than the
paper: T^m(s)<3^r, not merely 2*3^r.  Injectivity is required only on the
set being counted, explicitly present as IterateSeparated.  For the bad
fibres the integer threshold is floor(3m/5)+1, giving the denominator
2^(floor(3m/5)+1).  Integer division in the conclusion is intentional.

Both pieces suffice for summability.  At m=5t+5, divide the block bound
by the shell floor 2^(5t).  The resulting majorant is exactly

    27(5t+6)(27/32)^t + (243/16)(243/256)^t.

Both ratios are strictly below one.  This is a slightly weaker decay
rate than the paper's chosen constants, which is immaterial to the target.
No claim that the original paper's numerical constants follow from this
new bound is intended.

Persistent executable review: scripts/OrbitPackingOperatorAudit.lean.
It checks the actual theorem type, prints its transitive assumptions, and
checks the two rational decay inequalities.  It is not a replacement for
the final audit of the summability and crossing-equivalence chain.
