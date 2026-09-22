# Bounded formalization: orbit summability and coefficient crossing

Trevor explicitly authorized an Opus treadmill on 2026-09-22 after the
recommendation to formalize this bridge.  This is a separately requested
known-result integration task, overriding DIRECTION's no-routine-port gate
ONLY for the objective below.  It is not authorization to search for or
claim an unconditional Collatz proof.

## Objective and acceptance

Read RESEARCH-2026-09-22-packing-shadow.md completely, then the relevant
existing Lean definitions.  Integrate the paper's chain:

1. Injectivity of iterates on a divergent positive orbit and quantitative
   power-saving orbit packing (reuse existing results where available).
2. Summability of reciprocal orbit values, derived from that packing.
3. Bounded multiplicative +1 correction, hence homogeneous coefficient
   tending to infinity on a divergent orbit; obtain a tail whose every
   prefix coefficient is at least one.
4. Prove the existing FirstCrossing.CrossingExists predicate equivalent
   to the existing NoDivergentOrbit predicate, in their actual namespaces.
   Check exact definitions: do not introduce a shadow definition and claim
   it is the existing target.  For the reverse implication, bounded positive
   orbits eventually cycle, and every positive cycle has coefficient <1.

All four are the acceptance target.  A consumer with an assumed summability
hypothesis is a useful intermediate checkpoint but NOT completion.  No new
axiom, hidden assumption, or weakened target.  Named intermediate sorry
leaves are permitted while working; report exact remaining dependencies.
Do not assume StoppingCorrect, CSTVerified, Conjecture, or cycle exclusion.
Positive nontrivial cycles must remain allowed by this equivalence.

The paper gives elementary explicit constants; any proved power saving
sufficient for summability is acceptable.  Do not optimize constants.
Place modules under appropriate existing FrontA/Rigidity namespaces and
wire the finished bridge into the root build.  Prefer new dedicated files
with minimal edits to existing modules.  Preserve unrelated work.

## Provenance and reuse

The packing mechanism is classical Garcia-Tal, cited in the paper.
A peer implementation exists at https://github.com/msharpe248/collatz,
revision ec8174b567d5cab4960024782210b5f5db02bd3a, notably
lean/Collatz/OrbitSummability.lean and lean/Collatz/NoncontractingTail.lean.
The operator inspected its root LICENSE: MIT, copyright 2026 M. Sharpe.
If adapting its implementation, retain the full required MIT notice and
record provenance.  Do not claim that peer code was verified merely because
its paper says so.  Host clone /private/tmp/collatz-peer-shadow-20260922 is
not guaranteed visible inside the box.  The self-contained repo paper is
sufficient to work independently; do not spend the run repairing network
access or importing the peer's entire project.

## Boundaries, verification, and stop

At most three Opus/low laps, four-hour supervisor duration budget (checked
between laps).  Finish early when the full chain builds and the headline
declarations' transitive assumptions have been checked.  Use box done only
then.  Build the affected modules and root; retain an importable audit file
with #print axioms for the summability theorem and final equivalence.
Commit coherent green checkpoints and update a task-specific HANDOFF file
with the precise next leaf and proof approach for subsequent laps.

Report the mathematical edge established or the precise obstruction, not
sorry counts.  If a paper step fails, record the exact defect and preserve
sound partial work; do not patch the statement into an unrelated theorem.
Angular equidistribution, self-packing entropy improvements, few-run bounds,
new experimental searches, and general cleanup are out of scope.

Host preflight: tree clean at def6293; no active Collatz treadmill.  Lean
4.33.1 shared store inspected; relake plan succeeds and recognizes the
existing independent packages.  No fresh dependency download is needed.
