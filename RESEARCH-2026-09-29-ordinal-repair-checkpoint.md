# Ordinal repair: supply correction and a cubic continuation

Trevor's Goodstein comparison suggests ranking structured proof obligations rather than the integers seen along an orbit.  The current work supplies a more precise place to try that idea, but no decreasing rank for full repair has been found.

## Variable-depth follow-through: account for the reset

[Full-run and reset audit](RESEARCH-2026-09-29-q1-run-macro.md): the long phase can pay for one bad exit, but the target's next full odd/even run has infinite subfamilies above the original start and others below the odd-unit parameter.  Lean now proves the exact exit offset, failure of immediate return to the canonical multiplier family, the next actual run, and one-halving expansion.  It also proves that on fresh normalized states the candidate weight is `8d^4`, so a lower reset weight is equivalent to a smaller `d`.  This rank/reset template has not supplied an induction beyond numerical descent.  A transition preserving and controlling the inherited offset, with full reset cost and terminal condition, remains missing; another fixed-depth extension alone does not qualify.

## Q1 follow-through: a finite-depth strategy is now excluded

[Q1 coalescence and separation](RESEARCH-2026-09-29-q1-coalescence.md) now resolves the bounded-splicing test left by the slope audit.  On `s=240+1024t`, the actual `n` orbit meets the `q1` orbit at times 18 and 11, giving direct 18-step descent.  But for every bound `K`, another hard-family parameter has every `n` iterate through `K` at or above its start and every `q1` iterate through `K` below that start.  Both results are proved in [Q1Coalescence.lean](CollatzMoonshot/Obstructions/Q1Coalescence.lean).  No finite bounded-depth menu of splices into `q1` can cover the family.

The negative construction uses a shared parameter to shadow two different rational dynamics: `q1` approaches `-1/9`, whose first two steps reach the trivial positive cycle, while the actual target's sixth step approaches the negative fixed point `-1`.  Finite positive-integer prefixes then separate by height.  The older `-1/13` construction is retained as a control: it avoids bounded coalescence even on starts with a direct 15-step descent.

This excludes a specified finite-depth mechanism, not adaptive repairs with depth growing with the parameter.  The explicit separated-phase recurrence decreases binary precision while increasing a power-of-three multiplier; the exit transition and a full-state rank remain missing.  The other two arithmetic branches retain their independent open inputs.

## Follow-through: signed extraction and the carry obstruction

The next audit removes a second self-imposed prerequisite.  **A finite signed integer edge flow with boundary `e_n-e_1` already proves convergence.**  Positivity and an identical catalyst return are sufficient construction choices, not necessary hypotheses for extracting convergence.  [SignedFlow.lean](CollatzMoonshot/Obstructions/SignedFlow.lean) proves the equivalence and the stronger result for any nonzero integer multiple of the desired boundary.  It does not construct a new flow; existence is still equivalent to the convergence problem.

The [prefix audit](RESEARCH-2026-09-29-prefix-peel-audit.md) proves on paper that unrestricted semigroup supply can expose **any finite actual prefix** of a 3-free start.  Thus longer peeling alone is not evidence of a terminating repair.  For a fixed central script, an identical-unit return exists exactly when its base endpoint is nonnegative and its input-deficit catalyst has 3-free odd support.  This criterion is optional if the construction instead produces exact signed vertex balance.

The cubic now has an explicit [carry obstruction](RESEARCH-2026-09-29-post-cubic-return-debt.md).  Put `q=T(q1)` for its first auxiliary, with `q1<m<n`.  Induction makes `32q` a known convergent vertex, while

```
T^3(n)=32q-14,
T^4(n)=16q-7,       T(32q)=16q,
T^5(n)=24q-10,      T^2(32q)=8q.
```

The initial gap 14 becomes 7 and then `16q-10`, which is unbounded across the hard CRT family.  [CubicCarry.lean](CollatzMoonshot/Obstructions/CubicCarry.lean) proves these finite-prefix relations, the unbounded two-step gap, `T^6(n)=18q1+1`, and the conditional convergence of the neighbor.  This rules out this bounded-gap argument, not every coupled rank.

Using all lower auxiliary paths, the projected post-cubic residual reduces modulo their known edge boundaries to `e_1-e_(T(a))`.  The [basin-cut audit](RESEARCH-2026-09-29-signed-basin-obstruction.md) explains why inserting more scalar units or merely counting low labels does not close that residual.  The actual second frontier is still the missing connection.  No complete repair or decreasing full-state rank has been found.

## Correcting the prerequisite

The earlier roadmap made uniform borrowing from U2/U8/U13 a prerequisite.  That restriction was imposed by our experimental palette.  For the Collatz route, [Applegate–Lagarias, Theorem 1.1](https://arxiv.org/html/math/0411140) already implies that any finite multiset of odd labels prime to 3, together with any number of factors 2, is contained in a finite value-one word.  Multiply the multiset by a semigroup representation of the inverse of its value.  No convergence hypothesis is used.  The [supply addendum](RESEARCH-2026-09-29-unrestricted-supply-addendum.md) proves the exact criterion and distinguishes known literature from repo Lean results.

A signed central relation must still avoid 3-divisible borrowed labels.  Actual positive certificates of 3-free scalar value automatically do so; arbitrary signed relations need a separate support check.  Proving convergence for every 3-free start would cover all positive starts by stripping factors of 2 and taking one odd step when the odd part is divisible by 3.

Restricted closure remains useful for small executable witnesses and for studying the palette.  It will not gate the main rank search.  Supply existence is known; useful size bounds and boundary control are not.

## Why infinite affine families are not enough

[AffineQLift.lean](CollatzMoonshot/Obstructions/AffineQLift.lean) proves that **every individual Q identity** admits an unbounded affine deformation preserving positive odd 3-free labels and both smaller-input inequalities.  Two particular single-shared-label configurations also deform simultaneously.  This does not prove compatibility of arbitrary diagrams or prescribed progressions.

The exact `affine_scan.py closure` test excludes all eight direct matches of the four required input progressions to either existing supplied-head progression.  Generic dilation supplies another level on sparse subclasses, but that mechanism is automatic and does not establish closure.  It is retained as a calibration instrument, not a new main target.  [Root matching](RESEARCH-2026-09-29-affine-root-classification.md) gives a sharper description of which divisibility conditions a proposed affine rule must meet.

## A genuine continuation beyond the two-factor obstruction

Write a=T(n) and v=T(5n)=5a-2.  A complete rational-function classification shows that a positive affine single-Q identity

    r_v r_Q = r_a r_E

has only the unchanged pair (Q,E)=(a,5a-2) or the nonintegral pair ((3a-1)/6,(5a-2)/6).  Thus one affine Q move cannot perform the next direct replacement.  This classification is a paper argument in the [continuation note](RESEARCH-2026-09-29-head-continuation.md), not a Lean theorem claim.

A three-factor identity escapes that precise obstruction:

    r_(5a-2) r_((3a-1)/64) r_(5(2a-7)/93)
      = r_a r_((3a+1)/58) r_((2a-7)/21).

Both sides reduce to 4(2a-7)/(3(9a+61)).  On

    n = 25542881863 + 39026668800 s,  s >= 0,

all four auxiliary labels are positive odd integers prime to 3 and strictly below the supplied smaller endpoint m.  This is a variable cubic, outside the previous fixed-C5 action language.  Its scalar identity, domain/bounds, frontier identities, connection to the original family, and growth congruence are now proved in [CubicPeel.lean](CollatzMoonshot/Obstructions/CubicPeel.lean).

The first K32 version was rejected as the main target because it forced descent at step 7.  The K64 version above satisfies

    T^6(n)+1 = 4(8081927465 + 12348281925 s).

The coefficient of s inside the parentheses is odd, so a residue choice gives arbitrarily many following odd steps.  The new local identity therefore remains applicable on a subclass with unbounded initial growth.

After the cubic, the virtual frontier is 16m and the actual frontier is T^2(n).  Both the larger numerical frontier and the lower auxiliary boundary must still be accounted for.  This is a second local replacement, not a complete repaired flow.

## Where the Goodstein idea fits precisely

For smaller-input borrowing, a finite multiset of pending labels already has the ordinal rank

    alpha(O) = sum in decreasing u of omega^u * multiplicity_O(u).

Replacing one obligation u by finitely many obligations strictly below u decreases alpha, regardless of how many children are created.  All these ordinals lie below omega^omega.  This is the multiset extension of strong induction; it needs neither hereditary-base arithmetic nor epsilon_0.  Its missing input was rule coverage, not well-foundedness, and unrestricted supply now bypasses that existence question.

Full repair needs a richer state.  At minimum it must retain the actual frontier, the virtual construction being replaced, the signed vertex defect, and unpaid factor/return obligations.  Even factors need source vertices: a bare exponent of 2 does not specify a flow.  The current two local replacements lower the number of remaining virtual odd edges but raise the largest defect vertex and create additional return obligations.  Counting only the virtual edges is not a rank for the full state.

There is a useful way to avoid charging the enormous supplied unit at every internal move.  Work in **completed blocks**: a block borrows a common unit W, executes a finite central relation, and returns the identical W.  Its boundary cancels between block endpoints.  A rank on the base configuration can decrease across the completed block even if intermediate words explode.  The known supply theorem can justify the finite borrowing subroutine, without a uniform word-size bound.

This cancellation is available only when W really is returned.  In our partial peels, newly borrowed inputs have been consumed; the return obligations are still open.  Dropping them would manufacture a decrease.  The next acceptance test is therefore a precisely specified block that (1) starts and ends with nonnegative certificates, (2) closes its borrowing debts, (3) preserves the intended scalar, and (4) decreases a rank of the complete remaining defect.  An invariant class of states generated by the construction suffices; there is no need to normalize every possible scalar certificate.

If every nonbalanced state in that invariant class admits such a block, and terminal states have boundary e_n-e_1, well-founded induction produces a finite nonnegative flow from n to 1.  That would prove convergence.  Neither the required rank nor the block-existence theorem has been established.

## Original completed-block target, now optional

One sufficient architecture is to take the exact post-cubic residual and seek a completed block with the common-unit return condition.  The signed-flow result above now permits a second architecture: construct an exact finite signed boundary to a known convergent vertex, without positivity or catalyst-return conditions.  A candidate ordinal assignment must compare the actual before/after residual, including debt; higher ordinal notation alone is not progress.  Do not enlarge the finite example census or treat additional affine families as evidence of uniform termination.  The pairwise and anchored-operator branches retain their separate missing estimates.

## Validation

The two changed persistent CLI suites pass **17 tests**.  The root Lean build passes after restoring the exact intended even endpoint m; the existing CI audit now contains declaration-type and definition anchors for that endpoint and the explicit growth congruence.  Both new modules are root imports.  The paper classifications and literature supply lemma remain explicitly distinguished from the Lean results.

## Current research gate

A successor proposal must exhibit an arithmetic transition connecting the actual frontier to a known convergent path, or a precisely specified signed-defect rewrite with a proved full-state decrease.  Neither exposing another finite prefix nor canceling the lower auxiliary debts qualifies.  A coupled multiplier/carry state must retain the additive offset and handle the parity split displayed above; no such transition is currently proved.  The pairwise-cycle and anchored-operator branches retain their independent missing estimates.

## Follow-through validation

The existing repair CLI includes the 14-gap and sixth-iterate regression with hand-derived numeric anchors; its 13 subprocess tests pass.  Both new Lean modules are root imports.  The existing CI audit consumes the exact signed-flow definitions and theorem types, and the carry definition and unbounded-gap theorem.  Paper-only statements remain explicitly labeled above.

### Earlier slope gate, now resolved for Q1 at bounded depth

The [slope audit](RESEARCH-2026-09-29-affine-coalescence-slope.md) applies the already-known fixed-tail obstruction to all ten supplied hard64 families.  Nine have an outside prime in the ratio of their slope to the target slope, so no infinite parameter subclass can merge their ordinary orbits with the target at uniformly bounded depths on both sides.  This includes the original smaller endpoint `m`.  Only `q1` passes the necessary test, with `128q1=9n+1` and `T^7(n)=27q1+2`.  These identities do not establish a meeting.  The Q1 investigation above now gives both a sparse positive class and an all-depth obstruction to a uniform bound; methods with growing depth remain outside the exclusion.  The finite-exception theorem is a paper argument, and all ten exact slope ratios are checked by the existing CLI regression suite.
