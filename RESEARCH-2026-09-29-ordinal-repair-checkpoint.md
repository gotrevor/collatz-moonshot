# Ordinal repair: supply correction and a cubic continuation

Trevor's Goodstein comparison suggests ranking structured proof obligations rather than the integers seen along an orbit.  The current work supplies a more precise place to try that idea, but no decreasing rank for full repair has been found.

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

## Current next target

Take the exact post-cubic residual from the continuation note and seek a completed block with the common-unit return condition.  A candidate ordinal assignment must compare the actual before/after residual, including debt; higher ordinal notation alone is not progress.  Do not enlarge the finite example census or treat additional affine families as evidence of uniform termination.  The pairwise and anchored-operator branches retain their separate missing estimates.

## Validation

The two changed persistent CLI suites pass **17 tests**.  The root Lean build passes after restoring the exact intended even endpoint m; the existing CI audit now contains declaration-type and definition anchors for that endpoint and the explicit growth congruence.  Both new modules are root imports.  The paper classifications and literature supply lemma remain explicitly distinguished from the Lean results.
