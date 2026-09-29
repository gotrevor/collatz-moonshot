# What catalytic repair adds to an induction search

Trevor's question: could a few large repairs reveal a reusable induction, and what distinguishes this from something a clever graduate student would already try?  Yes, selected examples can be useful discovery data.  The previous dismissal of additional numerical examples was too broad.  The distinction is what structure is extracted from them.

## Prior art and the actual contribution so far

[Applegate and Lagarias, The 3x+1 Semigroup](https://arxiv.org/html/math/0411140), especially sections 1 and 2, explicitly discuss ordinary descent induction, why it would prove Collatz, and their weaker construction using artificial multipliers.  Their theorem already gives algebraic certificates for every positive integer.  Neither induction nor lifting this relaxation should be presented as an unprecedented idea.

[Yolcu, Aaronson and Heule, An Automated Approach to the Collatz Conjecture](https://arxiv.org/abs/2105.14697) already study string rewriting and automated termination proofs for Collatz and related systems.  Rewriting, searching for a decreasing measure, and automated proof discovery are also established approaches.  This is a focused comparison, not an exhaustive priority search.

Our concrete research object is a different rewriting space: commutative multiplicative certificates, a restricted family of unit insertions, legally supplied catalysts, and the missing vertex-balance condition.  A signed integer relation and a borrowability derivation can be searched separately and then combined into a positive executable repair.  The 71 certificate demonstrates that this machinery can cross an obstruction that defeated the earlier palette.  These facts are useful local results and research infrastructure; they do not yet supply a new general termination mechanism.  Their novelty in the literature has not been established.  The relation-lattice/catalyst reduction is elementary commutative rewriting, not a claim of a new algebraic theory.

The precise hard step is a uniform, oriented repair of canonical construction steps that either reaches actual vertex balance or recursively reduces a well-founded proof state.  Unrestricted value-one insertion makes scalar equivalence trivial on the 3-free part, and complete scalar connectivity would still not select a trajectory.  Borrowed factors, factor count and maximum label can all grow.  A finite repair to a supplied known path therefore does not establish this hard step.

## A better role for large examples

Use the same constructive input repeatedly: for n=64k+7, the artificial multiplier 5 followed by six actual steps reaches m=(45n+5)/64<n.  Preserve this construction history and distinguish its inverse-5 word, virtual six-step prefix, and smaller-endpoint certificate.  Do not mix unrelated certificate-generating methods and then call a shared numerical feature an induction.

Suggested structured families are n=2^j+7 and n=2^j-57 for j>=6, both lying in 7 modulo 64.  They vary long runs above the fixed low six bits; they are experiment inputs, not conjectured solved families.  Include unrelated held-out k as controls so a pattern fitted to these binary families does not masquerade as a general rule.

The object to compare is the repair derivation.  Separate construction/return of borrowed words from the central repair, align repeated blocks, and ask whether a block admits a symbolic parameterization and a recursive call to a strictly simpler proof state.  Numerical size alone is not the progress metric.  The previous bound n<69*6^L for a meeting with the virtual smaller endpoint already excludes a uniform bounded-length coalescence table for the entire progression; this particular strategy needs growing/adaptive constructions.

Known trajectories may guide discovery.  Once a candidate rule has been extracted, freeze it and test it on fresh starts without supplying their target trajectories to the repair search.  A path certificate for a smaller integer is a legitimate induction hypothesis, and must be distinguished from leaking the desired path for n.  Finite holdouts still do not prove universality: the decisive next deliverable is a symbolic repair lemma with its exact arithmetic domain, catalyst-availability proof and decreasing recursion measure.  A recurrence that leaves one exceptional branch uncontrolled is an explicitly partial result.

The appropriate claim today is a concrete, testable way to look for such a lemma.  We do not yet have a theorem showing that this approach overcomes the known induction barrier.
