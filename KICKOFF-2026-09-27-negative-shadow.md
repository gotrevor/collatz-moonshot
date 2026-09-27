# Bounded formalization: negative-shadow obstructions

Trevor requested Lean formulations and proofs of the negative results on 2026-09-27.  This is a known-result formalization task, separate from the search for a new Collatz mechanism.  The research gate in DIRECTION does not prohibit recording a proved obstruction.  Launch authorization is tracked by the attended session separately.

## Concrete scope

Read `RESEARCH-2026-09-27-negative-shadow.md` and `CollatzMoonshot/Obstructions/NegativeShadow.lean`.  Complete that module, preserve its definitions and every headline statement, and import it from the root build.  The general statements are deliberately rational-valued: no real supremum machinery is necessary, because the claimed least upper bound is rational.

Acceptance requires all of these mathematical claims:

1. `catalog_ten_six`, `catalog_ten_three`, `catalog_ten_increases`: the exact finite catalog fails at `6 -> 3`.  The existing FrontB numerator and odd count bind it to the repo's parity-word convention.  Duplicates in the list do not affect a maximum.
2. `score_le_square`, `scoreValues_isLUB`, `envelope_not_nonincreasing`: the all-rational envelope is exactly `(n+1)^2` and fails the claimed monotonicity above 1.
3. `witness_admissible`, `witness_reaches_neg_one`, `witness_weighted_gt`, `weighted_witnesses_unbounded`, `inverse_basin_scores_unbounded`: explicit primitive references in the actual rational inverse basin produce unbounded weighted scores at 1.

No new axioms, additional conjectural hypotheses, restricted n/p ranges, or replacement of an actual score by its upper bound.  Intermediate named leaves are welcome.  Refute and report a faulty target rather than weakening it silently.  Keep all proof dependencies in this module during the bounded task; no hiding unfinished helper proofs outside the completion scope.  Preserve the statements by name and text; ask the architect before changing one.

## Proof plans

For the bound use `pow_padicValNat_dvd`, positivity of `bn+a`, and `Nat.le_of_dvd`; then cast to Q and compare `(bn+a)/a` with `n+1`.

For sharpness choose `q=2^k`, let b be the largest positive odd integer <= q/(n+1), and a=q-b*n.  Then q-(n+1)b is between 0 and 2(n+1), a>=b, and gcd(a,b)=gcd(q,b)=1.  For sufficiently large q the score is q^2/a^2 and exceeds any rational strictly below `(n+1)^2`.  An epsilon proof or a direct upper-bound test proves IsLUB.  It may be easier to define b as `2*((q/(n+1)-1)/2)+1` once q/(n+1)>0.  Prove the rounding bounds explicitly.  Powers of 2 eventually exceed any rational bound; standard Archimedean power lemmas avoid limits.  `padicValNat.prime_pow` evaluates the score on q.

For witnesses use `A_p=2*4^p-3^p`, `B_p=3^p`.  Both positivity and `B_p<=A_p` follow from `3^p<=4^p`.  A_p is coprime to 3, so to B_p; B_p is odd.  Also A_p+B_p=2^(2p+1).  After casting, the weighted score is

`3^p * (2*4^p)^2/(2*4^p-3^p)^2 > 3^p`.

For the rational dynamics prove two steps take witnessRef(p+1) to witnessRef(p).  Numerators are reduced odd at the first step and reduced even at the second step.  The closed pair map is `(3*x+1)/4`; its rational algebra alone is insufficient without checking numerator parity.  Use Rat numerator/denominator lemmas plus the gcd facts.  Induct on p to get the iterate theorem.  At p=0 the reference is -1 and the iterate count is 0.

Finally exponential unboundedness gives the range theorem, and the admissibility/dynamics theorems give the inclusion into the genuine inverse-basin set.

Concrete anchors: score(3,1,1)=16; score(9,5,3)=1024/25; score(14,2,1)=64; rationalStep(-5/3)=-2; witness(2)=(23,9); weighted scores p=0,1,2 are 4,192/25,9216/529.  The external probe has a persistent passing CLI suite.

## Work and acceptance discipline

At most three Opus/low laps, with a four-hour between-laps duration cap.  Commit a compiling scaffold before hard proof work, then coherent green checkpoints.  Only this module, its root import, the research note's formalization-status paragraph, and `HANDOFF-2026-09-27-negative-shadow.md` are task files.  The attended architect may write disjoint new research files concurrently; do not edit them.  Do not launch further tasks or optimize unrelated proofs.

Build the module and root.  Retain an audit of the headline declarations' transitive dependencies; check that none still depends on sorryAx before claiming completion.  Completion must retain every named headline above.  Do not use a helper-file relocation to satisfy a file-only gate.  Report what the mathematics now says and the precise next leaf if unfinished, not a sorry tally.

Host preflight: Lean 4.33.1 shared store exists; `relake plan` recognizes the warm independent dependencies and proposes optional sharing.  No cache download is needed.  No active Collatz treadmill was reported at preparation time.
