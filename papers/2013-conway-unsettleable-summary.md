# Conway, "On Unsettleable Arithmetical Problems" (2013)

## Provenance
- **Author**: John H. Conway
- **Venue**: *The American Mathematical Monthly* **120** (3), March 2013, pp. 192-198.
  DOI [10.4169/amer.math.monthly.120.03.192](http://dx.doi.org/10.4169/amer.math.monthly.120.03.192).
  Reprinted in *The Best Writing on Mathematics 2014* (Princeton UP).
- **Local PDF**: `papers/2013-conway-unsettleable.pdf` (gitignored - copyrighted; this repo is
  eventually-public, so only this summary is committed).  Source: raganwald.com mirror of the JSTOR scan.
- **Why it's here**: this is the actual source of "Conway thinks Collatz is outside normal
  axiom space."  The folklore version overstates it; the paper is more careful and more useful.

## What is PROVED

An explicit **24-fraction Collatzian game** (later reduced to **7 fractions by John Rickard**)
has a starting number whose orbit never reaches 1, where that non-termination **is not
provable** from a given consistent axiom system.  Mechanism: Conway 1972 shows any computable
function is simulated by a fraction game (FRACTRAN); bolt on a machine that searches for a
proof of `0 = 1` from the `n`-th axiom system, and Gödel does the rest.

> "In general, if a Collatzian game does not stop, then there is no proof of this."

**"Unsettleable" means unprovable and unrefutable from set theory** - his words: "I shall use
the term unsettleable because for more than a century the ultimate basis for proof has been
set theory."  So this is ZFC-level, not merely PA-level.

## What is only SPECULATED

- On `3n+1` itself: *"There is a slight chance that this problem itself is unsettleable - some
  very similar problems certainly are."*  **That is the whole claim.**  No argument that
  Collatz specifically is unsettleable is given or attempted.
- His candidate for the simplest unsettleable statement is **not Collatz**.  It is the
  **amusical permutation** `μ : 2k ↦ 3k, 4k+1 ↦ 3k+1, 4k−1 ↦ 3k−1`, and the assertion that
  **8 lies on an infinite cycle**.  (Name: twelve steps of `μ` multiply by ≈2, like twelve
  piano semitones to an octave; the ratio `3¹²/2¹⁹` is the Pythagorean comma.)

## Conway's own hedge on 3n+1 (Appendix 1) - the part the folklore drops

> "The `3n+1` game presents special features, in that the probabilistic arguments suggest that
> large numbers **decrease**, rather than increase as in the amusical permutation.  If this
> were provable, the conjecture would be settled by being provable.  There is some slight hope
> that this might happen."

He names the **Hardy-Littlewood circle method** as the hope (citing Vinogradov), noting the
`P + E` shape where `P` is exactly a probabilistic main term over `p`-adic densities.  Then:
*"It is not entirely inconceivable that such a method might one day prove the Collatz `3n+1`
Conjecture... However, I don't really believe it."*

So Conway is **not** claiming Collatz is beyond axioms.  He is claiming (a) nearby problems
provably are, (b) Collatz *might* be, (c) unlike the amusical permutation, Collatz has a
downward drift that leaves a real if slim route to a proof.

## "Probvious" 🎯

Conway coins **probvious** = "probabilistically obvious" for statements like "the cycle of 8
is infinite", verified numerically past `10^400` (and past `10^5000` after the text was
written).  This is precisely the epistemic status of the entropy-margin count in
`FRONT-B-ROUTES.md`, and it is worth borrowing the word.

⚠️ His own footnote undercuts it honestly: at `μ^1981(82) ≈ 5.5·10^63` the orbit **decreases**
by a factor of more than `2^16` where an increase of nearly `2^19` was expected, which
"casts some doubt on the probabilistic arguments in the text."

## Relevance to Front B

Conway's unsettleability targets **non-termination**, a `Π⁰₂` property with no finite
certificate.  **"No nontrivial cycle" is `Π⁰₁`** - a counterexample is a checkable pair
`(n, m)`.  A false `Π⁰₁` sentence is refutable in any `Σ₁`-complete theory, so *unsettleable
and false* is impossible for our front: if Front B were unsettleable, it would be **true**.

That does not make it provable, and it is not evidence for or against.  But it does mean
Conway's paper is pessimism about the **divergence** front, not this one.  Recorded in
`CollatzMoonshot/FrontB/Threads.lean`, thread 21.
