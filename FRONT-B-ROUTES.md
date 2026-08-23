# Front B route map: how a cycle proof could actually close 🔒

> 🧾 **The board is also Lean.**  `CollatzMoonshot/FrontB/Threads.lean` states every thread
> below as a `Prop`, so "killed" is a theorem and "open" is an uninhabited statement.  Prose
> and Lean are kept in sync deliberately; if they drift, **the Lean file wins**.

*Companion to `APPROACHES.md`, which ranks the three lanes for the conjecture as a whole.
This file is only about **Front B**, the nonexistence of a nontrivial cycle, and its job is
to say which ideas are structurally capable of finishing and which are not.*

## Notation

A cycle has `a` odd steps, `b` even steps, minimum element `N`, and

* `D := 2^b − 3^a > 0`, an **odd** integer;
* each cycle member is `M(v')/D` where `v'` ranges over the rotations of the cycle's parity
  word and `M` is a positive integer combination of monomials `2^i 3^j`.

From `CycleDiophantine.lean` (proved, axiom-clean):

```
3^a < 2^b ≤ (3 + 1/N)^a       equivalently      0 < b·log 2 − a·log 3 ≤ a/(3N)
```

and from the product identity `2^b = 3^a ∏(1 + 1/(3mᵢ))`, the size relation

```
D ≈ 3^a · a / (3 · m̄)          m̄ = harmonic mean of the cycle's odd elements
```

## 🚩 The filter: which direction does your tool bound `D`?

**Everything that says "2 and 3 are far apart" bounds `D` from BELOW.**  Baker linear forms,
effective irrationality measures for `log₂3`, S-unit lower bounds, `abc` applied to
`3^a + D = 2^b`, Stewart-type digit bounds - all of them say `D` cannot be too small.  By the
size relation a lower bound on `D` is an **upper** bound on `m̄`, which excludes only *short*
cycles.  It converts "verified up to `N`" into "no cycle shorter than about `√N`".  **It can
never finish**, because `log₂3` is irrational and therefore admits arbitrarily good rational
approximations: for large `a` the Diophantine constraint is slack by miles.

**Finishing requires an UPPER bound on `D`.**  Once `D` is bounded by a constant, `2^b − 3^a`
bounded means finitely many `(a,b)` **effectively**, by Baker - and every surviving pair dies
against the Eliahou length bound.  An upper bound on `D` is an *integrality* statement, not a
Diophantine one: `D` divides things, and divisibility is where the additive and multiplicative
structures actually collide.

**The transcendence is the closer, never the opener.**  This is confirmed by both known
theorems: Knight (2026) closes the high-cycle case with an upper bound (`D | 2^{k−2}`, `D` odd,
so `D = 1`) and needs no transcendence at all; Steiner (1977) closes the circuit case because
circuits make the exponent structure rigid enough for Baker to finish a *bounded* problem.

✅ **Resolved 2026-08-22**: the old `APPROACHES.md` claim that an effective S-unit or
abc-strength input finishes cycles entirely was an overclaim and has been removed.  Applying
abc to `3^a + D = 2^b` gives `D ≳ 2^{b/(1+ε)}`, a lower bound, hence only
`m̄ ≲ a·3^{εa}`, which excludes no large `a`.  `Assumed/ABC.lean` and
`length_bounded_of_abc_and_boundedDen` record the corrected scissors: abc closes only when an
independent upper bound on `D` supplies the other blade.

## Route 1 - The integrality lattice (bound `D` above by divisibility) 🔢

**The 2-vs-3 mechanism.**  `D` is odd, while the numerators `M(v')` are additive combinations
of the multiplicative monomials `2^i 3^j`.  Whether an odd number can divide all of them is a
question about how the 3-adic and 2-adic structures sit inside one additive span.

**The missing theorem.**  Integrality forces `D | M(v')` for *every* rotation, so
`D | G` where `G = gcd_{v'} M(v')`.  Bound the **odd part of `G`** by a constant and `D` is
bounded and Baker closes.  Knight's proof is the special case where a rotation *difference*
has numerator `2^{k−2}`, whose odd part is 1; his cancellation of the 3-parts needs two
rotations sharing a prefix of length `k−2`, which forces a Christoffel word, which is exactly
why he only reaches the extremal cycle.

**What we would see in their library.**  A structure theorem for the lattice spanned by the
rotations of a binary necklace evaluated at `(2,3)`.  Pure algebra and combinatorics on words;
no analysis anywhere.

**First step available to us.**  Compute `G` for random aperiodic words and see whether its odd
part is bounded, growing, or wild.  This is a **cheap numerical experiment that can refute the
route in an afternoon**, and it is a genuinely CDC-shaped target for a fan-out.
⚠️ Literature check first: Steiner / Simons-de Weger / Hercher have ground on the exponent
vector for decades and may have this, possibly with a known reason it fails.

## Route 2 - Compression to boundedly many circuits 🗜️

**The 2-vs-3 mechanism.**  The cycle equation is an S-unit equation over `S = {2,3}`:
`Σ 3^{a−1−i} 2^{E_i} = N·D`.  The subspace theorem (Evertse-Schlickewei-Schmidt) bounds the
number of nondegenerate solutions by a function of the **number of terms** and `|S|` alone -
not of the coefficients.  That is the deepest known statement of "additive relations among
multiplicatively independent quantities are rare."

**The missing theorem.**  The term count here is `a`, the cycle length, which is unbounded, so
the ESS bound is vacuous.  What is needed is a **compression**: show that an integral cycle
with many circuits reduces to one with boundedly many, or that the many-circuit case
degenerates.  Then Simons-de Weger's machinery finishes, since it already handles every
bounded circuit count.

**What we would see in their library.**  A theorem of the form "every integral cycle has at
most `C` circuits", proved by a rearrangement or extremal argument on parity words.

**Honest read.**  This is the most conservative route: every tool except the compression lemma
already exists, and the whole frontier of the literature is exactly the slow march up the
circuit count (68, then 91, ...).  A civilization that got there probably got there here.

## Route 3 - Classification, not rigidity, for the joint action 🌀

**The 2-vs-3 mechanism.**  Furstenberg's ×2×3 phenomenon: the joint action of two
multiplicatively independent maps is stiff, so invariant objects are forced to be trivial.

**The missing theorem.**  Current rigidity (Rudolph-Johnson, EKL) is about **positive-entropy
measures**, and a cycle is a finite orbit with entropy zero, so today's theorems say nothing.
What is needed is entropy-free rigidity for the Collatz skew product on `ℤ_2 × ℝ` - a
**classification of finite invariant sets**, which is an upper-bound-flavoured statement and
therefore *not* killed by the filter above.

**What we would see in their library.**  An entropy-free ×2×3 rigidity theorem, i.e. the hard
part of Furstenberg's conjecture.  The most beautiful and the least likely to be in reach; if
they had it, they would have proved a great deal more than Collatz.

## Where the odds sit

- Route 2 (compression) - most likely to be how it is actually done, ~55% conditional on the
  cycle front being resolvable at all.
- Route 1 (integrality lattice) - ~20%, and the only one with a same-day refutable experiment.
- Route 3 (classification) - ~10%, and it would be a much larger event than Collatz.
- Something none of these names - ~15%.

None of the three is in reach.  The value of this map is the **filter**: it tells us in advance
that any idea whose content is "2 and 3 are far apart" is structurally incapable of closing
Front B, no matter how strong the input.  That disqualifies most of what looks attractive,
including the `abc` line currently in `APPROACHES.md`.

---

# Ruled out on 2026-08-22 🔪

Three threads pulled, all with reproducible evidence in `experiments/`.  Two died, and
the third narrowed enough to change the ranking.

## Route 1 (integrality lattice) **collapses** - do not revisit

Rotating the parity word acts on numerators by `M ↦ M/2` (leading 0) or
`M ↦ (3M + D)/2` (leading 1).  Since `D` is odd, `2` is invertible mod `D`, so

> `M(σʲ v) ≡ M(v) · 3^{xⱼ} · 2^{−j}  (mod D)`,  `xⱼ` = ones in the first `j` letters

**Every rotation is a unit multiple of every other, mod `D`.**  Hence `D | M(v')` for all
rotations is *equivalent* to `D | M(v)` for one, and `gcd` over rotations carries no
information the single condition did not.  Verified for every word tested
(`experiments/probe.py`, `unit_multiple_law=True` throughout).

The same law explains why Knight needs a *difference*: differences of unit multiples are
not unit multiples.  Generalising it needs two rotations agreeing outside a bounded window,
which by Morse-Hedlund forces low factor complexity, i.e. a Sturmian/Christoffel word.  The
extremal case is the only case the trick reaches.  `experiments/oddpart.py` measures the odd
part of the gcd of rotation-differences: tiny (1 to 893) for random words, but that is
genericity of large integers, not structure - it cannot see the vanishingly rare words that
would be cycles.

## The counting route: the Diophantine half is already DONE, and it still cannot close

Every word is the parity word of exactly one rational cycle; it is an *integer* cycle iff
`D | W(v)`.  Naive count: `C(k,x) / (k·D)` cycles per `(k,x)`.

- The bulk of that mass sits at `x/k ≈ 1/2`, where `D ≈ 2^k` and the predicted cycles have
  **bounded elements** - killed outright by the computational verification bound.
- Cycles with *large* elements live only in the band `k = ⌈x·log₂3⌉`, where the word entropy
  is `H(log 2 / log 3) = 0.9500`, so the expected count is `≈ 2^{−0.05k}`.  Measured
  convergence to that exponent in `experiments/margin.py`.
- **The margin is exponential while Baker's loss on `D` is only quasi-polynomial**
  (`D > 2^k·exp(−C log²k)`).  The entropy budget overtakes it around `k ≈ 10⁴`, and Eliahou
  already forces `k > 1.7 × 10⁷`.  So the Diophantine input needed here **already exists,
  with room to spare** - this is the one place a lower bound on `D` is used in the *right*
  direction, which corrects the filter above: the filter kills Diophantine input used
  through the SIZE relation, not through counting.

**Why it still cannot finish**: a counting argument proves "few", and we need "none".  With
a main term below 1, the error term would have to be below 1 as well - full cancellation in
a sum of `2^{0.95k}` terms, far past square-root cancellation.  Heuristics of this shape
explain the absence of cycles; they cannot witness it.

## Control that validates the machinery 🧪

Run the same count with `D < 0` (the `3n+1` map on negative integers) and the `−17` cycle
appears at exactly `(k,x) = (11,7)`, contributing precisely its 11 rotations
(`experiments/hist.py`).  The method sees cycles when cycles exist.  The sign asymmetry is
the 3x−1 barrier showing up in the counting picture, and any proof must consume it.

## Consequence for the ranking

**Route 2 (compression to boundedly many circuits) is now the only survivor, and for a
sharp reason**: the subspace theorem and Baker produce **exact finiteness**, not estimates,
so they can output "zero" after a finite check.  Size arguments point the wrong way,
counting arguments cannot reach zero, and integrality identities reach only Christoffel
words.  Revised: Route 2 ~70%, exact-identity families (Knight-style, new word classes)
~15%, Route 3 ~10%, unnamed ~5% - all conditional on the front being resolvable at all.

## Fourth thread: "near-integer cycle" has no usable proxy 🧪

Route 2 assumes integer cycles want **few circuits** (maximal runs of odd steps), which is
why bounding the circuit count would finish.  Testable: do the necklaces closest to being
integer cycles have low circuit count?

Measured with `gcd(W, D)` as the nearness proxy, over every necklace for `x = 10, 12, 15`
(`experiments/circuits3.py`).  Result: **inconclusive, and the proxy is the reason.**

- Deduplication matters twice over.  `gcd` and circuit count are both rotation-invariant, so
  a word-level tally inflates every sample by a factor of `k`; an uncorrected run showed a
  clean "near-misses have MORE circuits" signal that was one necklace counted 24 times.
- After deduplication `x = 10` and `x = 12` show no signal (`|z| ≤ 1`).  `x = 15` shows
  `z = −11` for the top 50, but that group is the `gcd = 13` tier: `D = 13 × 186793`, so the
  gcd takes only four values and "top 50" means "divisible by 13".  The signal is
  small-prime divisibility structure correlating with word combinatorics, not proximity to
  cyclehood.
- **Divisibility is not a metric.**  A necklace with `gcd = D/13` is not "close" to one with
  `gcd = D` in any sense that respects the dynamics.  So numerical exploration cannot guide
  the compression lemma, which is presumably why the literature proceeds by proof (Steiner,
  Knight) rather than by experiment.

Consequence: Route 2's missing lemma has to be attacked directly, and **we should not expect
data to suggest its statement.**  That lowers the value of further numerics on this front.

## The negative side is a falsification test worth building 🚨

The `3n+1` map on negative integers has three nontrivial cycles (`−1`, `−5`, `−17`), and the
whole formalism carries over with `D = 2^k − 3^x < 0`.  **Any argument that would also rule
those out is wrong.**  That makes the negative side a unit test for candidate proofs, and it
operationalises the 3x−1 barrier from `APPROACHES.md`: every lemma we prove should be run
against `(k,x) = (1,1)`, `(3,2)` and `(11,7)` before we believe it.
