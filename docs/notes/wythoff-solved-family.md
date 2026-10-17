# The Wythoff family through `U`: a solved line, a sporadic cubic, and a golden trap

**Abstract.**  For a real `α > 1` with `β = α/(α − 1)`, the *Wythoff map*
`W_α(2k) = ⌊kα⌋`, `W_α(2k − 1) = ⌈kβ⌉ − 1` merges the two Beatty sequences of `α` and `β`, so by
Rayleigh's theorem it is a permutation of `ℤ` preserving `ℕ⁺` ([`wy`][wy], [`wy_bijective`][wyb]).
At `α = 3` it is Conway's amusical permutation `U`.  We prove in Lean that an infinite
two-parameter line of these maps is *solved*: `{1}` is the only finite orbit, every other orbit
runs to `∞` in both time directions, the orbit minima are characterized by a finite parity test,
and their number up to `X` satisfies an exact identity.  The line contains the even integers
`α = 2r` and the quadratic `α = 2r + 2√(r² − r)`, and continues through cubic, quartic and higher
members.  Off the line we prove a sporadic cubic member (Theorem Y), the golden member
`α = 3 + √5` with infinitely many 3-cycles and a trap cut out by `{kφ} < ½`, a family of even traps
(Theorem K), and, for rational `α = p/q` with `p` even, an exact Markov law for the parity
itinerary.  None of it reaches `U` (§7).

All results are linked at commit [`daf38cf`][commit].  Every theorem below checks with
`#print axioms` against the standard three (`propext`, `Classical.choice`, `Quot.sound`),
verified 2026-10-16.  Densities are stated conditionally on Weyl's equidistribution theorem,
which Mathlib does not have; it enters only as the named hypotheses
[`WeylEquidistribution`][weyl1], [`WeylEquidistributionMulti`][weyld] and (for Theorem F)
[`SflOddDensityHalf`][sfl].  Everything else is unconditional.

## 1. The engine: orbit classification from a monotone potential (Lemma P)

Let `σ` be a permutation of `ℤ` preserving `ℕ⁺`, `S` a set, `Φ` a `σ`-invariant set, and `T ≥ 1`.
Suppose positive points off `S ∪ Φ` step down, and a positive `s ∈ S ∖ Φ` first returns to `S`
within `T` steps, to a larger value ([`Hyp`][hyp]).  Then the finite orbits through `ℕ⁺` are
exactly those in `Φ` when `Φ` consists of fixed points ([`permOrbit_finite_iff`][pfi]); every
other orbit tends to `∞` both ways ([`tendsto_pow_neg`][tpn]); its minimum is its unique point of
`S` whose `T` predecessors lie off `S` ([`isOrbitMin_iff`][omi]); and
`#{minima ≤ X} + #{s ∈ S ∖ Φ, s ≤ X : R(s) ≤ X} = #(Φ ∩ [1, X]) + #((S ∖ Φ) ∩ [1, X])` with `R`
the first-return map ([`minCount_add_returnCount`][mca]).  For `W_α` with `α > 2`, `S` is the
evens: they step up, and the odd points above `1` step down once `α ≥ 3`.  What remains is to
bound the runs of odd points after an even one and show the return lands higher.

## 2. Theorem G: the solved line

Fix integers `m ≥ 0` and `r ≥ 2`.  Let `x ∈ (½, ¾)` be the root of `x^{m+1} − 2rx + r`
([`gRoot_spec`][grs]), `β = 2x` and `α = 2x/(2x − 1)`.

* **Exact composite** ([`wy_iterate_eq_of_odd_run`][gid]).  If `n` is even and
  `W(n), …, Wᵐ(n)` are odd, then `W^{m+1}(n) = r·n`, for every `n ∈ ℤ`.  Since `r·n` is even, at
  most `m` odd points follow an even one.
* **Classification** ([`permOrbit_gPerm_finite_iff`][gfi], [`isOrbitMin_gPerm_iff`][gmi]).
  `{1}` is the only finite orbit in `ℕ⁺`; every other orbit tends to `∞` both ways; `x > 1` is an
  orbit minimum iff it is even and its `m + 1` predecessors are odd.
* **Count** ([`minCount_gPerm_add`][gca]).  `#{minima ≤ X} + #{even s ≤ X : R(s) ≤ X} = 1 + ⌊X/2⌋`,
  and since `R(s) ≥ r·s` there are at least `1 + ⌊X/2⌋ − ⌊X/2r⌋` orbits with minimum `≤ X`.
* **Density** ([`tendsto_minCount_gPerm`][gde], given Weyl and `deg x = m + 1`):
  `(α − 2)/(2αβᵐ)`.
* **Mirror** ([`wy_iterate_eq_of_even_run_mirror`][gmir], [`permOrbit_gmPerm_infinite`][gmi2]).
  `W_β` has `W^{m+1}(n) = r(n + 1) − 1` on the mirrored word and no finite orbit in `ℕ⁺`.

The proof of the composite is a sandwich.  Write the even step as `v ↦ ⌊(α/2)v⌋` and the odd step
as `v ↦ ⌈x(v + 1)⌉ − 1`.  Each floor or ceiling error is at most `1` before scaling by `x < 1`, so
after the word the real argument lies strictly between `rn` and `rn + Σ_{l ≤ m} xˡ`, and
`Σ_{l ≤ m} xˡ < 1` is exactly `(r − 1)(2x − 1) > 0`.  No irrationality is used.  Row `m = 0` is
`α = 2r` ([`alphaG_zero`][g0]), row `m = 1` is `α = 2r + 2√(r² − r)` ([`alphaG_one`][g1]), proved
separately with its own exact count `1 + A(X) − B(X)` in `WythoffQuadratic`
([`wq_wq_of_odd`][fD], [`permOrbit_wqPerm_infinite`][fi], [`minCount_add_countB`][fc],
[`tendsto_minCount`][fd]).  Row `(2, 2)` is the cubic `α³ − 16α² + 32α − 16 = 0`, `α ≈ 13.7587`,
with minima density `≈ 0.36746`.

## 3. Theorem Y: a cubic member solved by a recurrence

Let `x ≈ 0.52596` be the real root of `x³ + x² + 3x − 2`, `β = 2x`, `α = 2x/(2x − 1) ≈ 20.2623`.
No composite slope `(α/2)xʲ` is an integer, so §2 does not apply.  Instead, if `n` is even and
`W(n), W²(n), W³(n)` are odd, then `W⁴(n) = 4n + W³(n) − W²(n)` for every `n ∈ ℤ`
([`wy_iterate_four_eq`][yid]), which is even.  The proof writes `W³` and `W⁴` exactly in terms of
the fractional parts left by each step, and bounds two affine functions of two of them over
polygons by explicit linear certificates ([`yPhase4_of_neg_one`][ypoly] is the tight one: its
bound fails at the corner the strict inequality excludes).  With Lemma P (`T = 4`), `{1}` is the
only finite orbit, the minima are the evens with four odd predecessors ([`isOrbitMin_yPerm_iff`][ymi]),
and, given two-dimensional Weyl (`deg x = 3` is proved, [`linearIndependent_yRoot`][yli]), the
minima have density `3/10 + x/8 + x²/10 ≈ 0.39341` ([`tendsto_minCount_yPerm`][yde]).

## 4. Even traps: Theorem K

Suppose `x = α/2` satisfies `x² = bx + c` with `b, c ∈ ℤ`.  Then for even `n = 2k` with `W(n)`
even, `W²(n) = b·W(n) + c·n + ⌊(b − x){kα}⌋` for any real `α` ([`wy_wy_of_even_even`][Ap]).  When
the conjugate `b − x` lies in `(0, 1)`, that is `1 ≤ −c ≤ b − 2`, the last term vanishes, so
`{n > 0 even : W(n) even}` is a trap ([`coneSet_trap`][trap]) and there are infinitely many
infinite orbits ([`wkPerm_infinitelyManyInfiniteOrbits`][kinf]), with trap entry points of
density `(1 − 2/α)/4` given Weyl ([`tendsto_coneEntryCount`][kde]).  When `b − x ∈ (−1, 0)`, as
for `α = 1 + √5`, the term is `−1` and for `n ≠ 0` an even-even step is always followed by an odd one
([`wy_wy_of_even_even_anticone`][anti]).  The quadratic row of Theorem G is the case
`(b, c) = (2r, −r)`.

## 5. The golden member `α = 3 + √5`

Here `x = β/2 = 1/φ` and `W(2k)` is even iff `{kφ} < ½`.  If `n` is even and `W(n)` is odd then
`W³(n) = n` ([`wy_gold_iterate_three`][g3]), so there are infinitely many 3-cycles.  The set
`{2k : k > 0, {kφ} < ½}` is Theorem K's trap for `(b, c) = (3, −1)`, and its image is exactly
`{2k : k > 0, {kφ} < 1/(2φ²)}` ([`mem_image_coneSet_gold_iff`][gimg]).  Every orbit through
`ℕ⁺` is `{1}`, a 3-cycle, or infinite, running to `∞` both ways through the trap
([`goldPerm_trichotomy`][gtri]).  The minima of the infinite orbits are exactly the `2k` with
`1/(2φ²) ≤ {kφ} < ½` ([`isOrbitMin_and_infinite_iff`][ginf]); given Weyl, they have density
`1/(4φ)` ([`tendsto_goldInfMinCount`][gid2]), which equals Theorem K's entry density, and the
3-cycle minima have density `¼` ([`tendsto_goldCycleMinCount`][gcyc]).

## 6. Rational members: the parity itinerary is a Markov chain

For `α = p/q` the map is residue-class-wise affine, with two sides `±` according to the limit
taken.  When `p` is even, each piece's image is one residue class mod `p` of fixed parity, and
the parities of `x, W(x), W²(x), …` and of `W⁻¹(x), W⁻²(x), …` form exact two-state Markov
chains: over any whole number of periods, each cylinder of forward and backward parity words
is counted by the product of the chain's transition probabilities ([`cylCount_eq`][Mc]).  The
forward and backward words are independent given the parity of `x` ([`cylCount_condIndep`][Mi]),
but not unconditionally (an explicit witness at `10/3`, [`tenThirds_dependent`][M103]); for odd
`p` the law is i.i.d. ([`cylCount_eq_odd`][Modd]).  The transition probabilities come from a
parity count over the pieces ([`card_even_image_even`][L1]), and a parity class is absorbing
iff the side is `+` and `q = 1` or `p − q = 1` ([`absorbing_iff`][T]).

## 7. What this does and does not say

Each solved member above rests on a step that consumes no fresh 2-adic digit: an exact composite
`r·n`, a linear recurrence, or a conjugate that pins a floor.  `U`'s slopes `3/2` and `3/4`
have negative 2-adic valuation in every composite, and the analysis behind research note §60
finds no member of `2 < α < 3 + √5` other than `α = 4` solvable this way (85%, not proved), so
these mechanisms are what `U` lacks.  The results map the family around `U`; they do not
decide whether `U`'s orbit of `8` is infinite.

[commit]: https://github.com/gotrevor/collatz-moonshot/tree/daf38cf
[wy]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGeneral.lean#L30
[wyb]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGeneral.lean#L79
[weyl1]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGeneral.lean#L211
[weyld]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGeneral.lean#L224
[sfl]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffQuadratic.lean#L1280
[hyp]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/MonotonePotential.lean#L48
[pfi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/MonotonePotential.lean#L353
[tpn]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/MonotonePotential.lean#L369
[omi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/MonotonePotential.lean#L396
[mca]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/MonotonePotential.lean#L513
[grs]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L76
[g0]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L223
[g1]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L228
[gid]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L325
[gmir]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L416
[gfi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L1341
[gmi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L1358
[gca]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L1370
[gde]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L1492
[gmi2]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffLine.lean#L1709
[fD]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffQuadratic.lean#L444
[fi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffQuadratic.lean#L935
[fc]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffQuadratic.lean#L1082
[fd]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffQuadratic.lean#L1428
[yli]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffSporadic.lean#L181
[ypoly]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffSporadic.lean#L295
[yid]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffSporadic.lean#L440
[ymi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffSporadic.lean#L691
[yde]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffSporadic.lean#L1723
[Ap]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffCone.lean#L49
[trap]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffCone.lean#L251
[kinf]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffCone.lean#L471
[kde]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffCone.lean#L594
[anti]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffCone.lean#L687
[g3]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGolden.lean#L193
[gimg]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGolden.lean#L338
[gtri]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGolden.lean#L584
[ginf]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGolden.lean#L627
[gcyc]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGolden.lean#L865
[gid2]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffGolden.lean#L885
[L1]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffRational.lean#L421
[T]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffRational.lean#L593
[Mc]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffRationalMarkov.lean#L1178
[Mi]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffRationalMarkov.lean#L1208
[M103]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffRationalMarkov.lean#L1230
[Modd]: https://github.com/gotrevor/collatz-moonshot/blob/daf38cf/CollatzMoonshot/WythoffRationalMarkov.lean#L1250
