# Barriers and a phase picture for Collatz's permutation

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

**Abstract.**  Klamkin's problem (a) asks whether Collatz's permutation `U(2n) = 3n`,
`U(4n+1) = 3n+1`, `U(4n+3) = 3n+2` has only finitely many orbits on `ℕ`.  We make precise, and prove
in Lean, the folklore that arguments reading `U` only partially cannot prove that it has infinitely
many infinite orbits.  A *method class* is the set of permutations a method cannot tell from `U`,
and a *barrier* is a member of that set with the opposite answer.  The main result is an exact
criterion: every permutation that agrees with `U` off a set `S` has infinitely many infinite orbits
if and only if infinitely many whole tails of `U`-orbits avoid `S`.  A finite-depth corollary
follows: agreeing with `U` to any finite depth at each point, outside a sparse set, does not force a
second infinite orbit.  On the other side, a trap theorem gives infinitely many infinite orbits for
a permutation one class transposition away from `U`, at least `X/3 − O(1)` of them meeting `[0, X)`.
We prove that `U` itself has no trap at any modulus, and we record a numerical census of `U`'s
neighbours with a conjectured phase boundary.  The same schema gives a short barrier for the Collatz
map: arguments that cannot see which of `(3x ± 1)/2` is taken cannot prove the Collatz conjecture.

All results are linked at commit [`1381730`][commit].  Every proved statement below checks with
`#print axioms` against the standard three (`propext`, `Classical.choice`, `Quot.sound`) or a subset
of them.  `no_early_ray_join` in §4 also takes a literature hypothesis, which it receives as an
argument; the hypothesis is not an axiom.

## The problem, and what the barriers are about

`U` ([`amusical`][amusical]) is a bijection of `ℤ` that preserves `ℕ`.  Klamkin (SIAM Review 5
(1963) 275-276) asked whether it has only finitely many orbits on `ℕ`
([`AmusicalInfinitelyManyOrbits`][kl] is the negation).  The problem is open.  Its history, the
known cycles, and a proved upper bound on the density of orbit minima are in the companion note
[`amusical-orbit-minima.md`](amusical-orbit-minima.md).

Write **(a)** for "infinitely many orbits" and **(a∞)** for "infinitely many *infinite* orbits".
(a) also holds if `U` has infinitely many cycles.  Every barrier below keeps all of `U`'s cycles and
changes only how the infinite orbits are joined.  So the barriers block proofs of (a∞), and a proof
of (a) through infinitely many cycles is not touched by them.  Most of the barriers are
unconditional: the barrier permutations fuse whatever infinite orbits `U` has.  If `U` has none,
the barrier is vacuous but still true.

## 1. The schema

Fix a space of maps containing `U` and a target property `A`.  A *method class* is an equivalence
relation `~` on the space, standing for the information a method uses.  A hypothesis `P` with `P(U)`
is *`~`-relative* if `P(σ)` holds for every `σ ~ U`.  A *barrier* for `~` is some `τ ~ U` with
`¬A(τ)`.  If a barrier exists, no `~`-relative hypothesis implies `A`: it would hold at `τ`.  The
logic is one line, and the content is in the constructions of `τ`.

This is the shape of Selberg's parity problem in sieve theory.  There, a weight agrees with the
primes on everything the sieve axioms see but is supported on the wrong parity.  We cite it as a
model only.

## 2. What an argument must read: the tail threshold (proved)

**Theorem TT.**  For every `S ⊆ ℤ` the following are equivalent:

1. every permutation `τ` of `ℕ` with `τ(n) = U(n)` for all `n ∉ S` has infinitely many infinite
   orbits;
2. infinitely many infinite orbits of `U` contain a forward tail `{U^j y : j ≥ 0}` (`y ≥ 0`) that
   misses `S`, or infinitely many contain a backward tail `{U^{−j} y : j ≥ 1}` that misses `S`

([`tail_threshold`][tt]).

*Proof idea.*  (2 ⇒ 1): a tail that misses `S` is also a tail of `τ`, and disjoint rays cannot
share an orbit.  (1 ⇒ 2): if (2) fails, all but finitely many infinite orbits meet `S` at
arbitrarily late and arbitrarily early times.  Rewire `U` only at points of `S`, at stage `k` at
cut points above a height `Y_k`, and splice every such chain into one bi-infinite chain.  The
result has finitely many infinite orbits, contradicting 1.

**Reading.**  Condition 2 already implies (a∞) for `U`, since distinct orbits with `S`-free tails
are distinct infinite orbits.  So an argument that consults `U` only through its arrows out of
`ℕ ∖ S` proves (a∞) exactly when infinitely many whole tails avoid `S`.  The data it uses must then
contain a witness of (a∞).

**Theorem T1★ (odd rewiring).**  Take `S` to be the odd numbers.  For every `F → ∞` there is a
permutation `τ` of `ℕ` with `τ(2m) = 3m` for all `m`, `τ = U` on every finite orbit of `U`, at most
`F(N)` points `n < N` with `τ(n) ≠ U(n)`, and all infinite orbits of `U` lying on one `τ`-orbit
([`exists_oddRewire`][oddrewire]).  Here condition 2 fails: forward runs through even numbers have
length `v₂(x)`, and `U⁻¹` decreases multiples of 3 and sends everything else to an odd number.  So
any proof of (a∞) must use `U`'s odd branch exactly, along entire tails.

## 3. Finite-depth fusion (proved)

Say `τ` and `U` *disagree at depth `d` at `n`* if `τ^j(n) ≠ U^j(n)` for some `|j| ≤ d`
([`DisagreeAtDepth`][disagree]).  Write `D*(X) = max_{n<X} D(n)`.

**Theorem M1.**  Let `D, G : ℕ → ℕ` with `G(X)/(D*(X) + 1) → ∞`.  There is a permutation `τ` of `ℕ`
with `τ(2m) = 3m`, `τ = U` on every finite orbit of `U`, and all infinite orbits of `U` on one
`τ`-orbit, such that for all large `X` at most `G(X)` points `n < X` have `τ` and `U` disagreeing
at depth `D(n)` at `n` ([`exists_depthFusion`][m1]).

*Proof idea.*  Take T1★ with a change budget `F` tuned to `G` and `D`.  A disagreement at depth `d`
at `n` needs a change of `τ` at a point of `U`'s own segment `U^i(n)`, `|i| ≤ d`, in either time
direction.  Each change lies on at most `2D*(X) + 1` such segments.

Instances of the Lean statement:

* `D` bounded: any `G → ∞` works.
* `D(n) ≈ C log n`: the exceptional set can be `O((log X)^{1+ε})`.  So every density statement
  about the first `C log n` steps from `n` holds equally for `τ`.  This is roughly the depth that
  the residue of `n` modulo `2^k 3^k`, with `2^k 3^k ≤ n`, can control.
* `D(n) = ⌊n^{1−ε}⌋`: the exceptional set can have density 0.

So no property of `U` that reads each point to a finite depth, up to a sparse set of exceptions,
implies a second infinite orbit.  Theorem TT is the infinite-depth form: infinitely many whole
tails are what must be read.  We do not know how far the hypothesis `G/D* → ∞` can be weakened.
The natural obstruction: if `U` had finitely many orbits, some orbit would return to linear size
at arbitrarily late times ([`exists_linearlyRecurrent_of_finitelyManyOrbits`][linrec]), and a
single cut on such an orbit can spoil the depth-`D` agreement of many points below `X`.

## 4. Further barriers and no-go results in this repository (proved unless marked)

* **Density-0 rewiring.**  A permutation `σ` of `ℕ` with `σ(n), σ⁻¹(n) ≤ 2n + 1` agrees, off a
  set of density 0 and on every finite orbit, with a permutation in which all infinite orbits of
  `σ` form one orbit ([`rewire_single_orbit`][rewire]).  `U` satisfies the step bound.  So
  densities, window counts and crossing counts do not determine (a∞).
* **Bounded-ratio rewiring of `U`.**  Some `τ` keeps `U`'s finite orbits and has a single infinite
  orbit through all of `U`'s.  For some `C` it differs from `U` at no more than `C(log₂ N + 1)²`
  points below `N`, and it satisfies `τ(n) ≤ 3U(n) + 3` and `U(n) ≤ 3τ(n) + 3`
  ([`exists_boundedRatio_rewire`][ratio]).
* **Sparse survivors.**  Let `f` be a permutation of `ℕ` with finitely many periodic points, and
  let `F, G → ∞`.  There is a `π` that keeps `f`'s cycles and merges all infinite orbits into one,
  such that for large `X`: `π` (or `π⁻¹`) differs from `f` (or `f⁻¹`) at no more than `F(X)` points
  below `X`, and at most `G(X)` points below `X` are forward survivors, meaning `π^t(m) ≥ m` for all
  `t` ([`exists_reglue_sparseFS`][pi]).  For `U` the changes can avoid the even numbers, so that
  `π(2m) = 3m` ([`exists_reglue_sparseFS_amusical`][piU]).  This version **assumes** that `U` has
  finitely many periodic points.  That is open, though believed.
* **Finite changes are invisible.**  Composing a permutation of `ℕ` with finitely many
  transpositions does not change whether it has infinitely many orbits
  ([`infinite_permOrbits_mul_swaps_iff`][swaps]).  This is standard.  It explains why every barrier
  above changes infinitely many points.
* **No invariant mean.**  No finitely additive probability mean on `ℤ` is invariant under both
  `n ↦ n + 1` and `U` ([`no_translation_amusical_invariant_mean`][nomean]).  Translation forces the
  evens to have mass `1/2` and the multiples of 3 to have mass `1/3`, but `U` maps one set onto the
  other.  This is not a barrier but a no-instance result: translation-compatible averaging has
  nothing to work with.
* **Ray joins.**  Given Ellison's bound as a hypothesis, `U^k(3^m)` is not a power of 2 for
  `1 ≤ k ≤ 2m − 2` ([`no_early_ray_join`][ray], hypothesis [`EllisonBound`][ellison]).  The two
  known joins are `U^9(27) = 32` and `U^37(81) = 512` ([`ray_join_three`][ray3],
  [`ray_join_four`][ray4]).  *Paper only, not formalized:* let `F_1` be the family of permutations
  obtained from `U` by swapping the targets of `4n + 1` and `4n + 3` for any chosen set of `n`
  ([`ampSwap`][ampswap]; bijectivity is [`ampSwap_bijective`][ampbij]).  For every `m ≥ 5`, some
  member of `F_1` maps `3^m` to a power of 2 within `log_{4/3}(3^m) − 8.4` steps.  So an argument
  that holds on all of `F_1` cannot exclude joins beyond `c*·m` steps, where
  `c* = log_{4/3} 3 ≈ 3.8188`.

## 5. The same schema for the Collatz map (proved)

Let `T_ε` send even `x` to `x/2`, and odd `x` to `(3x + 1)/2` when `ε(x)` holds and to `(3x − 1)/2`
otherwise ([`signCollatz`][signdef]).  With `ε ≡ true` this is the Collatz map, in the form
that takes `(3x + 1)/2` at odd `x`.

**Sign-blind gate.**  For every `K` there is a sign choice `ε` with `ε(x) = true` for all `x < K`
such that `T_ε` has an orbit tending to infinity ([`signBlind_gate`][gate]).  The choice is
`ε(y) = [y < K or y ≡ 3 (mod 4)]`.  From `4K + 3`, every iterate is odd and larger than the last.
Also, the all-minus member, which is the `3x − 1` map, has the cycle `5 → 7 → 10 → 5`
([`signCollatz_minus_cycle`][minus]).

So an argument that uses the Collatz map exactly below some height, and above it uses only that
each odd step is one of `(3x ± 1)/2`, cannot prove that every orbit converges.  The sign choice in
the barrier depends on `x mod 4`, so "blind" here means blind to a per-point choice.  The substance
is folklore (see Prior work); we state it because it puts the Collatz map under the same schema as
§§2-3.

## 6. The other side: traps, and a solvable neighbour of `U`

**Trap theorem.**  Let `σ` be a permutation of `ℤ` that maps a set `C` into itself.  Call the
points of `C ∖ σ(C)` *entry points*.  Distinct entry points lie on distinct orbits
([`permOrbit_injOn_entry`][inj]), and every orbit through an entry point is infinite
([`permOrbit_infinite_of_entry`][infent]).  Hence infinitely many nonnegative entry points give
infinitely many infinite orbits meeting `ℕ`
([`infinitelyManyInfiniteOrbits_of_trap`][trap]; the target is
[`InfinitelyManyInfiniteOrbits`][imio]).  When `C` and `σ(C)` are finite unions of residue classes,
it follows that at least `(d(C) − d(σC))·X − O(1)` infinite orbits meet `[0, X)`, where `d` is
natural density.  This density form follows from the two lemmas and is not stated separately in
Lean.

**`U` has no residue trap.**  If a union of residue classes modulo `M` is mapped into itself by
`U`, it is empty or all of `ℤ` ([`amusical_no_periodic_cone`][nocone]).  The underlying fact is that
the residue graph of `U` is strongly connected at every modulus.  Every forward orbit of an infinite
orbit is a trap with one entry point, so traps exist exactly when infinite orbits do.  What fails
for `U` is a checkable trap: one made of residue classes.

**Theorem V.**  Let `V = U ∘ τ`, where `τ` is the class transposition `2k ↔ 8k + 3`.  Equivalently,
`V` is `U` with the targets of `0 (mod 2)` and `3 (mod 8)` swapped:

    V(2k) = 6k + 2,   V(4k + 1) = 3k + 1,   V(8k + 3) = 3k,   V(8k + 7) = 6k + 5

([`amusicalV`][vdef]; `V = U` on `1 (mod 4)` and `7 (mod 8)` is
[`amusicalV_eq_amusical`][veq]).  The evens are a trap for `V`, since `V(2ℤ) = 2 + 6ℤ`.  Its entry
points are exactly the classes `0, 4 (mod 6)` ([`amusicalV_entry_iff`][ventry]).  So `V` has
infinitely many infinite orbits ([`amusicalV_infinitelyManyInfiniteOrbits`][vthm]).  With the
injectivity lemma, at least `X/3 − O(1)` of them meet `[0, X)`.

*Paper, checked numerically on `[0, 2·10^5)`:* the orbits of `V` on `ℕ` are `{1}` and exactly one
infinite orbit through each entry point, and each entry point is the strict minimum of its orbit.
So the orbit minima of `V` have density exactly `1/3`.  This is Klamkin's conclusion, in a
quantitative form, for a permutation one class transposition away from `U`.  It keeps the domain
and image partitions of `U` and three of the five refined branches listed below.

**A census of `U`'s pairings (numerical).**  Refine `U`'s domain to the classes `0 (mod 2)`,
`1, 3, 5, 7 (mod 8)` and its image to `0 (mod 3)`, `1, 2, 4, 5 (mod 6)`.  `U` pairs them in order,
for example `U(8k + 3) = 6k + 2`.  Each of the 120 pairings defines a bijection of `ℕ`, sending the
`j`-th element of a domain class to the `j`-th element of its paired image class.  `V` is one of
them.  We ran a residue-closure search (moduli up to 48) and counted orbit starts on `[0, 10^5)`.
A *start* is a point whose forward and backward orbits both pass `x·2^24` without dropping below
`x`.  The phase depends on one bit, the image of the even class:

| image of `0 (mod 2)` | members | residue structure | measured start density |
|---|---|---|---|
| `2` or `4 (mod 6)` | 48 | trap at modulus 2, loss `1/3` | `1/3` in all 48 |
| `1` or `5 (mod 6)` | 48 | 45 with no closed residue set; 3 split | `0.129`-`0.130` |
| `0 (mod 3)`, as in `U` | 24 | 23 with no closed residue set; 1 split | `0.049`-`0.050` |

"Split" means that the only closed residue sets have zero density loss, so they decompose the map
without trapping anything.  For the 48 even-image members, the lower bound `X/3 − O(1)` is proved
by the trap theorem; the rest of the table is measurement.  The odd-image members also sit one swap
from a solvable member, and they show no trap.  So being next to a solvable permutation does not by
itself help.

**Conjecture B (phase boundary).**  Consider class-wise order-preserving bijections of `ℕ`, that
is, maps `mj + r ↦ nj + s` between the classes of two residue partitions.  Split off finite-order
pieces and invariant residue pieces of zero loss.  Then residue data certify a positive density of
orbits exactly when no residue-transitive wild piece remains.  On a residue-transitive piece, the
orbit-minimum density is a positive constant with no residue-based lower bound.  `U` is
residue-transitive at every modulus (above), so under this conjecture it is on the wall.  The
evidence is the census above together with a wider search of small members, which found nothing
contradicting it.  The conjecture is stated loosely and needs refinement.  The repository contains a
residue-transitive permutation with provably infinitely many orbits, obtained from a
valuation-counting engine rather than a trap ([`infinitelyManyOrbits_of_pingPong`][pingpong]; the
transitivity of the specific member is checked by computer, not in Lean).  A precise form must
exclude such engines.  Finite order is the solvable extreme, where every orbit is finite; Kohl's
remark quoted under Prior work is the related fact that tame groups acting on `ℕ₀` are finite.

**Avoidance.**  Every infinite orbit of `U` visits `{0, 3, 5} (mod 8)` infinitely often going
forward ([`amusical_visits_zero_three_five`][avoid]).  Suppose an orbit avoided these classes from
some point on.  Then from that point it never lands on `4 (mod 8)`, the classes `1, 2, 6, 7 (mod 8)`
map to odd numbers, and odd steps do not increase `|n|`.  The forward orbit would then be bounded,
so periodic.  The method is the mod-8 transition-graph argument of Yolcu, Aaronson and Heule for the
Collatz map, moved to `U`.  It uses only residues, so it says where infinite orbits go, not whether
they exist.  It has no bearing on their open Conjectures 4.11-4.14, which concern the Collatz map.

## Cited hypotheses

* [`EllisonBound`][ellison]: `|2^x − 3^y| > 2^x e^{−x/10}` for positive `x, y` with `x` outside
  `{1, …, 11, 13, 14, 16, 19, 27}`.  It is transcribed from Ellison, Séminaire de Théorie des
  Nombres de Bordeaux 1970/71, exp. 12, Theorem 3, and enters only `no_early_ray_join`.  We did not
  re-check the transcription against the original for this note.
* The finiteness of `U`'s periodic points, assumed by
  [`exists_reglue_sparseFS_amusical`][piU], is not a literature result.  It is an open statement
  about `U` and appears as an explicit hypothesis.

## Prior work

* **The informal barrier is Conway's.**  Conway (Amer. Math. Monthly 120 (2013) 192-198) writes in
  §5 that "there is a very small positive probability that for some very large positive numbers M
  and N, µ^M(8) might just happen to be the same googol digit number as µ^{−N}(8)".  Appendix 1
  says that `U`'s behaviour "would not be established even if one proved that almost all large
  numbers tend to increase, since, for instance, the number obtained by applying µ a million times
  to 8 might just be the same as the number obtained by applying µ^{−1} rather more times to 8 or
  14".  His `µ` is `U`.  Theorems TT and M1 are theorem forms of this remark.
* **Tao** (arXiv:1909.03562, Remark 1.4) considers whether `Col_min(N) ≤ C_0` for almost all `N`.
  He says this "is likely to be almost as hard to settle as the full Collatz conjecture, and out of
  reach of the methods of this paper": one orbit that never drops below `C_0` should, heuristically,
  absorb a positive density of starting points.
* **Traps.**  The qualitative mechanism is used in the literature but, as far as we found, never
  stated as a counting lemma.  Simons (arXiv:2205.10582, §5.4) proves that his `P(2, 6, 5, 3)` has
  "an infinite number of divergent trajectories with minima 3, 9, 15, · · ·".  Those minima are
  exactly `C ∖ σC` for `C` = the non-multiples of 6.  He adds: "For extended generalizations the
  existence of divergent trajectories cannot be proved."  Kohl ("Graph theoretical criteria for the
  wildness of residue-class-wise affine permutations", preprint, 2007, Lemma 3.4) uses the same kind
  of hypothesis to conclude wildness rather than an orbit count: "a union of finitely many residue
  classes of Z which is a proper subset of its image and a proper superset of its preimage".  That
  is a trap for `σ⁻¹`, and Kohl notes that image and preimage may be interchanged.
* **Tame and finite order.**  Kohl (Math. Z. 264 (2010) 927-938, §6) writes: "If a tame group does
  not act faithfully on a respected partition, then the kernel of the action clearly does not act
  on N0.  Thus as the group CT(Z) acts on N0, its tame subgroups are finite."
* **Avoidance.**  Yolcu, Aaronson and Heule (arXiv:2105.14697), Proposition 4.7: "All nonconvergent
  C-trajectories contain some n ≡ 6 (mod 8)".  See also their Theorems 4.9-4.10.  The paper concerns
  the Collatz map only.
* **Sign choice.**  Guy, "John Isbell's Game of Beanstalk and John Conway's Game of Beans Don't
  Talk", Math. Mag. 59 (1986) 259-269.  In the game, players choose `3n ± 1` at odd `n`.  We know it
  only through Lagarias's annotated bibliography (2003, entry 79).  The `3x − 1` cycles are
  classical.

## What is not claimed

Nothing here proves or refutes (a) or (a∞) for `U`.  The barriers keep `U`'s cycles, so they say
nothing about a proof of (a) through infinitely many cycles.  The schema of §1 is a way of reading
the theorems.  Whether a particular published argument is relative to a given method class is a
judgement, not a theorem.  The following are not separate Lean theorems: the depth corollaries of
M1 (instances of it), the density form of the trap theorem, the `X/3` count for `V`, and the orbit
classification of `V` (paper, checked numerically).  The `F_1` ray-join ceiling `c*` is paper only.
The pairing census is numerical, and Conjecture B is a conjecture.

Prior-work search.  Opened: Conway 2013; Tao's 2019 paper (§1); Simons 2022; Kohl's
graph-criteria preprint and his 2010 Math. Z. paper, with his RCWA manual and thesis searched by
keyword; Yolcu-Aaronson-Heule; Lagarias's annotated bibliographies (2003, 2006) and 2021
overview; OEIS (no entry for the first terms of `V` or `V⁻¹`; the same search for `U`
returns A006368).  Not opened: Guy 1986 itself; Selberg and Bombieri on the parity problem; the
literature on cyclic approximation and one-orbit permutations in dynamics, where the gluing
construction behind TT may be folklore; work citing Yolcu-Aaronson-Heule; MathOverflow.  In what we
opened we did not find the following: the equivalence TT; M1; the density form of the trap
theorem; `V` as an example; or mod-8 avoidance for `U`.  The barrier idea itself is Conway's, and
the substance of the sign-blind gate is folklore.

## Building

```
git clone https://github.com/gotrevor/collatz-moonshot && cd collatz-moonshot
git checkout 1381730515e2169b01966b430fec0721f95a21b4
lake exe cache get && lake build CollatzMoonshot.AmusicalOddRewire \
  CollatzMoonshot.AmusicalDepthFusion CollatzMoonshot.AmusicalTrap \
  CollatzMoonshot.AmusicalAntiKohl CollatzMoonshot.AmusicalSeventh \
  CollatzMoonshot.AmusicalRewireRatio CollatzMoonshot.AmusicalReglue \
  CollatzMoonshot.AmusicalTailEvent CollatzMoonshot.AmusicalNoMean \
  CollatzMoonshot.AmusicalRayJoin CollatzMoonshot.AmusicalSwap CollatzMoonshot.AmusicalPingPong
```

[commit]: https://github.com/gotrevor/collatz-moonshot/tree/1381730
[amusical]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/Amusical.lean#L31
[kl]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/Amusical.lean#L174
[linrec]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/Amusical.lean#L275
[tt]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalOddRewire.lean#L82
[oddrewire]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalOddRewire.lean#L136
[disagree]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalDepthFusion.lean#L30
[m1]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalDepthFusion.lean#L129
[rewire]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalSeventh.lean#L122
[ratio]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalRewireRatio.lean#L40
[pi]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalReglue.lean#L69
[piU]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalReglue.lean#L87
[swaps]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTailEvent.lean#L51
[nomean]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalNoMean.lean#L55
[ellison]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalRayJoin.lean#L29
[ray3]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalRayJoin.lean#L35
[ray4]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalRayJoin.lean#L39
[ray]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalRayJoin.lean#L70
[ampswap]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalSwap.lean#L31
[ampbij]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalSwap.lean#L37
[imio]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L40
[inj]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L65
[infent]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L80
[trap]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L96
[vdef]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L109
[veq]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L139
[ventry]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L152
[vthm]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L170
[avoid]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L219
[signdef]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L259
[gate]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L265
[minus]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalTrap.lean#L292
[nocone]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalAntiKohl.lean#L176
[pingpong]: https://github.com/gotrevor/collatz-moonshot/blob/1381730/CollatzMoonshot/AmusicalPingPong.lean#L323
