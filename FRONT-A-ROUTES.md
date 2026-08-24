# Front A route map: how divergence could actually be excluded 🧭

> 🧾 **The board is also Lean.**  `CollatzMoonshot/FrontA/Threads.lean` states the
> principal interfaces below.  Proposed new mathematics is a `def`; proved wiring and
> falsification facts are theorems.

*Companion to `FRONT-B-ROUTES.md`.  Front B asks whether a finite cycle can exist.  Front A
asks whether a positive orbit can be unbounded.  The two problems consume different evidence
and should keep different proof interfaces.*

## The exact drift currency

For the unaccelerated map, let `a(n,k)` and `b(n,k)` be the odd and even steps in the first
`k` iterates.  Above a floor `N`, `Rigidity/Drift.lean` proves

```
T^k(n) · 2^b ≤ n · (3 + 1/N)^a.
```

Thus a block descends whenever its odd-step frequency is below

```
q(N) := log 2 / log(2 · (3 + 1/N)).
```

The information-free threshold is `q(1) = 1/3`; a divergent orbit supplies arbitrarily high
eventual floors, and `q(N) ↑ q* := log 2 / log 6 ≈ 0.38685`.  In the shortcut-map convention
this is the familiar odd-step threshold `log 2 / log 3 ≈ 0.63093`.

`exists_floor_of_diverges` proves something stronger than mere `limsup = ∞`: a divergent
Collatz orbit eventually stays above every fixed height.  A repeat would make the orbit
periodic, so divergence makes the orbit injective, and an injective sequence of naturals can
visit a finite low interval only finitely often.

## Three filters 🚧

### 1. Pure ℤ₂ dynamics is blind

The 2-adic Collatz map is conjugate to the full one-sided shift.  Its invariant measures are
therefore abundant, including measures with the wrong parity frequency.  The proved
`-1 ↔ -2` 2-adic cycle has odd mass `1/2`, above `q*`.  Any unconditioned assertion about all
`T2`-invariant measures is false.

The arithmetic input must appear either as support on the closure of an actual positive
orbit, as an empirical-limit condition, or through an explicit archimedean/carry coupling.

### 2. Many divergent integers do not contradict Tao 2019

Tao's theorem controls `orbitMin n`, not eventual behavior.  If a large backward tree enters
one fixed divergent seed `d`, then every member `m` of that tree has

```
orbitMin(m) ≤ d.
```

For every `f(m) → ∞`, all sufficiently large members are therefore **Tao-good**:
`orbitMin(m) < f(m)`.  Even positive logarithmic density of divergent starting values would
not contradict the theorem if they all fall into one small divergent core.

The Lean witness is `mem_taoGood_of_reachesValue`.  This kills **raw backward-density
amplification** as a route.

### 3. Front A must not silently prove Front B

`DescentAll` is equivalent to the full Collatz conjecture.  It is a valid target, but it is not
a divergence-only consumption form: the minimum of a hypothetical nontrivial cycle cannot
descend.

The correctly scoped condition is

```
∀ n, Diverges n → ∃ k, T^k(n) < n.
```

`noDivergent_of_descends_if_diverges` proves that this already kills divergence by strong
induction.  A finite-certificate version is **repeat or descend**: every start either has two
equal iterates or eventually falls below itself.  The repeat branch deliberately permits
bounded nontrivial cycles; `noDivergent_of_repeatOrDescend` shows the disjunction closes only
Front A.  The converse is finite pigeonhole, so `repeatOrDescend_iff_noDivergent` proves this
certificate target is exactly Front A, not an accidental strengthening.

## Route A1 - Orbit-limit parity rigidity 🏔️

**Current lead.**  Average a positive orbit in compact `ℤ₂`, obtain empirical limit measures,
and force their odd mass below `q*`.  Clopen parity transports the measure statement back to
finite odd-step frequencies, while the free-floor theorem converts those frequencies into
archimedean descent.

The current pin is `ParityRigidityW1'`:

```
every invariant probability supported on a positive orbit closure
has μ(odd) < q*.
```

### Strength audit

* **W1 is not Front-A-only.**  W1 says every such measure charges `{1,2,4}`.  The uniform
  invariant measure on a hypothetical positive nontrivial cycle would violate W1, so W1
  already implies `NoNontrivialCycle`.  It does not implement the approach map's promised
  division in which rigidity permits atomic measures and arithmetic classifies them.
* **W1' has the right strength.**  Every positive cycle, trivial or not, has odd frequency
  below `q*`, because `3^a < 2^b`.  Conversely, if Front A holds then every positive orbit is
  eventually periodic and every invariant probability on its finite orbit closure is the
  uniform cycle measure.  After the standard finite-measure plumbing, one should therefore
  have the calibration theorem

  ```
  ParityRigidityW1' ↔ NoDivergentOrbit.
  ```

  This is useful: it says W1' is an exact change of language into a setting where rigidity
  tools might act.  It is not by itself a reduction in logical strength.
* **The current quantifier may be stronger than consumption needs.**  An orbit closure can
  support invariant measures that the orbit never samples statistically.  The board pins
  `EmpiricalParityRigidity`, asking only for a subsequential empirical odd-frequency limit
  below `q*`.  Proving that this weaker pin closes Front A requires finite-shift invariance and
  a tail-minimum/free-floor argument; this is now an explicit open thread rather than hidden
  inside W1'.

**Missing new mathematics**: an arithmetic intertwining theorem that makes the positive-orbit
conditioning visible to ×2×3 rigidity, or an entropy-generation theorem for empirical orbit
limits.  Krylov-Bogolyubov and Portmanteau are plumbing, not the hard step.

## Route A2 - Floor-preserving saturation of Tao's theorem 🌊

Combine the forward statistical theorem with density of backward Collatz trees, but use
**moving high-tail seeds**, not one fixed seed.  `exists_floor_of_diverges` gives, from one
counterexample, tails whose entire future lies above any prescribed `N`.  The required
saturation theorem must amplify those tails while ensuring the backward path does not dip
below the scale being protected.

A strong quantitative target is

```
∃ n, Diverges n
  → ∃ f → ∞,
      upperLogDensity {m | orbitMin(m) ≥ f(m)} > 0.
```

This contradicts Tao 2019 immediately.  `FloorPreservingSaturation` in the Lean board pins the
minimal output form: it produces an `f → ∞` for which Tao's good set fails to have logarithmic
density one, and `noDivergent_of_floorPreservingSaturation` performs the one-line consumption.

**Assets already available**: Tao 2019 forward mixing, Tao 2020 backward equidistribution, and
Krasikov-Lagarias-type backward-tree lower bounds.

**Missing new mathematics**: quantitative control of the *minimum along the backward branch*.
Counting preimages without this height condition is now ruled out, not merely viewed as weak.

### 2026-08-23 pull: the barriered tree has a measurable signal

The first concrete probe is `experiments/barrier_tree.py`.  For a seed `d` and `p ≥ 0`, it
enumerates the finite tree

```
B_d(p) = {m | m reaches d along a path contained in [d, 2^p d]}.
```

The ceiling matters: an endpoint below `2^p d` can otherwise reach `d` through a much larger
intermediate value.  These band-truncated trees increase with `p` and exhaust the full basin
whose path never falls below `d`.  The experiment records

```
H_d(p) = d · ∑_{m ∈ B_d(p)} 1/m,
c_d(p) = (H_d(p) - (2 - 2^-p)) / log(2^p),
```

where `2 - 2^-p` is the exact harmonic contribution of the unavoidable doubling spine.

There is one exact, Lean-checked residue obstruction.  The inverse branches of `x` are `2x`
and, only for `x ≡ 4 (mod 6)`, `(x-1)/3`.  Consequently, if `3 ∣ d`, the *entire* backward
basin of `d` is just `2^k d`; no barrier hypothesis is needed.  See
`FrontA/BackwardTree.lean`.  This does not kill the moving-tail plan: after an orbit takes an
odd step it is a unit modulo `3` forever, so a hypothetical divergent orbit supplies arbitrarily
high tail seeds with `3 ∤ d`.

For units modulo `3`, the initial census found a real signal rather than spine noise:

| seeds | unit seeds | ceiling | min `c_d(p)` | 10% | median | 90% | max |
|---|---:|---:|---:|---:|---:|---:|---:|
| `10000..10179` | 120 | `2^18 d` | 0.2049 | 0.5004 | 1.6700 | 6.4783 | 15.7598 |
| `1000000..1000179` | 120 | `2^18 d` | 0.2213 | 0.4928 | 1.7498 | 5.6077 | 9.4708 |
| `2000000..2000999` | 667 | `2^15 d` | 0.2213 | 0.4588 | 1.5459 | 5.3054 | 36.0056 |

The worst seed in the million-scale sample, `d = 1000052`, remained stable under a deeper
safe-only run:

| `p` | 12 | 15 | 18 | 21 | 24 |
|---|---:|---:|---:|---:|---:|
| `c_d(p)` | 0.2254 | 0.2225 | 0.2213 | 0.2198 | 0.2195 |
| `#B_d(p)` | 412 | 3,149 | 24,223 | 186,303 | 1,475,492 |

The near factor `8` in node count every three increments of `p` suggests linear growth in
`2^p`, while the scaled harmonic mass grows roughly linearly in `p`.  Raw-versus-safe controls
are highly nonuniform: among 36 seeds at `p = 15`, safe harmonic mass ranged from about `2%`
to `100%` of the basin obtained when dips below `d` are allowed.  Floor preservation is not a
harmless constant loss.

**What this buys.**  `UniformBarrierHarmonicGrowth` is now a precise new subtarget, with the
weaker pointwise form beside it.  The census makes this inequality worth attacking; it does
not make it true.

**What it does not buy.**  Undoing the scaling gives only
`∑ 1/m ≍ c_d log R / d` for one seed.  A moving floor requires `d → ∞`, and backward basins of
successive points on one orbit overlap heavily.  Thus even a uniform positive lower bound on
`c_d` does not yet contradict Tao.  The next mathematical pull is an **annular moving-seed
aggregation lemma**: extract disjoint new harmonic mass from successively higher tail seeds
without losing the result to the `1/d` factor or to nesting of their backward basins.

That next pull was tested immediately in `experiments/barrier_tail.py`.  Since no divergent
orbit is known, the proxy takes an ordinary orbit up to its global peak and keeps the strict
future-minimum records: each selected `d_i` has a forward path to the peak staying above
`d_i`, exactly the finite high-floor condition.  Ignoring overlap entirely, the optimistic
additive budget is `∑ c_{d_i}(15)/d_i`:

| excursion start | unit future-minimum records | peak | naive total budget |
|---:|---:|---:|---:|
| 27 | 17 | 9,232 | 0.293888 |
| 77,031 | 14 | 21,933,016 | 0.000154908 |
| 837,799 | 23 | 2,974,984,576 | 0.000006849 |

The product `(starting floor) × (total budget)` stays order one; later-record tail budgets
collapse still faster.  This is a **negative result for naive aggregation**, not a theorem
about a hypothetical divergent orbit, but it exposes the missing input more sharply.  One
needs something like `DivergentTailHarmonicBudget` (`∑_k 1/T^k(n) = ∞` on every divergent
orbit), or coefficients growing strongly enough to replace it, *plus* an overlap/packing
lemma.  Neither follows from divergence alone by an evident argument: an exponentially
escaping orbit would have finite reciprocal budget.  Route A2 therefore remains alive but
is less attractive than the single-tree census initially makes it look.

### The first genuine chip: binary safe branching, and a 3-adic stress test

`FrontA/BackwardBranching.lean` now proves the arithmetic kernel of a uniform pruned tree.
For every `x ≥ 2` with `3 ∤ x`, there are two distinct `y₁,y₂ > x`, still units modulo `3`,
such that each `yᵢ` reaches `x` through a path contained in `[x,128x]`.  The proof is an
exhaustive six-unit-class calculation modulo `9`: among the three admissible odd-inverse
exponents

```
x = 1 mod 3:  j = 2,4,6
x = 2 mod 3:  j = 3,5,7,
```

exactly one child is divisible by `3`, leaving two reusable unit children.  Iterating gives a
binary floor-preserving subtree: at depth `r`, at least `2^r` distinct predecessors fit below
the crude ceiling `128^r d`.  This is now fully proved: `binaryBarrierSubtreeGrowth` produces
the `2^r`-element `Finset` for every unit seed, axiom-clean.  Collisions between children of
distinct odd parents are excluded by the 2-adic valuation of `3y + 1`
(`unitOddBlockChild_parent_eq`), and band witnesses compose (`reachesInBand_trans`).  This is
genuine unconditional progress, but only a counting exponent `1/7`.  It does **not** approach
linear harmonic mass.

The stronger uniform harmonic target was also attacked rather than admired.  The odd-branch
integrality pattern is controlled by increasingly deep 3-adic digits of `d`.  A deterministic
random/prefix search (`experiments/barrier_adversary.py`) found nested low-ternary prefixes
whose normalized slopes decrease:

| seed | `c_d(15)` | `c_d(18)` | `c_d(21)` | `c_d(24)` | `c_d(30)` |
|---:|---:|---:|---:|---:|---:|
| 1,000,052 | 0.2225 | 0.2213 | 0.2198 | 0.2195 | 0.2199 |
| 359,421,848,168,309 | 0.1993 | 0.1909 | 0.1854 | 0.1829 | 0.1789 |
| 798,338,741,946,713 | 0.1914 | 0.1830 | 0.1743 | 0.1696 | 0.1630 |
| 10,205,741,556,338,552 | 0.1914 | 0.1803 | 0.1698 | 0.1639 | 0.1555 |

The last `p=30` run enumerated `52,327,889` safe nodes.  The slope still looks positive for
each fixed seed, but the apparent uniform `0.2` floor is gone.  This suggests a real
pointwise-versus-uniform split: every fixed unit seed might have positive basin density while
the infimum over seeds tends to zero along a 3-adic adversary.  That would be especially bad
for moving-tail saturation, whose seeds are not fixed.

The first variable-height transfer chip is now exact.  `experiments/barrier_transfer.py`
derives the reusable growing odd-child costs in all six unit classes modulo `9`; their
coordinatewise worst stream begins

```
5, 7, 11, 13, 17, 19, 23, 25, ...
```

`FrontA/BackwardTransfer.lean` proves the finite Collatz-specific part: every unit parent
`x ≥ 2` has seven distinct reusable growing children with individual costs bounded by
`5,7,11,13,17,19,23`, their band witnesses have exact ceiling `2^j x`, and children of
distinct odd parents cannot collide for arbitrary costs.  It also proves the exact rational
transfer inequality

```
sum_{j in {5,7,11,13,17,19,23}} (5/6)^j > 1.
```

The standard variable-length tree recurrence therefore has certified exponent
`log_2(6/5) = 0.263034...`; the infinite periodic envelope has critical exponent
`0.266895...`.  This substantially improves the crude `1/7 = 0.142857...` bookkeeping,
without using the shrinking branch.  The generic renewal/tree-growth consequence has not
been formalized in Lean: the theorem-grade new Collatz input and its exact weight inequality
are formalized, while the experiment prints prefix-free finite-budget checks (for example
`15` leaves by cost `19`).  No axiom was added.

The shrinking branch now has a Lean-checked finite certificate as well.  The two height
states are `x ≥ d` and `4x ≥ 7d`.  A high node in classes `2,8 mod 9` may use `j=1`: its
child stays above `d` and returns to the low state.  Every growing child of a high node
remains high; from a low node, every `j ≥ 3` child becomes high.  Tracking unit residues
modulo `27` leaves one unknown ternary digit after division, so each edge is sent
adversarially to the least potential among its three possible lifts.

The first calculation charged each macro edge its gross peak factor `2^j`.  That is safe but
systematically overcharges successive odd endpoints, which satisfy

```
y = (2^j x - 1)/3.
```

For endpoint-height exponent `α`, the correct asymptotic edge weight is therefore
`(3/2^j)^α`.  At `α=1/2`, the completely rational underweight

```
(5/3)(7/10)^j < sqrt(3)(1/sqrt(2))^j = (3/2^j)^(1/2)
```

follows from `25 < 27` and `98 < 100`.  `barrier_transfer.py` exactly verifies the resulting
`36` inequalities (minimum ratio `1.006096707253...`, minimum margin
`0.335318898903...`).  `FrontA/BackwardHeightTransfer.lean` then kernel-checks the same
table without `native_decide` and proves every interpretation bridge: exact seven-child
costs, the two height transitions, the child residue modulo `9`, all three modulo-`27`
lifts, and the local potential expansion for the actual children in both the growing-only
and shrinking-enabled cases.  The shrinking child is proved distinct from every growing
child, and a single odd-block collision lemma handles different odd parents at arbitrary
exponents.

`FrontA/BackwardRenewal.lean` closes the analytic bridge that the rational table alone did
not.  Rational search weights do **not** telescope, so iterating them would not justify the
claimed exponent.  The exact edge weight

```
sqrt(parent / child)
```

does telescope.  Lean proves the certified rational weight is strictly smaller on every
actual Collatz edge, then upgrades both local expansion theorems to these exact weights.
It also separates path destination from path floor (`ReachesToInBand`), proves the generalized
band composition needed by a shrinking child, packages both child regimes into one finite
value-injective interface, and turns an ancestor collision into an explicit `OnCycle`
witness.  Growing-edge peaks are at most `4` times their child endpoint; shrinking-edge peaks
are at most `2` times their parent endpoint.

The finite stopping target is now exact.  Freeze each branch when its endpoint first exceeds
`H`.  Every exit is below `2^23 H`, every complete path is below `2^25 H`, and a stopping
frontier with the telescoping mass has

```
potential(low,d) < card(S) * 200 * sqrt(d/H).
```

Thus it has order `sqrt(H/d)` distinct barriered preimages.  `BackwardStopping.lean` now
proves the recursive existence disjunction too: finite expansion either terminates in such a
frontier, or a bounded endpoint collision supplies an explicit cycle.  Its ancestor-chain
fuel argument is axiom-clean, so `NetHalfRepeatOrStoppingGrowth` is fully discharged.

`experiments/barrier_stopping.py` runs the exact first-exit construction.  It found no repeat
on the tested odd unit roots.  At `H/d = 2^18`, seeds `5,13,17` produced `36,194`, `14,892`,
and `12,030` first-exit leaves, against rigorous square-root floors `253.44`, `174.08`, and
`140.8`; exact mass/root ratios were `13.88`, `8.25`, and `8.21`.  This validates the finite
object and shows that the half-exponent certificate is very conservative.

Numerically, the net-height critical exponent keeps rising as more ternary memory is added.
Using the stable rich height grid, depths `2..7` give approximately
`.436,.611,.689,.734,.761,.780` with the shrinking branch.  Growing-only controls give
`.370,.416,.435,.449,.460` through depth `6`.  Denser height grids do not move the depth-4
value, so residue depth—not height discretization—is presently the main limitation.  This is
encouraging genuine structure, but it still points below the harmonic exponent `1` needed by
the original saturation route.

There is one correlation the preceding conservative operator deliberately discarded.  Given
`x mod 3^k`, the next digit `t` of `x mod 3^(k+1)` is shared by every child.  Its exact
contribution to the cost-`j` child is `2^j t·3^(k-1)` modulo `3^k`, in addition to the fixed
carry digit in `(2^j r-1)/3`.  Replacing the sum of three-lift minima by the minimum of the
three **joint child sums** gives a stronger universal operator.  With residues modulo
`81` and only five height floors `{1,7/4,5/2,3,4}`, its numerical critical exponent is
`0.683819575608`.  More usefully, `barrier_transfer.py` now checks an exact 270-state integer
potential at exponent `2/3`, using the rational underweight

```
(52/25) * (629/1000)^j < (3/2^j)^(2/3).
```

All 810 source-state/lift inequalities are strict (minimum ratio `1.016618220460`).
`BackwardTwoThirds.lean` now kernel-checks this exact table, proves the shared-lift/carry and
five-height interpretation lemmas, and packages the result as `exists_twoThirdsExpansion`
over actual distinct Collatz children.  Its axiom footprint is only the base three.

The completed `2/3` stopping theorem made a deeper correlated search worthwhile.  After
parameterizing that search, the old five-floor grid at ternary depths `3..7` gives critical
exponents `.661695,.683820,.706968,.727160,.740806`.  Unlike the earlier independent-lift
operator, the correlated operator also gains materially from tracking larger endpoint/floor
ratios.  At depth `5`, a rich 21-floor diagnostic reaches `.760516`; the target compresses to
only five floors `{1,7/4,3,6,12}` with critical exponent `.755567122828`.

This yields a new exact candidate.  On unit residues modulo `243`, with the next source digit
tracked modulo `729`, an 810-entry integer potential satisfies all 2,430 shared-lift
inequalities for the rational edge underweight

```
(2279/1000) * (2973/5000)^j < (3/2^j)^(3/4).
```

The comparison follows from `(2279/1000)^4 < 27` and
`8*(2973/5000)^4 < 1`.  The exact common-denominator checker reports minimum ratio
`1.005333383627`; the frozen potential lies in `[1,000,000, 19,334,101]`.  Thus a uniform
exponent-`3/4` first-exit theorem is now a concrete finite Lean target, not merely a spectral
guess.  It still falls short of the harmonic exponent `1`, so even after formalization the
packing/overlap bottleneck remains.

The chippable mathematical ladder is now:

1. ~~finish the binary-subtree iteration~~ — DONE (`binaryBarrierSubtreeGrowth`);
2. ~~replace the uniform `2 children / ×128` charge by individual reusable-child costs~~ —
   DONE locally (`sevenCostTransferAt`, exponent certificate `log_2(6/5)`); the stronger
   exact 36-state net-height certificate at exponent `1/2`, its state interpretation, and
   its application to actual children are also DONE in Lean;
3. ~~replace rational path weights by exact telescoping weights; prove endpoint-to-peak,
   generalized-band, finite-child, cycle-alternative, and square-root frontier lemmas~~ —
   DONE in `BackwardRenewal.lean`;
4. ~~prove the remaining recursive statement `NetHalfRepeatOrStoppingGrowth`~~ — DONE
   (`FrontA/BackwardStopping.lean`, 2026-08-23, axiom-clean).  The proof runs a fuel-`H+1`
   frontier recursion from `(false, d)`: every node carries an odd-parent ancestor chain
   whose length equals its creation round; uniqueness of the odd parent of `3y+1 = 2^j x`
   makes two chains from a common value agree step by step, so **any** collision of a new
   endpoint value with a live frontier value or its own ancestry splices into an explicit
   positive cycle at or above `d`.  In the no-collision branch the chain of a round-`m` low
   node is a set of `m` distinct values in `[d, H]`, so `m + d ≤ H + 1` and the recursion
   terminates in the pinned first-exit frontier.  Mass strictly grows each round by
   `weighted_biUnion_expands` with exact `sqrt(parent/child)` telescoping.  Combined with
   `NetHalfStoppingFrontier.card_bound`, every odd unit root `d ≤ H` now unconditionally
   has either a cycle above `d` or `> V(d)·sqrt(H/d)/200` distinct first exits in
   `(H, 2^23 H)` reached inside `[d, 2^25 H]`;
5. ~~formalize the exact shared-lift 270-state local certificate~~ — DONE in
   `BackwardTwoThirds.lean`, including the modulo-`243` interpretation, five height
   transitions, and actual-child expansion.  The analytic half of the `1/2`→`2/3` upgrade is
   now also DONE in `BackwardTwoThirdsRenewal.lean`: the exact real edge weight
   `(x/y)^(2/3)` (`Real.rpow`), its strict rational underweight on actual blocks
   (`twoThirdsRationalWeight_lt_edgeWeight`, cube comparison `(52/25)^3 < 9`,
   `4·(629/1000)^3 < 1`), exact telescoping through positive endpoints
   (`twoThirdsEdgeWeight_mul`), the finite value-injective child set with real-weight
   expansion (`exists_twoThirdsChildFinset`), potential positivity/ceiling `1051827`, the
   `TwoThirdsStoppingFrontier`/`TwoThirdsRepeatOrStoppingGrowth` objects, and the stopping
   cardinal bound `V(0,d) < card(S)·(1051827·(d/H)^(2/3))`.  The recursive
   `TwoThirdsRepeatOrStoppingGrowth` is now also DONE (as a THEOREM) in
   `BackwardTwoThirdsStopping.lean`: the fuel-`H+1` frontier recursion ported from
   `BackwardStopping.lean` onto `Fin 5`/`InFiveHeightState` nodes, reusing verbatim the
   value-based `StoppingChain`, `chain_agree`, `chain_reachesValuePos`,
   `StoppingChain.round_add_le`, `reusable_band_step`, and `reachesValuePos_self_iff_onCycle`,
   with strict mass via `weighted_biUnion_expands` under the exact `(x/y)^(2/3)` telescoping
   (`twoThirdsEdgeWeight_mul`).  The `NoNontrivialCycle` wiring
   (`twoThirdsStoppingFrontier_of_noCycle`) eliminates the cycle alternative, a kernel-checked
   uniform lower bound `100000 ≤ twoThirdsPotential i x` on unit residues
   (`twoThirdsPotential_ge_min`) is added, and the explicit corollary
   `twoThirds_stopping_card_bound` gives, for every odd unit `2 ≤ d ≤ H`, a value-injective
   first-exit frontier `S` with `100000 < card(S)·1051827·(d/H)^(2/3)`, endpoints in
   `(H, 2^23 H)` reached inside `[d, 2^25 H]`.  Axiom audit: base three
   `[propext, Classical.choice, Quot.sound]`, no `native_decide`.  Thus the exponent-`2/3`
   frontier is now unconditional exactly as the `1/2` frontier was;
6. formalize the frozen exponent-`3/4` local certificate: modulo-`729` shared source lift,
   modulo-`243` child state, floors `{1,7/4,3,6,12}`, and the 810-state potential; then port
   the already-proved real-rpow renewal/stopping layer from exponent `2/3` to `3/4`.
   **DONE (2026-08-24).**  Certificate `exists_threeQuartersExpansion`
   (`BackwardThreeQuarters.lean`); renewal layer `BackwardThreeQuartersRenewal.lean` with the
   real edge weight `((x)/(y))^(3/4)`, the fourth-power underweight
   `(2279/1000)(2973/5000)^j < (3/2^j)^(3/4)` (from `(2279/1000)^4<27`, `8(2973/5000)^4<1`),
   exact telescoping, value-injective `exists_threeQuartersChildFinset`, potential ceiling
   `19334101`, and `ThreeQuartersStoppingFrontier.card_bound`; stopping layer
   `BackwardThreeQuartersStopping.lean` with the fuel-`H+1` recursion
   `threeQuartersRepeatOrStoppingGrowth`, cycle elimination
   `threeQuartersStoppingFrontier_of_noCycle`, uniform potential minimum `1000000`, and the
   discharged pinned corollary `threeQuarters_stopping_card_bound`:
   `1000000 < card(S)·19334101·(d/H)^(3/4)`, endpoints in `(H, 2^23 H)` reached inside
   `[d, 2^25 H]`.  Axiom audit: base three plus the allowed native_decide certificate axioms
   (810-entry array, scale `1000·5000^23`).  The full ladder step (certificate → renewal →
   stopping) is now a mechanical port at any exponent; `3/4 < 1` still, so this is a rung, not
   the harmonic target;
7. formalize the exact depth-8 exponent-`4/5` candidate.  The shared-lift search on floors
   `{1,7/4,3,6,12}` has numerical critical exponent `.801207515868`; more importantly, the
   generated 21,870-state potential exactly passes all 65,610 inequalities for
   `(75257/31250)(574349/1000000)^j < (3/2^j)^(4/5)`, with minimum ratio
   `1.001017912682` and weights in `[1000000,41080952]`.  Child state is modulo `6561`, the
   shared next source digit lifts to modulo `19683`, and all five height floors are needed by
   the tested exact certificate.  The final end-to-end corollary is pinned in
   `BackwardFourFifthsStopping.lean`; complete local certificate, renewal, and stopping in
   one project;
8. decide experimentally, then prove, whether the correct theorem is pointwise harmonic
   growth or a uniform bound—the 3-adic adversary is the falsification side;
9. only if enough uniformity survives, return to `DivergentTailHarmonicBudget` and annular
   packing.  Otherwise Route A2 has merged back into the positive-integer itinerary rigidity
   problem of Routes A1/A3.

## Route A3 - Symbolic/carry certificates 🤖

The Bernstein-Lagarias conjugacy turns the parity itinerary into a shift sequence, while
multiplication by `3` is a base-2 transducer.  A successful theorem has to distinguish the
itineraries of ordinary positive integers from the unrestricted 2-adic full shift.  Carries
are the concrete coupling between those two worlds.

There are two plausible output forms:

1. a Cobham/transducer rigidity theorem showing that a positive-integer itinerary cannot
   sustain the required near-critical drift indefinitely;
2. a machine-found, kernel-checked **repeat-or-descend certificate**, possibly using weighted
   automata, matrix interpretations, or richer parity/carry features.

The second output form is deliberately weaker than a universal termination certificate.  It
allows the repeat alternative and therefore does not claim to settle cycles.  This makes it a
clean target for Front A and a better search space than `DescentAll` when the two-proof
architecture is being respected.

Transfer-operator/spectral methods from `APPROACHES.md` fit here as an analytic certificate
variant: the desired spectral inequality must ultimately imply either empirical parity
rigidity or repeat-or-descend.

## Current priority order

1. **Orbit-limit parity rigidity**, but work with the weakest empirical pin that the drift
   consumption actually needs; keep the all-supported-measures W1' as the stronger target.
2. **Floor-preserving saturation**, beginning with inequalities for backward branches of the
   high-floor tails supplied by a hypothetical divergent orbit.
3. **Repeat-or-descend certificates**, using the existing carry/transducer infrastructure and
   treating a repeat as a permitted Front-B handoff rather than certificate failure.

No route is close.  The board's immediate value is negative and architectural: it prevents
raw density amplification, pure 2-adic measure claims, and universal-descent requirements
from being mistaken for correctly scoped Front-A progress.
