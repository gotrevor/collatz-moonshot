# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE — awaiting a new idea; no execution lap selected

Set by the **2026-09-13 whole-repository reflection**, reconciled through
`6a33554`, from baseline `5a54acc`. This supersedes all older assignments and
rankings in handoffs, route maps, source docstrings, and PENDING_WORK history.

**Nothing currently on Front A or Front B clears the bar of probability times
magnitude of NEW mathematics for a bounded objective.** Do not launch another
proof lap from the deferred list. This is a judgment about the presently
specified mechanisms, not an impossibility theorem or a claim that Collatz is
unprovable. The completed campaign remains green and useful.

The operator explicitly requested reflection and documentation only. That
instruction overrides reflection.md's generic instruction to implement a proof
step afterward. No Lean proof, new experiment, or Aristotle job is part of this
lap. Its deliverable is this reconciled decision and the verification/handoff.

## What the completed laps actually bought

The git range contains 17 commits after the baseline, including host experiment
commits and direction reviews; it is not 17 independent proof advances.
`5a54acc` itself is dated September 8 and closes the front-normalized rung-3
classification at length 8. It is the settled baseline for this review.

| Commits | Reconciled result | Limit on what follows |
|---|---|---|
| `f8fa4a5`, `cf8d748`, `56304ac`, `5ea1b38`, `9b5dc54` | Rung, word-model, and orbit censuses; recorded length sweep 2..80 has hits at 8,27,46,65,73. | Finite data; a cluster on the trajectory of 27 is not a universal theorem. |
| `26c49b9`, `c3aba74` | Campaign A2: exact trunk slack/criterion, 2305/2313 obstruction, and null-model audit. | Prefix remainder cannot be dropped. The proved model law is not a distribution law for admitted integer traces. |
| `529ccef`, `4a12a68` | Arbitrary-block cascade, rational envelope, and explicit fixed-run length bound. | Complete for each fixed b, not uniform in b. “Campaign B” here is work on Front A, not a proof of the cycle front. |
| `9ae73a3`, `972c772` | Further fixed four-block empty censuses and corrected census commentary (minimum observed run ratio 9/46; first populated rung after 3 is 7). | No global run-density law; no new theorem from editing the summary. |
| `5bdea84`, `882c787` | Rational short-run positivity question selected, then refuted by a primitive Q=2 family at unbounded length. | Rational positivity does not imply integer admission. |
| `bc4158e`, `3a3e838` | Six-letter admission question selected, then refuted by a padded primitive Q=2 family. | The certified filter is exactly P_6; full admission remains separate. |
| `e6cb096`, `6a33554` | Odd-start strict cycle-witness edge selected, then proved; unrestricted pair finiteness now implies Collatz. | New formal dependency information, not a proof of either finiteness hypothesis. |

The fixed-b theorem is

```
odd n ∧ AcyclicParadoxical n m ∧ oddRunCount(traceWord n m) ≤ b
  → m < 4*((2^b−1)*(b+53342))^2+b.
```

It includes a terminal odd run without adding a trajectory step. The rational
small-vertex argument and repeated squaring produce the factor `2^b−1`; the
existing polynomial 2/3 separation closes the feedback. This is a meaningful
extension to strict segments, but its mechanism is the Simons–de Weger pincer
on a new object. Their fixed-circuit finiteness combines an elementary upper
bound with logarithmic-form separation; its rate deteriorates with circuit
count. It is not a source of uniform compression. Source availability is
resolved. [Simons–de Weger v1.44, Theorem 3, Lemmas 7/12, §8](https://deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.44%5B2010%5D.pdf).

Do not confuse the benefits: rung classification and fixed-b formalization
advance restricted structure; the obstruction families eliminate relaxations;
cycle repetition clarifies the graph. None supplies the remaining uniform
integer-trajectory input. Another known specialization does not inherit novelty
from having a fresh theorem name.

## Exact statement and dependency graph

`Conjecture` means every positive integer reaches 1 under the standard map
`step`; `NoDivergentOrbit` excludes unbounded positive orbits;
`NoNontrivialCycle` permits only 1,2,4 on positive standard cycles.
Their conjunction is equivalent to Conjecture by `conjecture_iff_split`.
Paradoxical segments instead use the shortcut map `tstep`.

```
AcyclicParadoxical n m :=
  n>2 ∧ m>0 ∧ 3^ones(traceWord n m)<2^m ∧ n<tstep^[m] n
U := {(n,m) | AcyclicParadoxical n m}
O := {(n,m) ∈ U | n is odd}
```

“Acyclic” means strictly unequal endpoints. Interior repetitions are allowed.
The sets count pairs, not distinct starts, primitive words, first returns, or
segments before first descent. These distinctions are load-bearing.

The default build proves:

- `U.Finite → NoDivergentOrbit`.
- `U.Finite → O.Finite → NoNontrivialCycle`.
- Hence `U.Finite → Conjecture`.
- An odd shortcut periodic member n>2 produces infinitely many lengths in O,
  by repeating its period and appending one odd step. Infinitely many starts
  are neither needed nor claimed.
- `ParityRigidityW1' → NoDivergentOrbit`; also
  `RepeatOrDescendCertificate ↔ NoDivergentOrbit`.
- `NoNontrivialCycle ↔ FrontB` in the integral-word dictionary.

All these displayed edges are trust-base clean. **Still open:** O.Finite,
U.Finite, O.Finite→U.Finite, both unconditional fronts, W1', compression and
the other research predicates. `Conjecture → U.Finite` is not supplied by
this graph. Pointwise termination does not supply a uniform pair bound.

The old “Front A only” reading of paradoxical finiteness is now decisively
wrong: even O.Finite carries cycle exclusion. A uniform bound on odd-start
run count, together with fixed-b finiteness, repackages O.Finite; a uniform
length bound does likewise (finitely many words, each with finitely many
starts below its threshold). Neither is a harmless auxiliary assumption.

## Standing obstruction: full admission is the missing information

For a Boolean word v of length m with a ones, put `N=numer(v)` and
`D=2^m−3^a>0`. Its full realizing residue and least allowed start are

```
r_m = [−N*(3^a)^(-1)] mod 2^m
c_m = min {n ∈ ℕ | n>2 and n≡r_m mod 2^m}.
```

A word admits a strict paradoxical start exactly when `D*c_m<N`. All its
admitting starts are the representatives n>2 in that residue class with
`D*n<N`. Keep the least-above-2 correction when r_m≤2. In contrast, the
rational affine fixed point is `N/D`; positivity of it and of every internal
head does not realize the word as a small integer trajectory. For an actual
integer cycle the endpoint equality instead requires `D*n=N`.

`882c787` certifies `(XY)^k XYY`, X=TF, Y=TTF, with bounded run lengths,
primitivity and all rational head slacks positive, for unbounded k. Its common
six-bit residue is 57, above N/D. `3a3e838` certifies
`(XY)^(2j+12) X Y^17`, j≥0, at lengths 10j+113, with the same positivity and
primitivity and now `D*57<N`. Thus even that necessary entry test admits an
unbounded family. Both are mathematical all-parameter arguments with exact
rational scripts, not new Lean theorems.

Evidence boundary: the checked-in second certificate proves P_6 survival,
not an arbitrary-L theorem. Its full-admission rejection check covers 36
parameters. Prior operator context additionally reports universal full
rejection with canonical starts of about m bits; no corresponding universal
proof artifact was added to this repository. The current operator treats
finite-prefix relaxations as exhausted. **All fixed finite-prefix follow-ups
remain retired**, without relabeling the P_6 certificate as a theorem for every
L. Neither that retirement nor these examples refutes every symbolic proof.

At fixed (m,a,N) the full residue is deterministic. A uniform argument must
therefore consume trajectory-side information: the actual small start and
all its parity/carry compatibility. This can be expressed symbolically, but
cannot be replaced by rational head positivity, a fixed-prefix test, or an
independent random-residue model. A2's exact trunk criterion already shows why
retaining only the minimum and subsequent climb loses decisive information.

## Whole-board ranking: all below the bounded-objective bar

This is an ordinal ranking of present research prospects, **not a work queue**.
“High magnitude” means a new mechanism would matter; it does not make an
unspecified mechanism a bounded task. Historical 40%, 55%, and 70% route odds
are conditional speculation about eventual solutions, not success probabilities
for the next lap. They have no scheduling authority.

| Rank | Candidate | Probability × magnitude of NEW mathematics in a bounded lap | Decision / missing deliverable |
|---|---|---|---|
| 1 | Front A: a new trajectory constraint beyond RT's harmonic-mean condition | Low for an unconditional strengthening × high; high for a faithful port × negligible new mathematics | No proposed extra inequality controls admission or couples the mean to length/start strongly enough. Do not assign the port. |
| 2 | O.Finite → U.Finite | Unassessable without a specified map (treat as low) × substantial graph value | No map with target membership and finite fibers is known here. “Normalize even starts” is not an objective. |
| 3 | Coefficient stopping time (CST), or a genuinely new restricted obstruction to its failure | Low × high; known equivalence/verification ports have high probability but low new content | No fresh restricted class and mechanism are specified. Global CST is an open cycle-excluding conjecture. |
| 4 | Carry/transducer or repeat-or-descend certificate | Very low at present × very high | No state space with a proved sound transition invariant and a surviving descent/recurrence certificate. The interface alone is exactly Front A. |
| 5 | W1' parity rigidity / Furstenberg intertwining | Very low × very high | No arithmetic transfer from a positive integer orbit to the joint ×2,×3 action, nor applicable entropy input. The conditional consumer is already complete. |
| 6 | Tao forward/backward saturation; pointwise harmonic growth and packing | Very low × very high | Need actual high-floor harmonic mass AND control of overlap across moving seeds. Neither follows from the completed subharmonic certificates. |
| 7 | Front B primitive compression, bounded denominator, or a new Knight-type identity class | Very low × high | No transformation preserving integrality/nontriviality while reducing complexity, and no new identity class. Fixed-circuit finiteness does not bound circuit count. |
| 8 | Numerator/residue discrepancy or cycle counting | Very low at the useful error scale × high | No estimate reaching an integer exclusion threshold; mean behavior is not enough. Exact conditioning leaves no randomness. |
| 9 | The 4614 cutoff, U.Finite itself, global start/length/run bounds | No credible bounded attack × very high | These are destination conjectures, not reductions. Increasing a census cannot prove their universal quantifiers. |
| 10 | More fixed rungs, sharper fixed-b constants, cycle transport, standard certificate/axiom ports, converse wiring | Often high × little or no new mathematics | Valuable formalization under a separately requested objective, but below this operator's bar. |

RT Theorem 4.2 says `1−C≤E/n≤((3+1/h)^a−3^a)/2^m`, where h is the
harmonic mean of the actual odd terms, C=3^a/2^m and E=N/2^m.
Its upper bound is a product/AM–GM
estimate. It gives a necessary condition, not control of h as the trajectory
varies. CST is `t(n)=τ(n)` for n≥2, including infinite values; equivalently a
paradoxical segment contains an earlier value below its start. Conjecture 6.1
excludes all paradoxical starts above 4614. Those conjectures must not be
assumed as known constraints. [Rozier–Terracol v5, §§1,4,6](https://arxiv.org/html/2502.00948v5).

For rank 2, even-prefix deletion sends the actual 18@8 witness to 9@7,
which is not subcritical. Reanchoring at a minimum does not repair coefficient
control automatically, and forgetting prefix depth does not prove finite
fibers. A real proposal must specify a map `f:U\E→O` for an explicitly finite
exception set E (possibly empty), prove membership for every input, and bound
or otherwise prove each fiber finite. No such map is supplied by this review.
If proved, this would make O.Finite sufficient for full Collatz through the
existing U edge; it still would not prove O.Finite.

For ranks 4–6, distinguish three inputs that an umbrella “rigidity certificate”
can conceal. Pure 2-adic invariant measures are not constrained by positivity
of the original integer: the existing negative-cycle witness defeats the
unconditioned parity claim. Topological Furstenberg rigidity is already proved
in this repo; it supplies neither the missing arithmetic intertwining nor a
measure entropy theorem. W1' uses standard-map threshold `log 2/log 6`, not
the shortcut threshold `log 2/log 3`. Its expected converse is finite-measure
calibration, still only a pinned target here, not new rigidity. W1 without the
prime is stronger and would also exclude nontrivial positive cycles.

Tao's result concerns orbit minima for logarithmically almost all starts.
A large backward basin entering one fixed seed d has orbitMin≤d and is
eventually Tao-good. The existing `mem_taoGood_of_reachesValue` formalizes the
failure of that amplification argument. A useful replacement needs moving
high floors and a positive logarithmic-density contradiction.
[Tao, Almost all orbits attain almost bounded values](https://arxiv.org/abs/1909.03562).
The exponent-4/5 renewal/stopping pipeline is complete; another exponent below
1 does not provide the harmonic budget. The harmonic obstruction excludes the
specified five-floor, constant-lift certificate scheme; it is not a theorem
against every enriched state space. Escaping that scheme without a proposed
invariant, or merely porting a larger table, is not a bounded new idea.

## Front B statement audit: do not trust obsolete labels

Reading `FrontB/Threads.lean` and `Powers.lean` exposes two residual mismatches.
These are source-grounded mathematical deductions recorded here, **not new
kernel theorems or proof assignments**:

1. `CountingGivesFinite` currently counts **all** nontrivial integral words,
   not primitive cycles. If v is one such word, `wpow v (j+1)` remains integral
   and nontrivial by `integerCycle_wpow_iff` and `isTrivial_wpow_iff`.
   `length_wpow` gives length `(j+1)*v.length`; v is nonempty, so the words
   are distinct. Thus that literal finiteness predicate implies FrontB, whose
   converse makes the set empty. `FinitenessIsNotEmptiness`, currently defined
   as this predicate AND `¬FrontB`, is consequently impossible. The comment
   that this is a weaker counting conclusion is false for the written type.
   Finiteness without emptiness is the appropriate warning for **primitive
   cycles** (or cycles modulo powers), a different population.
2. `LadderCompletes` universally quantifies over every circuit bound C.
   Set C to the primitive word's own circuit count and use primitive-root
   decomposition to see that it too is equivalent to FrontB. Fixed-C
   finiteness does not give fixed-C exclusion, let alone this whole ladder.

`NaiveCompression` and `NaiveBoundedDen` already have their power-degeneracy
proofs. Primitive `Compression` avoids that particular defect, but its unknown
constant does not finish the front: one still needs to exclude the finitely
many survivors up to that constant. A bound ≤91 closes only through the named
Hercher citation. The earlier route-map assertion that *any* bounded denominator
or circuit count automatically dies against a known lower bound overclaims.
A bound must be explicit and within verified exclusions, or the survivors
must be eliminated independently. No kernel theorem here says otherwise.

Other board entries have not acquired a mechanism overnight: rotation gcd
harvesting is already killed by unit-multiple equivalence; logarithmic-form
and abc lower bounds alone lack the upper bound/exclusion input; sign-blind
cycle arguments must survive the negative-cycle falsification harness;
sum-product, zero-entropy classification, function-field carry transport,
Cobham rigidity, and independence/Goodstein analogies have no specified
load-bearing lemma. Importing entropy definitions, translating citations, or
formalizing the two accounting corrections above does not clear the novelty
bar. Leave their formal interfaces unchanged in this documentation-only lap.

## Trust, verification, and reopening condition

The default source has zero disclosed sorries. The fixed-b headline inherits
eleven existing Rhin-lite native certificates; it is not bare-trust-base-only.
The new cycle witness and both finiteness edges use exactly `propext`,
`Classical.choice`, `Quot.sound`. RT 3.2, power approximation, and topological
Furstenberg are proved, despite historical file names under Assumed.

Named citation debt remains: Tao, Eliahou/Hercher bounds and computations,
Baker bounded difference; abc is an explicitly conjectural input to conditional
results. Historical Rhin axiom routes in `wip/` are retired and not root
imports. Cited axioms are debt, not permanent mathematical destinations;
discharging them still does not create the missing uniform mechanism.

The handoff records the real full build, fixed-b audit, trust-only graph audit,
existing obstruction certificates, and proof-debt check. No new arithmetic
claim was kernel-proved in this reflection.

**Standing state: awaiting a new idea. No next proof lap is authorized by this
file.** Reopen only when a proposal names an exact bounded statement, a first
attack with concrete mathematical evidence, the new information it consumes,
an acceptance test, and a costume check against the obstructions above.
For the even-start edge the actual finite-to-one map is mandatory. For a
uniform Front-A route the small integer trajectory must be load-bearing.
For Front B the proposal must go beyond fixed-circuit finiteness and preserve
the correct primitive/integral population. These are admission criteria for a
future idea, not assignments to search each row in turn.

The reflection objective is complete. Use `box done` after the green commit,
not `box stuck`: absence of a promising current idea is not an impossible
external condition or a request for an operator decision. Do not resume the
completed cycle edge, enlarge a prefix filter, or substitute routine
formalization merely to keep the treadmill moving.

Newest checkpoint: `HANDOFF-2026-09-13-whole-board-reflection.md`.
Earlier directions remain recoverable in git and dated handoffs.
