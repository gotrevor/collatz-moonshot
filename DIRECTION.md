# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

Set by the **2026-09-13 post-prefix altitude review**, reconciled through
`3a3e838` (the sole commit since `bc4158e`). This replaces the six-letter
assignment. Earlier assignments below are history, not a queue. **This review
selects direction only: no proof work is started in this lap.**

### Reconciliation: both relaxation questions are ANSWERED

`882c787` refuted the rational short-run length bound with the primitive
Q=2 family `(XY)^k XYY`, X=TF, Y=TTF. Its invariant interval certifies every
internal head, but the entry residue 57 mod 64 exceeds its threshold N/D.
`bc4158e` consequently selected the fixed six-letter filter P_6.

`3a3e838` refutes that filter's boundedness with the padded family

```
w_j=(XY)^(2j+12) X Y^17, j≥0;
a=6j+71, m=10j+113, b=4j+42, c_6=57;
k=2j+12;
5*(N-57D)=409787117366273728*32^k+256*3^35*27^k > 0.
```

The interval [34/5,225] certifies all head slacks ≥8/5 and subcriticality;
odd a,m and 5a−3m=16 certify literal Boolean-word primitivity. There are no
exceptional j. This is the old family with fifteen terminal Y blocks added;
the new content is the all-parameter strict prefix margin. Read
`PREFIX-ADMISSION-OBSTRUCTION-2026-09-13.md` and its handoff. This review
reran the existing exact certificate; it remains a mathematical certificate,
not a new Lean theorem.

**Reconcile evidence levels explicitly.** The checked-in proof/script establishes
universal P_6 survival and checks full rejection at 36 parameter values. The
current operator additionally reports independently host-verified **full
rejection for every member**, with full canonical n0 having about m bits.
Accept that report as current campaign context; the repository's finite-probe
output alone does not establish the universal full-rejection assertion. No
host proof artifact or new Lean proof of that assertion is added in this review.

The relaxation thread is retired. **Do not choose a larger L, any other fixed
finite-prefix filter, or a sequence of such filters.** The two counterfamilies
prove the two stated obstructions, not a general arbitrary-L theorem; the ban
on further filters is a direction decision about the same unproductive ladder.
Uniform enforcement of all prefixes reaches full admission itself.

For a word v of length m, a=ones(v), D=2^m−3^a>0, the missing datum is

```
r_m=[−N(v)*(3^a)^(-1)] mod 2^m;
c_m=min {n∈ℕ : n>2 and n≡r_m mod 2^m};
full admission: D*c_m<N(v).
```

When r_m>2, c_m=r_m. Keep the least-above-2 correction otherwise. Admission
says that the word is the actual trace of a small integer start below N/D.
Rational fixed-point positivity supplies neither that trace nor an integer
cycle. New work must expose trajectory information, not another word relaxation.

The day's other completions remain closed: rung 3 (`5a54acc`, front-normalized
length 8); excursion A2 (`c3aba74`, exact prefix remainder retained); and
fixed-b Campaign B (`4a12a68`), with
`m<4*((2^b−1)*(b+53342))^2+b` for odd-start segments with at most b odd runs,
including a final odd run. No uniform-in-b claim follows. The recorded census
2≤m≤80 and its 2305/2313 controls are unchanged; no larger census was run here.
The 0.22*m run bound and the naive 18@8→9@7 normalization remain refuted.

### Source-audited graph: the overlooked cycle edge

Write

```
O = {p : ℕ×ℕ | p.1 % 2=1 ∧ FrontA.AcyclicParadoxical p.1 p.2};
U = {p : ℕ×ℕ | FrontA.AcyclicParadoxical p.1 p.2}.
```

`FiniteAcyclicParadoxical` is exactly U.Finite. The predicate in
`FrontA/Paradoxical.lean` requires n>2, m>0, 3^a<2^m and T^m(n)>n.
**“Acyclic” means unequal endpoints; it does not prohibit interior repetitions.**
It has no primitivity, first-return, first-descent, or odd-start requirement.
Do not import the obsolete relaxation population's extra restrictions.

Already kernel-checked:

- U.Finite → NoDivergentOrbit (`finite_acyclicParadoxical_imp_noDivergent`).
- Conjecture ↔ NoDivergentOrbit ∧ NoNontrivialCycle (`conjecture_iff_split`).
- A positive shortcut cycle has 3^a<2^L (`subcritical_of_tstep_cycle`).
- Period counts add (`ones_traceWord_mul_of_cycle`); constant multiples of
  smaller powers are eventually dominated (`const_mul_pow_lt_pow`).
- A standard cycle supplies a related shortcut periodic member
  (`FrontB.tstep_cycle_of_step_cycle`), with its precise related-member cases.

The existing `infinite_paradoxical_of_tstep_cycle` constructs equal-endpoint
period multiples for **Paradoxical**, not strict **AcyclicParadoxical** witnesses.
Source search found no odd-start cycle-exclusion edge or U.Finite→Conjecture
corollary. The next objective is the missing strict-endpoint strengthening,
followed by its direct consumption. Its proposed mechanism is a repeated
period with one genuine odd step appended, at an odd periodic member above 2.
This is a target and first attack, **not a theorem proved by this review**.

Still open: O.Finite itself; U.Finite itself; O.Finite→U.Finite; both
unconditional fronts; and ParityRigidityW1'. A global odd-start length or run
bound repackages O.Finite with the existing fixed-b result, so cannot be an
assumption disguised as a lemma. U.Finite is not literally the paper's
Conjecture 6.1: that conjecture specifies the cutoff 4614 for **all** paradoxical
starts. Historical source docstrings conflating those statements are not authority.

### Ranking by probability × magnitude of NEW mathematics

These are subjective ordinal judgments about one bounded lap. A new graph edge
has value, but elementary cycle repetition is not a literature-novel Collatz
mechanism. No candidate gets credit for renaming an open finiteness statement.

| Rank | Candidate | Probability × magnitude | Decision |
|---|---|---|---|
| **1** | **(vi) Reconciliation's cycle-exclusion edge: O.Finite → NoNontrivialCycle** | High: the exact period and power APIs exist × moderate: settles whether the odd-start node already controls Front B, and completes U.Finite's conditional route to Collatz | **CHOSEN**, one bounded edge package below. New to this graph, no literature novelty claimed. |
| 2 | (ii) O.Finite → U.Finite | Low-medium without an actual finite-to-one construction × high if achieved | Deferred. The 18@8 counterexample kills only `(2^k*u,m)↦(u,m−k)`. No replacement map with proved target membership and finite fibers has been identified. A promise to “normalize” is not an objective specification. |
| 3 | (v) Trajectory constraints beyond the known stopping-time results | Medium for faithful conditional wiring, low for a stronger unconditional exclusion × potentially high | Deferred as a separate campaign. The literature constraints below calibrate the chosen edge; merely porting them or restating restricted finiteness is not new arithmetic. |
| 4 | (iii) Coarse residue-given-numerator discrepancy | Low for an error bound useful at rare admission thresholds × high if achieved | Ineligible now: no useful error scale is established. A null-model law or a bound of the order of the whole population supplies no exclusion. |
| 5 | Fixed-circuit Front B transport, certificate ports, further finite filters | High for known specializations × low new content | Not selected. Finite-prefix work is prohibited; fixed-circuit finiteness is known and supplies no uniform compression. |

**Front A versus Front B.** The day removes word-relaxation evidence for a
uniform Front-A bound; it does not create an independent Front-B compression
idea. Fixed-b finiteness is still meaningful but insufficient. Reconciliation
instead suggests that odd-start pair finiteness already excludes cycles. Check
that edge before funding a separate cycle lane. If it closes, U.Finite becomes
one explicit sufficient input for both fronts, while O.Finite still lacks a
proved divergence consequence. This changes the graph's dependency accounting,
not the difficulty of proving either finiteness hypothesis. Simons–de Weger's
source is available; lack of source is not a current blocker.

### Trajectory literature calibration (not new proof assignments)

In the shortcut convention, Rozier–Terracol Theorem 4.2 gives
`1−C≤E/n≤((3+1/h)^a−3^a)/2^m`, h the harmonic mean of odd terms;
Corollary 4.3 gives `log2/log(3+1/h)≤a/m<log2/log3`.
Terras' CST conjecture is `t(n)=τ(n)` for n≥2, including infinite values:
first strict descent equals first coefficient below 1. Equivalent formulations
require a paradoxical segment to contain an earlier value below its start.
The paper reports Terras' verification through 250000, Garner's through
1150000 (his Col convention), and extends CST through `2.8×10^19` in
Corollary 5.4. Conjecture 6.1 excludes paradoxical starts above 4614; Theorem
1.3 reports 593 segments at or below 4614 and none further through that verified
range. These are source results, not this repository's 320-control census or
new kernel certificates. Section 6 conditionally derives finiteness from a
uniform logarithmic total-stopping-time bound; that bound remains conjectural.
[Primary source, v5, §§1,4–6](https://arxiv.org/html/2502.00948v5).

Neither the harmonic constraint nor verified CST gives full admission for
arbitrary starts. CST includes a cycle consequence, but no CST assumption is
needed or allowed for the selected edge. No strongest-in-all-literature claim
is made beyond the precise source results just checked.

### Deferred discrepancy specification (retain the actual population)

For future altitude comparison only: W(m,a) consists of **all Boolean words**
of length m starting T, with a odd letters and D=2^m−3^a>0, each counted once.
For j≥0 let
`W_j={v∈W(m,a): 2^(−j−1)<N(v)/(D*2^m)≤2^(−j)}`, with a separate overflow
bin above 1. Compare

```
A_j = Σ_(v∈W_j) 1[D*c_m(v)<N(v)],
μ_j = Σ_(v∈W_j) p_odd(N(v)),
```

where p_odd counts starts in {3,5,…,2^m+1} strictly below N(v)/D, divided by
2^(m−1). At exact (m,a,N), the residue is deterministic. Any proposed error
E_j must explain its consequence for these actual sums: an emptiness argument,
for example, would need `μ_j+E_j<1` in every relevant bin plus control of the
overflow and all (m,a). No such scale or theorem is presently available;
we do not select a distribution campaign on the strength of a model analogy.

### ONE BOUNDED OBJECTIVE — the odd-start finiteness cycle-exclusion edge

**Next lap only:** prove the following edge, with a named predicate (a `def`,
never an axiom) for O.Finite:

```
finite_odd_acyclicParadoxical_imp_noNontrivialCycle :
  O.Finite → NoNontrivialCycle
```

The load-bearing intermediate is the exact strict-endpoint witness statement:

```
∀ n L, 2<n → n%2=1 → 0<L → T^[L] n=n →
  {m : ℕ | FrontA.AcyclicParadoxical n m}.Infinite.
```

**First attack.** Read the existing cycle/power lemmas in
`CollatzMoonshot/Assumed/Paradoxical.lean` and the standard/shortcut dictionary.
For an odd periodic member n>2, set a=ones(traceWord n L), A=3^a, B=2^L.
Try the explicit witness map

```
f(j)=(n, L*(J+j)+1), with J=3*A, j∈ℕ.
```

The next lap must check these exact obligations: the endpoint is T(n)>n;
the count is `(J+j)*a+1`; and `3*A^(J+j)<2*B^(J+j)`. The existing
`const_mul_pow_lt_pow` at c=3 provides the proposed starting estimate; carry
it to all j. Length injectivity follows from L>0. This map is an **injection
from period repetitions into O**, not an even-start normalization or a
finite-to-one map O←U. J need not be sharp.

Then extract an odd periodic n>2 from any hypothetical nontrivial standard
cycle. The dictionary may give a related member rather than the original
one; discharge that case and transport periodicity to an odd member. Exclude
entry into the trivial 1↔2 shortcut cycle explicitly. Do not assume the minimum
of the standard cycle is automatically returned by the dictionary.

**Acceptance criterion.** Kernel-check the displayed infinite-witness node
and its consumer O.Finite→NoNontrivialCycle. As the direct consumption of this
same edge, restrict U.Finite to O and compose with the existing divergence
closer to export

```
finite_acyclicParadoxical_imp_conjecture :
  FiniteAcyclicParadoxical → Conjecture.
```

This corollary introduces no further research assumption or second campaign.
Print axioms for both new edges and the witness theorem: standard trust triple
only, no CST/Collatz/cycle-exclusion axiom, no sorry, and no new native certificate
should be required. Run the real full gate and preserve the existing headline
and fixed-b audits. Update the applicable source strength caveat so it states
the proved implication faithfully, without identifying U.Finite with the
numerical 4614 conjecture. Commit green work and stop.

A kernel-checked load-bearing witness node with the precise remaining bridge
recorded is honest progress, not completion of the entire edge. If the proposed
map fails, provide the exact failed membership/count inequality or a verified
counterexample to that map; do not claim a counterexample to an implication
from O.Finite. Do not weaken the goal, add a global stopping hypothesis, or
silently substitute non-strict Paradoxical. No proof is attempted in this review.

**Costume check.** O.Finite is an explicit unproved hypothesis. The target is
an edge, not a proof of finiteness or Collatz. Period multiples alone have equal
endpoints and fail the strict target: the appended odd step is indispensable.
Repeated intermediate states are allowed by the actual predicate; adding a
simple-path or primitive-word condition changes the problem. Infinitely many
lengths at one start suffice because the hypothesis counts pairs, not distinct
starts. No unbounded-start claim is permitted. A closed edge would show that
the finiteness hypothesis carries cycle information already; it would not
supply O.Finite→U.Finite, a bound on even-prefix depth, or new uniform arithmetic.
This is elementary cycle repetition with a new formal graph consequence,
not a claimed novel literature theorem. No filter, new rung, census expansion,
Aristotle submission, or certificate-translation tranche is authorized here.

### Directive history
- 2026-09-13 (post-prefix altitude): reconciled `3a3e838`; closed P_6 and
  retired all finite-prefix relaxations. Selected the missing strict-endpoint
  cycle-exclusion edge O.Finite→NoNontrivialCycle, with the direct U.Finite→Collatz
  corollary. Ranked the even-start bridge second; no proof work started.
- 2026-09-13 (post-obstruction altitude): closed rational M_Q after `882c787`;
  chose exactly Q=2, L=6 prefix-admission boundedness as the next bounded
  architecture question. Ranked the finite-to-one edge second and coarse
  distribution third. No proof work started.
- 2026-09-13 (altitude review): reconciled rung 3, A2, and fixed-b completion;
  ranked all four operator candidates and chose the primitive short-run rational
  positivity obstruction. Exact probes refuted the literal 0.22 run-density bound
  and naive even-prefix normalization. Primary literature demoted cycle transport
  to a known, quantitatively weaker specialization. No proof work started.
- 2026-09-02 (altitude lap): **Retargeted to the odd-block ladder, rung 3.**  Previous objective
  (discharge `rozier_terracol_3_2`) certified complete.  Ranked the operator candidates and chose
  (a); deferred (b) as cross-repo packaging and (c) as off-path mathlib infrastructure.  Landed the
  whole rung-3 engine sorry-free (`FrontA/ThreeBlock.lean`) and **isolated the crux to a finite
  census**: the exact criterion plus the *two-level integer ceiling* leaves 27 tuples at
  `m ∈ {5,8,16,27}` (exhaustive `m ≤ 130`), while the real relaxation alone is provably infinite
  (18 → 258 → 2489 → 18324 tuples at `m = 8, 16, 27, 46`).  Finding: rung 3's finiteness is carried
  by interior integrality, not by a linear form in logarithms — an effectivity asymmetry against
  both rung 2 and Front B's `m`-cycle ladder.
- 2026-09-01 (review lap): **Caught and repaired a fidelity BUG at a headline's base.** The
  `rozier_terracol_3_2` axiom read "unboundedly large paradoxical starts `2^k n`"; machine-checked
  that this implies `NoNontrivialCycle` (open), hence is strictly stronger than Rozier--Terracol
  Thm 3.2. Restated the axiom in its published cardinality form, kept the refutation
  (`noNontrivialCycle_of_unboundedParadoxicalStarts`) and a non-vacuity anchor
  (`infinite_paradoxical_of_tstep_cycle`) in `src/`, and re-derived
  `diverges_imp_infinite_acyclicParadoxical` through an injection. Also pinned
  `acyclicParadoxical_seven_eight` (three odd blocks), proving the two-block exclusion sharp and
  closing the discovery ladder. **Redirected the objective** from the (completed) `sep_two_three`
  campaign to discharging `rozier_terracol_3_2`, decomposed bounded / unbounded orbit.
- 2026-08-24 (review lap): harmonic-dual project certified COMPLETE. Diagnosed
  `OneCircuit` a≥2 as Steiner/Baker (not `omega`) and off critical path; resolved it via
  explicit `SteinerOneCircuit` hypothesis (no new axiom, sorry removed). Set the binding
  objective to the two open fronts, Front B `Compression` first. Created DIRECTION.md +
  STATUS.md.
- 2026-08-24 (review lap, later): **RE-SCOPED.** Established Front B `Compression` is
  Front B restated (no elementary/known upper bound on circuit count) AND source-blocked
  (the needed SdW source was unavailable) → put on hold, forbid more block vocabulary. Redirected the binding
  objective to **Front A M2′** (`ParityRigidityW1' → NoDivergentOrbit`): confirmed mathlib
  has Prokhorov + Portmanteau-on-clopen; isolated the sole gap as a Krylov–Bogolyubov
  module; landed the two pure M2′ endpoints (`exists_freqThreshold_gt`,
  `not_diverges_of_eventually_lt`) and the precise 3-piece decomposition in PENDING_WORK.
- 2026-08-24 (M2′ completion + audit): `parityRigidityW1'_imp_noDivergent` proved with the
  full KB/support/frequency/drift chain and independently rebuilt/audited at the trust base.
  Redirected the live Front-A pull to the parity-reconstruction/carry barrier; see
  `FRONT-A-PARITY-RECONSTRUCTION.md`.
- 2026-08-24 (parity reconstruction completion + post-run audit): landed the exact
  experiment and sorry-free Lean baseline. Corrected the run's overclaim: endpoint spread
  within a suffix class is not a universal finite-state obstruction. Classified the pull
  BASELINE / RE-SCOPE and redirected to `FRONT-A-PARADOXICAL.md`.
- 2026-08-25 (review lap): paradoxical project executed → PROMISING EVIDENCE confirmed. Made
  real crux progress: DECOMPOSED `le_two_blocks_not_acyclicParadoxical` and PROVED Case A
  (both blocks subcritical) sorry-free via two head-block applications + word-split. Isolated
  the residual to one arithmetic core (GOAL2', joint 2-adic/3-adic residue force) shared by
  Cases B/C; wrote the reconstruction route + failed simple bounds into PENDING_WORK. Kept
  the objective on this new-mathematics crux (proving it = GO).
- 2026-08-25 (review lap, 1500): **REFUTED the "elementary A/B route" for the crux `b+d ≤ 5`.**
  Proved (exact-rational witness at `g=41`, `experiments/two_block_relaxation.py`) that the real
  relaxation of `¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` is feasible at unbounded `g`, so NO nlinarith/
  polynomial certificate exists (verified in-Lean: couplings compile, nlinarith fails). The
  integer-truth is Baker-forced. Redirected the MANDATED next move to the sole GO path: build
  effective irrationality of `log₂3` (linear forms in logs) in Lean; forbade all further
  elementary-inequality attempts on `b+d`. Axiom audit re-run: two headline consumption theorems
  clean (trust base + faithful `rozier_terracol_3_2`); two-block exclusion carries the single
  disclosed `sorryAx` (the `b+d≤5` crux).
- 2026-08-25 (review lap, 2100): **Route-decisive source read — crux core reclassified 🟡, target
  sharpened.** Identified `sep_two_three`'s residual as the classical **Gelfond 1935 / Bennett–Bugeaud**
  effective `|2ⁿ−3ᵐ|` bound (polynomial measure ≫ the exponential needed) — 🟡 project-scale, not the
  pessimistic 🟠. Landed sorry-free (trust base) `poly_le_two_pow` + `sep_of_uniform_measure`,
  machine-checking that ONE uniform measure `3^k ≤ (2^m−3^k)·k^C` (large k) + finite check ⇒ the full
  crux. Kept GO on the effective bound; next narrowing = discharge finite check at concrete `C`, then
  build the Padé/Gelfond core. Build 🟢 8752 jobs.
- 2026-08-25 (review lap, this one): **Direction KEPT (GO on effective measure), constants corrected,
  next chip pinned.** Findings landed: the object is **Rhin 1987** (`{1,log2,log3}` measure), honest
  explicit exponent `E=13.3 ⇒ C=15, k≥400`; `C=6` is unprovable from literature (illustrative only);
  Bennett–Bugeaud is off-path. Confirmed leg 1 (`Gelfond.lcmUpto_le`) + full single-kernel leg 2
  (`Legendre.lean`) are trust-base clean; leg 3 (two-*kernel* Rhin determinant) is a real multi-lap
  expedition (transfinite diameter, effective `n(ε)` asymptotics). The run then set a single-log
  denominator/integrality warm-up as its next chip; the public-readiness review later classified
  that work as ancillary. Build 🟢 8754 jobs; crux `sep_two_three` unchanged
  disclosed sorry.

---

## Standing charter (destination)

Prove the Collatz headline `Conjecture ↔ NoDivergentOrbit ∧ NoNontrivialCycle`
(`Conjecture.lean`, `Descent.lean`) by discharging the cited axioms behind each front
into machine-checked proofs, keeping `lake build` green and every headline
`#print axioms`-honest. "Done" = every headline's base is the trust base +
`native_decide` artifacts + genuinely-discharged inputs, with `🔴` open-conjecture
axioms appearing ONLY inside results the mathematics itself states conditionally.

Guardrails (repo-wide): a claim is real only when the kernel accepts it with a clean
`#print axioms`; disclosed `sorry`/cited axioms are honest, faked proofs are not; never
claim a Collatz result stronger than what is actually proved.
