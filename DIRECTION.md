# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

Set by the **2026-09-13 post-obstruction altitude review**, reconciled through
`882c787` (all commits since `5bdea84`). This replaces the earlier same-day
rational-positivity assignment. Historical instructions below are not a queue.
This lap selects direction only; **do not start proof work in this review**.

### Reconciliation: the previous question is ANSWERED

`972c772` corrected the census docstring: minimum observed runs/length is 9/46;
the first front-normalized rung after 3 is 7 at length 27. It added no theorem.
`882c787` answered the directive with an all-parameter counterfamily:

```
X=TF, Y=TTF, v_k=(XY)^k XYY, k≥0;
Q=2, b=2k+3, a=3k+5, m=5k+8;
R=(27/32)^k*(243/256)≤243/256<1;
z_i−2^q_i≥8/5; 5a−3m=1.
```

The maps for XY and XYY preserve [34/5,434/13], including positive slack at
all internal run heads. The invariant-interval argument certifies every k;
5a−3m=1 excludes every proper Boolean-word power. Thus **the proposed rational
M_Q is false already at Q=2**. This is a mathematical proof with an exact
rational certificate, not a Lean theorem or a finite-search extrapolation.
See `SHORT-RUN-OBSTRUCTION-2026-09-13.md` and its handoff. The operator reports
independent host verification; this review also reran the existing certificate.

Every member fails integer admission. Its first six letters TFTTFT require
`81n+119≡0 mod64`, equivalently `n≡57 mod64`, whereas
`N/D≤421/13<57`. In particular `N−D*n0≤−320D/13<0` for its full canonical
start n0. **Do not re-propose the rational bound or rediscover this rejection.**
The missing arithmetic is now exposed: a residue constraint compared to the
head threshold, not integrality of the auxiliary rational fixed point.

The other closed campaigns stay closed:

- Rung 3 (`5a54acc`):
  `FrontA.threeBlock_length_eq_eight_of_acyclicParadoxical` classifies the
  front-normalized three-run segments. Its proof uses polynomial separation;
  the old claim that interior integrality alone closes it is superseded.
- A2 (`c3aba74`): exact excursion slack and strict/equality criteria, with
  the indispensable descent numerator. The 2305/2313 controls have prefix
  remainders 7207/1375 and opposite admission. The null-model asymptotic is
  proved mathematically for that artificial model, not for the actual census.
- Fixed-b Campaign B (`4a12a68`):
  `FrontA.acyclicParadoxical_length_lt_of_oddRunCount` proves
  `m<4*((2^b−1)*(b+53342))^2+b` for odd-start segments with at most b maximal
  odd runs, including a final odd run. The composition uses the standard
  trust triple; the length result inherits eleven disclosed native certificates.

The recorded complete census covers 2≤m≤80, with nonempty rows 8/27/46/65/73,
counts 4/19/101/155/41, and minimum runs 3/7/9/13/17. The literal 0.22*m run
lower bound is refuted by 1807@46 (9 runs) and 1127@65 (13 runs). Only trunks
at m≥27 are all on the trajectory of 27. This review does not repeat the full
census or strengthen its finite scope.

### Live graph and actual open obligations

`FiniteAcyclicParadoxical` (`Assumed/Paradoxical.lean`) means finiteness of
**all pairs (n,m)** satisfying `AcyclicParadoxical`, with no odd-start condition.
That predicate (`FrontA/Paradoxical.lean`) means n>2, m>0, 3^a<2^m and strict
endpoint growth under the shortcut map; repeated intermediate states are allowed.
`finite_acyclicParadoxical_imp_noDivergent` is proved with the standard trust
triple. `conjecture_iff_split` still needs the separate open `NoNontrivialCycle`.
Neither finiteness node nor either Collatz front has been discharged here.

Let O denote the set of odd-start acyclic paradoxical pairs. Campaign B proves
a bound for each prescribed b, not O.Finite. A global length bound on O is
O.Finite in another form: bounded lengths give finitely many words, each with
finitely many starts by D*n<N; a finite set has bounded lengths. With Campaign
B, a global run bound is equivalent as well. None may be assumed as an input.
The edge O.Finite → FiniteAcyclicParadoxical remains unproved. Deleting an even
prefix does not supply it: 18→20 in 8 steps is subcritical (243<256), but its
odd-start suffix 9→20 in 7 steps is supercritical (243>128).

### Ranking by probability × magnitude of NEW mathematics

These are subjective ordinal judgments for one bounded attack, not measured
probabilities or claims of literature novelty. A port, renamed target, or finite
rerun has little new-mathematics value even if easy to finish.

| Rank | Candidate | Probability × magnitude | Decision |
|---|---|---|---|
| **1** | **(i) Six-letter admission after the Q=2 rational obstruction** | Medium-high for a certified family or a smaller arithmetic obstruction × high diagnostic value for uniform admission arguments | **CHOSEN**, with the exact population/filter below. Adding arithmetic tests the missing mechanism; no full finiteness result is promised. |
| 2 | (ii) Odd-start finiteness → unrestricted finiteness | Medium × high formal-edge value, moderate new mechanism | Deferred. A finite-to-one reduction needs a specified map or relation to O, finite exceptional cases, and finite fibers including even-prefix depth. The 18@8 counterexample kills only the naive map, not the implication. |
| 3 | (iii) Coarse residue-given-numerator law | Low-medium for a useful uniform error bound × potentially high arithmetic value | Deferred. Exact conditioning is deterministic; a coarse discrepancy theorem needs a population, threshold and useful error scale. Those are not supplied by the A2 null law. |
| 4 | (iv) Formalize the closed interval certificate or transport to fixed-circuit Front B | High × low new mathematical content | Deferred. Kernel translation of a known certificate is valuable later; fixed-circuit finiteness is already the known Simons–de Weger mechanism, not a new uniform result. Reconciliation reveals no better on-path candidate. |

The earlier review's source-availability correction remains in force: the
Simons–de Weger source is available, and the old source-blocked entries are
historical. Its theorem identification and quantitative comparison remain in
`HANDOFF-2026-09-13-altitude-direction.md` and the repository's paper ledger.
No new literature search or novelty claim is part of this lap.

For candidate (iii), a concrete comparison would use **all Boolean words** W(m,a)
starting T, of length m with exactly a odd letters and D=2^m−3^a>0, each counted
once; not just admitting words or the orbit census. Coarse bins may be fixed as
`W_j={v∈W(m,a): 2^(-j-1)<N(v)/(D*2^m)≤2^(-j)}`, j≥0, with a separate overflow
bin for N/(D*2^m)>1. Compare `Σ_(v∈W_j) 1[D*n0(v)<N(v)]` with
`Σ_(v∈W_j) p_odd(N(v))`, where p_odd counts uniform starts in
{3,5,…,2^m+1} below the **strict** threshold N(v)/D, divided by 2^(m−1).
A new error bound must control these actual sums. At exact (m,a,N),
`r(v)=−N*(3^a)^(-1) mod2^m` is already a point mass. No independence or
model-to-census transfer is assumed; retain the 2305/2313 controls.

### ONE BOUNDED OBJECTIVE — decide the Q=2, L=6 prefix-admission relaxation

Fix **Q=2 and L=6 once and for all**. Let S2 consist of Boolean words

```
v=T^q_0 F^e_0 ... T^q_(b−1) F^e_(b−1), b≥1, q_i,e_i∈{1,2}, m=|v|≥6,
Primitive(v) in FrontB.Powers (not a proper word power),
R=3^(sum q_i)/2^m<1,
z_(i+1)=3^q_i/2^(q_i+e_i)*z_i+1−2^(-e_i),
z_b=z_0 and z_i>2^q_i at every run head.
```

All gaps, including the terminal gap, are positive. Use the unique rational
affine fixed cycle; z0=1+N(v)/D(v), with N=`numer`, D=2^m−3^a>0.
No uniform bound on b, m or N/D is part of this population. Neither the
old family's uniform slack nor its gap from R=1 is required of new words.

For u=take L v, a_L=ones(u), N_L=numer(u), define

```
r_L(v) = [−N_L*(3^a_L)^(-1)] mod2^L, in {0,…,2^L−1};
c_L(v) = min {n∈ℕ : n>2 and n≡r_L(v) mod2^L};
P_L(v) : D(v)*c_L(v)<N(v).
```

The inverse exists since 3^a_L is odd. Thus P_6 tests existence of a start
above 2 in the **first-six-letter residue class** below the **full-word**
threshold N(v)/D(v). This tests the given entry head only, not all rotations
or every sliding window. Equality is rejection. It is necessary for actual
admission; it does not require that c_6 realizes the remaining m−6 letters.
Full admission is `D(v)*c_m(v)<N(v)`, a separate computation throughout.

**Question to decide, not to assume:**

```
Does there exist M such that ∀v∈S2, P_6(v) → |v|≤M?
```

This single fixed-filter question is the campaign. Do not silently change Q,
increase L, demand survival for every finite L, or switch to full admission.
The previous family belongs to S2 but fails P_6 for every k, so it does not
answer this question.

**First attack (next lap only).** Reuse `experiments/block_composition.py` and
`experiments/short_run_obstruction.py`. First check cyclic run-head rotations
and bounded prefix/defect changes of the existing family as baseline controls:
track how both c_6 and N/D change; do not infer integer admissibility from
rational rotation. Then search two short block macros with q,e∈{1,2} and a
common invariant interval whose primitive repeated/defect words have a fixed
six-letter prefix with c_6 strictly below their full-word fixed-point threshold.
Use a bounded macro search (at most four (q,e) blocks per macro initially),
exact rational arithmetic and all internal-head inequalities. Output N,D,c_6,
c_m, both admission margins, b,a,m and the primitivity witness separately.
No new experiment or construction search is authorized during this review.

**Acceptance criterion.** Finish with one of:

- An explicit unbounded primitive family in S2 satisfying P_6, with an all-k
  recurrence/invariant or exact formula certifying the strict filter margin.
  State any finite exceptional k and the unbounded surviving tail. This is
  an exact probe refutation of the displayed M statement; finite survivors
  alone do not suffice. Compute full-admission margins independently and
  distinguish finite checks from any universal claim about them.
- A proved explicit M (or cutoff m0 and the uniform inequality
  `D(v)*c_6(v)≥N(v)` for every v∈S2 with m≥m0), with its finite remainder
  justified. The proof must cover arbitrary b, not only the searched macros.
  This would be a new arithmetic exclusion node; Lean-check it before
  declaring a green theorem.

A green intermediate node or edge must prove an actual needed arithmetic
inequality, not merely encode the predicate. Failure of the bounded macro
search is an honest checkpoint with failed inequalities and a next on-path
attack, not proof of M and not a stuck condition. Do not fund a multi-lap
implementation tranche on finite-search failure alone.

**Costume check.** This is a six-bit necessary-filter relaxation, not the full
canonical indicator disguised as a new lemma. A surviving family refutes only
this relaxation's bounded-length claim; it need not admit a single integer
segment and does not refute restricted finiteness or Collatz. A rotation or
padding of the known family must be identified as such: new content would be
the all-parameter prefix-margin certificate, not another positivity family.
If that control already settles the exact question, stop; do not inflate its
novelty or escalate L to manufacture another campaign.

Conversely, a bound for S2∩P_6 would imply finiteness of the **actually admitting
words in this same primitive, Q=2, terminal-even population** (each bounded
word has finitely many starts below N/D). It would not establish finiteness
for all odd-start segments: other run lengths, proper powers and terminal-odd
words still need justification. Neither outcome supplies the even-start edge.
No run/length bound on all admitting words may be smuggled in as a hypothesis.
No literature-novelty claim is made by this direction selection.

**Excluded drift:** no rung 4/5 classification, fixed-b reruns, constant or
irrationality-exponent sharpening, global run/length bounds as inputs,
Front B vocabulary/transport campaign, package extraction, entropy build,
native-certificate cleanup, or the discredited unbounded-paradoxical-starts
axiom. Only a later altitude lap may replace this objective. This review stops
after the green committed directive and handoff.

### Directive history
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
