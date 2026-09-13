# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

Set by the **2026-09-13 altitude review**, reconciled through `9ae73a3`.
This replaces the 2026-09-02 directive. The historical instructions below are
not a work queue. This review changes direction only; no proof work was started.

### Closed campaigns — do not reopen

- **Rung 3 COMPLETE (`5a54acc`).**
  `FrontA.threeBlock_length_eq_eight_of_acyclicParadoxical`
  (`FrontA/ThreeBlock.lean`) classifies front-normalized three-run segments:
  length exactly 8. The exceptional lengths and the long tail are both closed.
  The final proof consumes the polynomial separation measure; the old account
  claiming finiteness from interior integrality without logarithmic separation
  is superseded by the source audit in `BLOCK-COMPOSITION-2026-09-13.md` §2.
- **Campaign A2 COMPLETE (`c3aba74`).** Exact trunk slack and strict/equality
  criteria are in `FrontA/Excursion.lean`. The 2305/2313 control refutes omission
  of the descent numerator. `EXCURSION-AUDIT-2026-09-13.md` proves the null-model
  law mathematically with exact controls; it is not a Lean asymptotics theorem
  and not a law for the actual census. No excursion-rate obligation remains
  from that assignment.
- **Campaign B COMPLETE (`4a12a68`, following `529ccef`).**
  `FrontA.acyclicParadoxical_length_lt_of_oddRunCount` proves
  `m < L(b) = 4*((2^b-1)*(b+53342))^2+b` for every odd-start acyclic paradoxical
  segment with at most b maximal odd runs. The rational envelope, small vertex,
  squaring, numerical feedback, and word bridge are all proved. The composition
  uses the standard trust triple; the length theorem additionally inherits
  eleven disclosed native certificates. It is **not** bare-trust-base-only.
  The factor-2 proposal and missing-bridge language in lap-1 notes are obsolete.

### What still reaches the headline

`FiniteAcyclicParadoxical` in `Assumed/Paradoxical.lean` quantifies **all**
(start, length) pairs, not only odd starts. Its proved implication to
`NoDivergentOrbit` is trust-base clean; `conjecture_iff_split` additionally needs
`NoNontrivialCycle`. Both fronts remain open. Global paradoxical finiteness is
stronger than convergence, not an established easier reformulation of Front A.

The campaign proved `∀ b, ∀ odd-start segments with runs ≤ b, m < L(b)`.
It did not prove `∃ M, ∀ odd-start segments, m < M`. The latter is the restricted
finiteness target itself (bounded lengths give finitely many words and starts
via `D*n<N`; a finite set has bounded lengths). Using Campaign B, a global bound
on run count is also that restricted target in another form. Neither statement
may be imported as a lemma. Passing to the unrestricted node still needs an edge.
`AcyclicParadoxical` means strict endpoint growth, not absence of repeated states.

### Census reconciliation — finite evidence, with two corrected claims

The recorded complete start census (`9b5dc54`, instrument
`experiments/paradoxical_orbit_census.py`) covers **2 ≤ m ≤ 80**, every subcritical
odd count, and every odd start through its analytic bound X(m). Nonempty lengths
are exactly 8, 27, 46, 65, 73, with respectively 4, 19, 101, 155, 41 starts and
minimum run counts 3, 7, 9, 13, 17. All trunks **at m ≥ 27** lie on the trajectory
of 27; do not extend that wording to the length-8 trunks 7 and 11. The extra word
censuses through `9ae73a3` corroborate empty fixed-four-run slices; they do not
open rung 4 or 5 as objectives.

**The literal bound `runs ≥ 0.22*m` is false.** Exact review controls give
`1807 -> 1822` at (m,a,b)=(46,29,9), and `1127 -> 1154` at (65,41,13):
`50*9 < 11*46` and `50*13 < 11*65`. The minimum observed ratio is 9/46.
The old “rung 6 first appears at 27” sentence in `block_ladder_rung_census.py`
also conflicts with its newer complete-census paragraph: the minimum is 7.
These are probe refutations/corrections, not new all-length bounds. Many runs
and small **average** run lengths describe the table; no uniform bound on the
largest run follows. This lap repeated complete lengths 8 and 27 and all five
nonempty rows through start 5000, not the full 2..80 completeness scan.

### Candidate ranking: probability × magnitude of NEW mathematics

These are subjective ordinal estimates for a bounded next campaign, not measured
success rates. A likely port of a known theorem has little novelty value.

| rank | candidate | probability of useful new result × magnitude | decision |
|---|---|---|---|
| **1** | **(3) Many short runs: expose the limit of rational positivity** | medium-high × high route value for an exact obstruction/refutation; low probability of global finiteness | **CHOSEN**, narrowly scoped below. It tests what information must replace the present `2^b-1` feedback, rather than tuning that exponent. |
| 2 | (4) Numerator/residue transfer | medium × potentially high, but no quantitative law specified yet | Deferred. Conditional on exact N at fixed (m,a), the canonical residue is already determined. The open question is arithmetic distribution across a specified coarse population and admission threshold, not recovering an unknown independent conditional residue. |
| 3 | (2) Odd-start finiteness → unrestricted finiteness | medium × moderate edge value, little new mechanism by itself | Deferred, genuinely unproved. Deleting an even prefix need not preserve subcriticality; see the exact obstruction below. A finite-to-one reduction would be a useful green edge, but does not discharge either finiteness node. |
| 4 | (1) Transport composition to Front B integer cycles | high probability of a port × low new mathematical content | Deferred as known fixed-circuit finiteness with weaker quantitative bounds. Equality and cyclic-run bookkeeping need an explicit bridge, not a new research campaign. |

**Literature costume check for (1).** The source is available: the old
“Simons–de Weger source-blocked” explanation is obsolete. The ledger
`papers/simons-deweger-2010-m-cycles-summary.md` and
`ON-LINE-FINDINGS-2026-08-24-simons-deweger-m-cycles.md` identify Theorem 3(a)
as fixed-circuit finiteness. Re-read primary v1.44 (2010), §1.4, Lemmas 6–7,
12–14: it chains minima with exponent `rho=log(3)/log(2)` and combines that with
a two-log lower bound. Its asymptotic odd-count ceiling is of order
`b*rho^b`, compared with our coarse length ceiling of order `4^b*(b+53342)^2`.
This is a comparison of bound strength, not a formal implication between APIs.
The source credits Steiner with one-circuit **exclusion**; a transported length
bound alone is weaker and does not discharge `SteinerOneCircuit`.
[Primary paper](https://deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.44%5B2010%5D.pdf).
The transport would be a new formal edge for a known mechanism, not a new cycle
finiteness theorem. Neither fixed-circuit finiteness nor arbitrary bounded
circuit count establishes `LadderCompletes` or `Compression`.

**Exact boundary for (2).** `18 -> 20` in 8 steps is acyclic paradoxical, with
five odd steps: `243<256`. Deleting its first halving gives `9 -> 20` in 7 steps,
whose multiplier is `243/128>1`. Thus the naive normalization map is refuted;
this does not refute the finiteness implication. Any future bridge must supply
another subcritical window and control the fibers, including even-prefix depth.

**Exact boundary for (4).** From the iterate identity,
`r(v) = (-N(v)*(3^a)^(-1)) mod 2^m`; see `realizing_residue_affine` in
`experiments/paradoxical.py` and the residue dictionary in
`FrontA/ParityReconstruction.lean`. The law of r given exact N is a point mass.
For subcritical odd words let n0 be the least representative above 2. Admission is precisely
`D*n0<N`. A coarse-bin discrepancy or residue-threshold counting statement would
be new; rewriting this exact indicator or fitting observed/model ratios is not.
The 2305/2313 prefix remainders remain compulsory controls.

### ONE OBJECTIVE — primitive short-run obstruction to the positivity relaxation

Decide whether **bounded individual runs plus positivity of the rational cycle**
can force bounded total length, even after word powers are removed. The proposed
statement to attack (not assume) is:

```
For every Q ≥ 1 there is M_Q such that every primitive word
v = T^q_0 F^e_0 ... T^q_(b-1) F^e_(b-1),  1 ≤ q_i,e_i ≤ Q,
whose rational affine cycle satisfies
z_(i+1) = (3^q_i / 2^(q_i+e_i))*z_i + 1 - 2^(-e_i),
z_b = z_0,  z_i > 2^q_i,  R = 3^(sum q_i)/2^|v| < 1,
has |v| ≤ M_Q.
```

Use the existing `FrontB.Primitive` meaning (not a proper word power).
All even gaps are positive here so cyclic and finite run counts coincide.
This is a **test of the current proof's relaxation**, not a new Collatz axiom.
Strict positivity prevents the repeated trivial `TF` cycle from being a fake
counterexample. Primitivity prevents simply replaying the known `wpow` degeneracy.

**First attack (one bounded architecture/probe lap).** Reuse exact rational
composition in `experiments/block_composition.py`. Find a short rational cycle
with strict slack at every joint, then try a bounded defect in a repeated block
pattern, or two block patterns preserving a common rational interval. Track
q, e, b, a, m, R, every z_i, and the minimum slack exactly. Search for a fixed Q
and an arbitrarily long **primitive** family; a finite list of survivors is not
a refutation of an unspecified M_Q. A recurrence/invariant-interval certificate
for the family would refute the proposed statement. Uniform positive slack or
R bounded away from 1 would strengthen the diagnosis, but are not requirements.
No such family is asserted by this review; construction is the next attack.

For each finite probe compute its canonical n0 and `N-D*n0` separately; keep
rational-envelope survivors distinct from actual admissions. Preserve all 320
census controls and the shared-trunk pair. If a family survives, identify exactly
which integer head congruences or final residue test reject its nonadmitting members; carry that input
forward as the missing arithmetic, rather than another real growth bound.

**Costume check and acceptance.** A family of rational cycles does not refute
Collatz or paradoxical finiteness. It would refute bounded-length arguments based
only on these rational hypotheses, even with short runs and no proper powers.
It would not prove `2^b-1` optimal or rule out all improvements to it. Conversely,
asserting bounded length/run count for all actual admitting words just renames
the restricted finiteness target; an unbounded excursion law can also exclude
nontrivial cycles. State the quantifiers before celebrating a new node.

Success is a green node, a green edge, or an exact probe refutation with its
scope pinned. Do not measure progress by sorry count. If the family search fails,
record the precise failed construction and remaining arithmetic test; do not
promote finite search failure to the proposed universal bound. No multi-lap
implementation tranche without a new inequality, family, or smaller obstruction.

**Excluded drift:** no rung 4/5 classification, fixed-b rerun, constant or
irrationality-exponent sharpening, shared-package extraction, entropy build,
Front B vocabulary campaign, or native-certificate cleanup. The old unbounded-
paradoxical-starts axiom remains forbidden. Only a later altitude lap may replace
this objective. Stop this review after the committed direction and handoff.

### Directive history
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
