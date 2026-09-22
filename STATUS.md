# STATUS — collatz-moonshot 📊
**Machine-checked conjecture graph for Collatz: two fronts, every edge axiom-audited.** ·
**Build**: 🟢 FORMALIZE-tier green (8771 jobs; inherited native certificates disclosed) · **Updated**: 2026-09-22 (mechanism search: goal audit, single-congruence lemma, 5n+1 control; awaiting a new idea).

> **2026-09-22 — mechanism search (Fable), no lap.**  The run-count node `r ≥ εK` does not
> imply CST; `StoppingCorrect ⟺ N_ε ∧ C_ε` (a tautology), and the complement `C_ε` (no survivor
> with `≥ εK` runs) holds the cycles whose crossing prefix has that many runs, a sub-problem
> of many-circuit cycles with no known mechanism.  Run-to-run admission carries exactly one
> congruence, so amortised run bookkeeping is closed.  New control: `5n+1` has first-crossing
> survivors `13, 17` and `5` (274 steps, 118 odd, 39 runs, `E = 8`), refuting any mechanism
> valid for all odd multipliers.  Two candidates retired with named failure steps.  Lean:
> `at_primitive`, `overshoot_modEq` (`FrontA/FirstCrossingResidue.lean`, base three axioms).
> Read `RESEARCH-2026-09-22-mechanism-search.md`.

> **CURRENT — whole-board reflection complete; no bounded objective selected.**
> Reconciled baseline `5a54acc` through `6a33554`, all 17 intervening commits,
> the route maps, thread definitions, and primary RT/Simons–de Weger/Tao sources.
> **Nothing currently clears the probability × magnitude of NEW mathematics bar.**
> `DIRECTION.md` now states the full-admission obstruction and ranks the whole
> board without converting deferred ideas into a proof queue. Fixed-b finiteness
> is the Simons–de Weger mechanism extended to strict segments; it supplies no
> uniform run bound. U.Finite implies full Collatz; O.Finite already excludes
> cycles. Neither finiteness input nor the O→U edge is proved.
> Source audit also catches `CountingGivesFinite` counting all words, so word
> powers make it equivalent to FrontB; its finiteness-versus-emptiness comment
> requires a different, primitive population. `LadderCompletes` likewise
> quantifies over all bounds. These are documented deductions, not new Lean proofs.
> The standing state is **awaiting a new idea**, not an operator-blocked claim.
> No proof work started. Read `HANDOFF-2026-09-13-whole-board-reflection.md` for
> exact verification and the gate parser caveat. All older assignments below
> are historical and subordinate to the CURRENT DIRECTIVE.

> **Historical completion — cycle-exclusion edge PROVED (trust-base clean).**
> `Assumed/Paradoxical.lean` now carries the infinite-witness node
> `infinite_acyclicParadoxical_of_odd_tstep_cycle` (odd periodic n>2 ⇒ the set of
> lengths m with `AcyclicParadoxical n m` is infinite, witnesses `L(3·3^a+j)+1`),
> the named hypothesis `FiniteOddAcyclicParadoxical` (O.Finite), the edge
> `finite_odd_acyclicParadoxical_imp_noNontrivialCycle : O.Finite → NoNontrivialCycle`,
> and the corollary `finite_acyclicParadoxical_imp_conjecture : U.Finite → Conjecture`.
> `#print axioms` for all three = `propext, Classical.choice, Quot.sound`; no
> CST/cycle axiom, no sorry, no new native certificate. Gate green, 8771 jobs.
> The dictionary's related-member case and the trivial 1↔2 shortcut cycle are
> discharged explicitly. O.Finite, U.Finite, and O.Finite→U.Finite remain open;
> U.Finite is now a machine-checked sufficient condition for full Collatz, not
> identified with the paper's numerical 4614 conjecture.
> Operator context strengthens the previous finite full-rejection observations:
> every padded-family member fails full admission, independently host-verified,
> with n0 of about m bits. The repository script still certifies full rejection
> only at its 36 probe values; this review does not add the host's universal proof.
> **Verification:** existing prefix certificate PASS; real full 8771-job gate
> and existing six-declaration axiom audit FORMALIZE-TIER GREEN. No new trust debt.
> Read `DIRECTION.md` and `HANDOFF-2026-09-13-cycle-edge-direction.md`.

> **Historical completion, 2026-09-13 — Q=2, L=6 boundedness refuted.**
> With X=TF and Y=TTF, `(XY)^(2j+12) X Y^17`, j>=0, is primitive and in S2,
> has unbounded length m=10j+113, and passes P_6 for every j. Its fixed-cycle
> interval [34/5,225] certifies every head slack >=8/5; odd a,m and
> 5a-3m=16 prove primitivity. The common six-letter prefix still gives c_6=57,
> but now N/D>66 and an exact positive-coefficient formula proves N-57D>0.
> This pads the known family by 15 Y blocks; the new content is the all-j
> prefix-margin certificate, not a new positivity construction.
> **Proof level:** mathematical all-parameter proof with an exact rational
> certificate, not a new Lean theorem. Full admission is checked separately;
> all 36 sampled full margins are negative, with no universal claim about them.
> **Verification:** new certificate and 36 probes PASS; original certificate,
> 320 census controls and 2305/2313 pair PASS; full 8771-job gate and existing
> six-declaration axiom audit FORMALIZE-TIER GREEN. No new trust debt.
> Read `HANDOFF-2026-09-13-prefix-admission-obstruction.md` and
> `PREFIX-ADMISSION-OBSTRUCTION-2026-09-13.md`. Return to altitude; do not
> increase L or start a full-admission campaign. Both Collatz fronts remain open.

> **Historical, 2026-09-13 — altitude complete; Q=2, L=6 admission directive committed.**
> Reconciled both commits since `5bdea84` through `882c787`. The rational M_Q
> question is closed: the interval-certified primitive family is unbounded,
> and every member fails the six-letter threshold test. DIRECTION now chooses
> exactly one new bounded question: can primitive Q=2 rational cycles pass
> **D*c_6<N** at unbounded length, where c_6 is the least start above 2 for
> the first six letters and N/D is the full-word threshold?
> First attack: baseline rotations/defects, then short invariant-interval macros.
> Acceptance and costume checks require an all-parameter refutation or a proved
> bound for the full specified population; full admission remains separate.
> The odd-start→unrestricted edge ranks second; coarse residue discrepancy third.
> **No proof work started.** Both Collatz fronts and arithmetic admission remain open.
> **Verification:** existing exact short-run certificate PASS; full 8771-job gate
> and six-declaration axiom audit FORMALIZE-TIER GREEN; diff whitespace check clean.
> Read `HANDOFF-2026-09-13-prefix-admission-direction.md`. Older entries are history.

> **Historical completion, 2026-09-13 — primitive short-run rational bound refuted.**
> For X=TF, Y=T²F, `(XY)^k XYY` is an unbounded primitive family with Q=2,
> joint slack ≥8/5 and R≤243/256. The invariant interval [34/5,434/13]
> certifies every k; 5a−3m=1 excludes all proper Boolean-word powers.
> This is an all-k mathematical proof with an exact rational certificate,
> not a new Lean theorem or an extrapolation from finite survivors.
> All family members fail admission: the common TFTTFT prefix forces
> n0≡57 mod 64, but N/D≤421/13. N and canonical n0 are tracked separately.
> **Verification:** 36 exact cycles through k=256, original 320 census controls,
> 2305/2313 prefix-remainder pair, and full 8771-job FORMALIZE gate with the
> existing six-declaration axiom audit. No proof or build configuration changed.
> The previous rational-positivity directive was completed; no stretch campaign started.
> Read `HANDOFF-2026-09-13-short-run-obstruction.md`; the general arithmetic
> admission problem and both Collatz fronts remain open.

> **Historical, 2026-09-13 — altitude review complete; next objective selected.**
> Rung 3 (`5a54acc`), A2 (`c3aba74`), and fixed-b Campaign B (`4a12a68`) are
> closed. `DIRECTION.md` now selects **one bounded probe of primitive short-run
> rational cycles**: decide whether their strict positivity can coexist with
> unbounded length, exposing the integer information a uniform argument needs.
> No family or new Lean theorem is claimed yet. Cycle transport is a known,
> quantitatively weaker specialization; its old source-availability blocker is
> obsolete. Odd-start finiteness still lacks a bridge to the unrestricted node.
> Exact review probes refute `runs ≥ 0.22*m` (9@46 and 13@65) and naive deletion
> of an even prefix (18@8 is subcritical; its 9@7 suffix is not). The exact
> numerator already determines the canonical residue at fixed length/odd count.
> **Verification:** full 8771-job FORMALIZE gate and Campaign B axiom audit green;
> A2 exact controls and independent review probes pass. No proof edits.
> Read `HANDOFF-2026-09-13-altitude-direction.md`. Older assignments below are
> historical; the CURRENT DIRECTIVE is authoritative.

> **2026-09-13 — Campaign B complete.**
> `FrontA.acyclicParadoxical_length_lt_of_oddRunCount` proves the explicit
> bound `L(b)=4*((2^b-1)*(b+53342))^2+b` for every odd-start acyclic
> paradoxical segment with at most b maximal odd runs. The composition,
> rational envelope, numerical feedback, word decomposition, and monotonicity
> are all kernel-checked. A Bernoulli small-vertex argument replaces the
> maximum-product construction. No new arithmetic obligation remains.
> The final length theorem inherits eleven existing Rhin-lite native certificates;
> the composition theorem itself uses the standard trust triple.
> See `HANDOFF-2026-09-13-fixed-block-bound.md`; the assigned campaign stops here.

> **Historical lap 1 — Campaign B running+advancing.** The arbitrary-block integer
> cascade now has a kernel-checked extraction and composition rule. A cyclic
> maximum-product potential yields the proposed uniform inequality
> `2^a<(b/δ)^(2^b-1)` and `m<2a+b`; its local growth, unit cut and arbitrary-length
> mass induction are kernel-checked in `FrontA/BlockComposition.lean`.
> `BLOCK-COMPOSITION-2026-09-13.md` gives the mathematical word-to-potential
> derivation and an explicit proposed `L(b)=2*((2^b-1)*(b+53342))^2+b` using the
> existing polynomial separation. **The complete segment bound remains to be
> formalized**, chiefly the finite cyclic-product construction and word bridge.
> Exact b=4,5 probes include every rational-positivity survivor at lengths 16,
> 27 and 46; no survivor violates the mechanism. Prefix remainders remain in
> the exact criterion. Next: Campaign B architecture lap 2, not A2 or rung 3.

> **2026-09-13 — Campaign A2 settled.** `FrontA/Excursion.lean` proves the trunk slack
> identity and exact strict/equality criteria; the kernel-checked 2305/2313 witness refutes
> admission from the climb, depth and odd count alone. The prefix remainder is indispensable.
> The `(91,46)` control has a one-step suffix climb `61→92`. The exact probe reproduces all
> 320 A1 table starts through start 5000, including every trunk count, without claiming to
> repeat A1's full completeness scan. `EXCURSION-AUDIT-2026-09-13.md` proves the model law
> `2δR→1`, records the residue/numerator dependence preventing a census prediction, and
> classifies every candidate excursion node. Its surviving bound `C_trunk>2δn/a` needs a
> new start-length input for polynomial/exponential growth in m. The next campaign is B's
> arbitrary-block composition architecture; A2 and rung 3 are complete.


> **2026-09-08 — rung-3 front-normalized classification CLOSED.**
> The parameterized exponent algebra now proves the sharp feedback bound `k ≤ 6t+5` using
> `3^5 ≤ 2^8`.  The Rhin-lite polynomial measure bootstraps the near-critical window to
> `k < 492276`; a new convergent bracket gives deficit scale `t=26` and hence `k ≤ 161`; a
> kernel-checked aggregate table improves this to `t=8`, hence `k ≤ 53` and `m ≤ 106`.
> One pruned native certificate, with `(k,m)` outermost and `f,g` derived from the totals, covers
> both the old `m ≤ 27` node and the contracted window.  Consequently
> `threeBlock_window_infeasible`, `threeBlock_leaves_infeasible`, `threeBlock_gap_of_long`, and
> `threeBlock_not_acyclicParadoxical_of_long` are all proved, and the proof-debt gate reports
> **0 sorries**.  An adversarial statement review then caught the remaining gap between that
> theorem (length outside `{5,8,16,27}` is impossible) and the advertised literal length-8
> classification.  The new `threeBlock_not_acyclicParadoxical_of_exceptional` rejects the ten
> ceiling-passing tuples at lengths `5,16,27` via nested cascade ceilings, exact parity-trace
> residues, and one `decide +kernel` certificate.  Therefore
> `threeBlock_length_eq_eight_of_acyclicParadoxical` proves the full front-normalized theorem.
> Full build: 8766 jobs green.  Trust note: the next bracket's 5-million-digit
> upper power comparison exceeds Lean's kernel numeral cap and uses `native_decide`; the unified
> residual census is also native, and both are explicit in `scripts/AxiomAudit.lean`.  The new
> exceptional-tail theorem itself prints only `propext`, `Classical.choice`, and `Quot.sound`.


> **2026-09-02 (historical) — the odd-block ladder reaches RUNG 3, and its crux is a finite census.**
> New module `FrontA/ThreeBlock.lean`.  Rung 3 asks for a *classification*, not an exclusion:
> **every acyclic paradoxical segment with three odd blocks has length 8** (four realized words,
> all `m = 8`).  Landed sorry-free: the **block-merge reduction** (rung 2 reused as a black box on
> both two-block sub-segments — `threeBlock_merge_reduction`), the exact criterion
> `threeBlock_criterion` (`n < y ⟺ D·w₁ ≤ 3^f·T − 2^(c+d+e+f)`), the slack identity
> `threeBlock_slack`, the 2-adic `threeBlock_cascade`, and the word→identities bridge.  **Finding:**
> the *real* relaxation implied by `w₃ ≥ 1` is infinite (18/317/2931 tuples at `m = 8/16/27`,
> 88718 for `m ≤ 40`), but keeping the *interior* scale `w₂` an integer collapses the whole rung to
> **27 tuples at `m ∈ {5,8,16,27}`** (exhaustive `m ≤ 130`).  So rung 3's finiteness is carried by a
> two-level integer ceiling, not by a linear form in logarithms — an effectivity asymmetry against
> rung 2 (which needs Baker via `sep_two_three`) and against Front B's `m`-cycle ladder.  The single
> `src/` sorry is that census, and it is sharply narrowed: **three positivity leaves are PROVED
> sorry-free** — `threeBlock_gap_of_real` (`w₃ ≥ 1`), `threeBlock_gap_of_w2` (`w₂ ≥ 1`) and
> `threeBlock_gap_of_w1` (`w₁ ≥ 1`), all instances of `threeBlock_gap_of_scaled_lower`.  Tuples
> failing all three number **58**, at the same four lengths, exhaustive for `m ≤ 80` — so the
> finiteness needs only the maximum of three cascade-level positivity bounds, with **no rounding
> at all**.  The disclosed node `threeBlock_ceiling_gap` is exactly that residual.


> **2026-09-01 — the last `src/` sorry of the RT campaign is PROVED; `finite_acyclicParadoxical_imp_noDivergent`
> is TRUST-BASE CLEAN.**  `FrontA.two_pow_approx_three_pow_from_above` (powers of two approximate
> powers of three from above to relative precision `1/N`, with `A > M`) is proved by a
> multiplicative pigeonhole (`exists_mul_box`, `exists_two_pow_three_pow_ratio_close`) plus a
> side-fixing flip (`approx_from_above_of_ratio_close`) — no logarithms, no irrationality of
> `log₂3`, no `native_decide`.  Consequently `Assumed.rozier_terracol_3_2` (RT 2026 Thm 3.2) and
> the Front-A closer `finite_acyclicParadoxical_imp_noDivergent` both print
> `[propext, Classical.choice, Quot.sound]`.  `check-proof-debt.sh` → **0 sorries**.  The
> `DIRECTION.md` objective set by the 2026-09-01 review lap is complete.

> **2026-09-01 — Rhin 1987 axiom RETIRED.**  `sep_two_three` is now proved from the Rhin-lite
> measure with **no literature axiom** (`FrontA/RhinLiteSep.lean`, `sep_two_three_rhinLite`;
> ledger = `propext/Classical.choice/Quot.sound` + the Rhin-lite tower's `native_decide`
> certificates).  The direct re-wiring of the existential `rhinLiteLIMeasure` was **refuted**
> (its constant is opaque: `N₀` from an `isLittleO`); instead the constants were made explicit —
> `lcmUpto(2000t) ≤ (22/5)^(2000t)` for all `t ≥ 1` (eight kernel block certificates + Chebyshev
> for `N ≥ 62000`), `κ = 436`, `c = 1/(2·(396/5)^6000·6^436)` — giving crossover `K = 141000`,
> with `450 ≤ k < 141000` closed by five consecutive-convergent brackets of `log₂3` (eight
> `decide +kernel` power certificates, largest `2^478245 < 3^301739`).  `Assumed/Rhin1987.lean`
> and the old `κ = 14` route are parked in `wip/`.  `src/` remains sorry-free.

> **2026-08-26 (Lane 1):** Furstenberg's topological ×p×q rigidity (1967) is now **proved,
> axiom-clean** in `Rigidity/Furstenberg.lean` — the `Assumed/Furstenberg.lean` axiom is
> discharged, and the ⟨p,q⟩-orbit-density corollary comes with it.  See the ledger entry below.

> **2026-08-26 live advance:** the independent Rhin-lite route has machine-checked exact content
> balances and `17^n ≤ B_n ≤ 18^n`. It now also exhausts the degree-8 critical roots without
> Sturm theory and proves the exact `(9/40)^1000` bound globally on `[2,4]` in
> `FrontA/RhinLiteMaximum.lean`. The compact-maximum bridge is complete and axiom-clean, and
> `FrontA/RhinLiteEven.lean` now lifts it to the even block subsequence `N = 2000t` (exact degree
> `2N`, central band `17^N ≤ B_N ≤ 18^N`, pointwise normalized-integrand identity/nonnegativity/
> `(9/40)^N` bound, plus the interval-integral consequences — integrability,
> `∫ ≤ length·(9/40)^N`, nonnegativity, and strict positivity on `[2,3]`/`[3,4]` — all
> sorry-free; objective 2 is complete. `FrontA/RhinLiteLogForm.lean` now also lands objective 3:
> the two `D_N`-cleared integer log forms `A₁ + B·log(3/2)`, `A₂ + B·log(4/3)`
> (`rhinLiteEven_two_log_forms`) with a common `B = D_N·(central coeff)`,
> `D_N·17^N ≤ B ≤ D_N·18^N`, `D_N = lcmUpto N · 12^N` — all sorry-free.
> `FrontA/RhinLiteApprox.lean` now wires objective 4 (the simultaneous-approximation criterion) as
> far as elementary algebra allows: `linForm_eq_log23` (change of basis to the Baker linear form)
> and `elim_identity` are trust-base clean, and `log23_effective_measure` (the effective
> irrationality measure of `log₂3` in the exact `hLF` shape) is **proved from** the single new
> disclosed crux `rhinLiteLIMeasure` (coarse Rhin linear-independence measure of
> `{1,log(3/2),log(4/3)}`). Two disclosed `src/` sorries remain: `sep_two_three`
> (`PowSeparation.lean`) and `rhinLiteLIMeasure` (`RhinLiteApprox.lean`); the latter is the
> concrete route to the former.
> **⚠️ Course correction (2026-08-31):** the `12^N`-cleared log forms of `RhinLiteLogForm` CANNOT
> prove `rhinLiteLIMeasure` — the clearing rate `K ≈ 3.49` exceeds the remainder decay `τ ≈ 1.49`
> (Wu needs `τ > K`), so the cleared remainder does not decay (in-kernel witness
> `overcleared_remainder_ge_one`).
> **Axiom-backed wiring (2026-08-31, DIRECTION option (a)):** `Assumed/Rhin1987.lean` states the
> provenance-audited `rhin_1987_log_two_three_measure` (Rhin 1987, `|u₀+u₁log2+u₂log3| ≥ 1/H^14`,
> `H ≥ 2`, read firsthand), and `log23_effective_measure` (the `log₂3` measure feeding
> `sep_two_three`) is now PROVED from it (`κ=14`, `c=1/3^14`) — clean ledger, no `sorryAx`. Closing
> `sep_two_three` now needs only the elementary crossover/finite-check step (`κ=14` pushes the
> threshold to `k ≈ 360`); see `PENDING_WORK.md`.
> The elementary mechanism (`logForm_conditional_lower`,
> `rhinLite_forms_bounded`, the size bridge) is proved and correct; it needs forms with a *decaying*
> remainder. Fix: structural clearing `H_N ∈ (12,x)^N ℤ[x]`, `D_N = lcmUpto N` (`K = 1 < τ`),
> `μ ≈ 7.9`. See `FRONT-A-RHIN-LITE-SCALING-2026-08-31.md`, `PENDING_WORK.md`.

> [!CAUTION]
> This is a chronological research ledger, not a claim that Collatz or either open front
> has been proved. Older entries preserve superseded plans and may overstate their likely
> importance. Lean source and `#print axioms` are authoritative; see `README.md` for the
> concise public status.

> **Sink closed (2026-08-31): `sep_two_three` is now PROVED sorry-free** from the cited Rhin 1987
> axiom. Added `sep_of_linear_form_poly_threshold` (threshold-parametric variant of
> `sep_of_linear_form_poly`), `crossover_exp_450` (`3^14·k^14 ≤ 2^(k/3)` for `k ≥ 450`, induction
> with base `1350^14 ≤ 2^150` and ratio step `(1+1/n)^14 ≤ exp(14/n) ≤ 2^(1/3)`), and the finite
> check `sep_two_three_small_450` (`native_decide` on `6 ≤ k < 450`, `m < 713`). Instantiated at
> `κ=14, c=1/3^14, K=450` with `log23_effective_measure_concrete` (moved into `PowSeparation.lean`).
> `#print axioms sep_two_three` = `[propext, Classical.choice, Quot.sound,
> rhin_1987_log_two_three_measure, <3 native_decide artifacts>]` — the ONLY math axiom is Rhin 1987.
> The whole two-block exclusion (`le_two_blocks_not_acyclicParadoxical`) is therefore machine-checked
> modulo that one cited axiom. **Sole remaining `src/` sorry: `rhinLiteLIMeasure`** — the novel
> Rhin-lite route whose purpose is now to *retire* the cited axiom, not to close `sep_two_three`.

**Public checkpoint (2026-08-31):** `lake build` is green (8764 jobs).
Both headline fronts remain open. `FrontA.sep_two_three` is now proved sorry-free modulo the cited
`rhin_1987_log_two_three_measure` axiom.  The novel Rhin-lite route aimed at retiring that axiom
(`FrontA.rhinLiteLIMeasure`) has its crux `rhinLite_det_dominance` **DECOMPOSED** into four disclosed
per-step analytic sub-nodes in `RhinLiteApprox.lean`.  THREE are PROVED trust-base clean
(`rhinLiteI₁_step_decay16`, `rhinLiteI₂_step_decay16`, `rhinLiteCentral_step_growth16`); the fourth,
`rhinLite_ratio_gap` (the rate-gap `μ₁>M₂`), is itself now PROVED from TWO one-sided per-interval
leaves via the pure-arithmetic glue `rhinLite_ratio_gap_of_step_bounds` (trust-base clean).  The
entire dominance assembly (`det_dominance_of_step_bounds`) is PROVED trust-base clean.  The
`[3,4]`-peak upper leaf `rhinLiteI₂_peak_upper` is now ALSO fully PROVED (via the tight per-interval
kernel bound `rhinLiteKernelAbs_div_pow_le_on_Icc34` — a `[3,4]`-restricted compact-max bridge plus
the tight bracket certificate).  The concentration lower leaf `rhinLiteI₁_concentration_lower` is
now PROVED by a log-convexity induction (`I₁(t+1)/I₁(t)` nondecreasing ⟹ stays `≥` its base value
`≥ 2κ`), resting on the moment log-convexity `rhinLiteI₁_logConvex` (`I₁(t+1)² ≤ I₁(t)·I₁(t+2)`) — now PROVED
trust-base clean via a general interval Cauchy–Schwarz (`interval_sq_integral_cauchySchwarz`,
`L²`-Hölder, also trust-base clean) — plus `rhinLiteI₁_ratio_base` (`2κ·I₁(0) ≤ I₁(1)`).  (This
replaced an earlier UNSOUND window decomposition whose "window carries ≥ ½ mass" claim is false at
small `t`.)  **Disclosed proof debt across the ENTIRE determinant crux is thus a SINGLE numerical
node `rhinLiteI₁_ratio_base`** (in `RhinLiteApprox.lean`).  Named literature and conjecture axioms
are also used explicitly.
The single-kernel Legendre development produces useful small nonzero
linear forms in `log 2`, but it neither proves the simultaneous `log 2`/`log 3` estimate
underlying `sep_two_three` nor constitutes progress on either Collatz front by itself.

## Where it stands
**Historical checkpoint (2026-09-01, review lap; superseded above).**  The Front-A two-block exclusion
`le_two_blocks_not_acyclicParadoxical` is now **fully machine-checked** — its ledger is the trust
base plus `native_decide` artifacts, with **no literature axiom** (the `sep_two_three` sink was
proved from the repo's own Rhin-lite measure, retiring the cited Rhin 1987 axiom), and it is
**sharp**: `acyclicParadoxical_seven_eight` exhibits a three-odd-block acyclic paradoxical segment,
so the exclusion ladder is finished.  This lap also caught and repaired a fidelity bug at a
headline's base: `rozier_terracol_3_2` had been stated as *unboundedly large* paradoxical starts,
which (machine-checked, `noNontrivialCycle_of_unboundedParadoxicalStarts`) implies
`NoNontrivialCycle` — an open problem — and is therefore strictly stronger than the published
theorem.  The axiom now carries Rozier–Terracol's cardinality claim, checked non-vacuous by
`infinite_paradoxical_of_tstep_cycle`.  It is the **only** cited axiom left under a Front-A
headline, and discharging it is the current binding objective.

**Historical standing picture (superseded by CURRENT above).**  The headline wiring is done and axiom-clean: `conjecture_iff_split` and
`conjecture_of_fronts` (`Conjecture.lean`, `Descent.lean`) reduce Collatz to two
front-hypotheses — `NoDivergentOrbit` (Front A, divergence) and `NoNontrivialCycle`
(Front B, cycles) — using only `propext/choice/Quot.sound`. Both fronts are open. Front B's closer needs `Compression` (an *upper*
bound on cycle circuit-count) — now diagnosed as Front B *restated* (no elementary/known
upper bound; the literature bounds circuits only below) and remains **on hold for lack of a new mathematical mechanism**. The source was
obtained on 2026-08-24 and re-read at the 2026-09-13 altitude review; source availability
is not a blocker. Front A milestone **M2′ is
complete**: `ParityRigidityW1' → NoDivergentOrbit` is sorry-free and trust-base clean, including
all Krylov–Bogolyubov/Portmanteau/frequency/drift plumbing. The remaining Front-A crux is
`ParityRigidityW1'` itself—the arithmetic restriction distinguishing positive-integer parity
itineraries from the unrestricted 2-adic shift. The inverse-parity reconstruction pull is
complete and classified BASELINE / RE-SCOPE. The
local-certificate lane is harmonic-capped below α=1 (proved, complete).

**Paradoxical-window project (`FRONT-A-PARADOXICAL.md`) — delivered, classified PROMISING
EVIDENCE.** Parts A/B/C complete: exact source lock (identity, criterion (P), slack (S), the
`7→8` example); **Rozier–Terracol Appendix A formalized sorry-free** (`headBlock_not_
acyclicParadoxical`); the exact few-block `numer` closed forms; and the full Front-A
consumption `finite_acyclicParadoxical_imp_noDivergent : FiniteAcyclicParadoxical →
NoDivergentOrbit`, machine-checked with ledger `[propext, Classical.choice, Quot.sound,
rozier_terracol_3_2]` (the whole divergence→infinite-acyclic bridge discharged sorry-free) —
and, since 2026-09-01, `rozier_terracol_3_2` is itself a proved theorem, so the ledger is the
bare trust base.
Computational evidence suggests that **every acyclic paradoxical word has ≥ 3 odd blocks**;
this was checked two ways (word-based to length 38; independent orbit-based to start 100000).
The corresponding general interior two-block exclusion
(`le_two_blocks_not_acyclicParadoxical`) is machine-checked **modulo the single inequality
`b + d ≤ 5`** — ultimately dependent on the sole source `sorry`, `sep_two_three`. Case A (both blocks
subcritical), the elementary squeeze, `window_unique_m`, the power bracket, and the finite
discharge once `b+d ≤ 5` are all sorry-free. **`b + d ≤ 5` is now confirmed Baker-grade**
(effective irrationality of `log₂3`): the 2026-08-25-1500 review lap REFUTED the last elementary
hope by proving the real relaxation of `¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` is feasible at unbounded `g`
(exact witness at `g=41`, `experiments/two_block_relaxation.py`), so no `nlinarith`/polynomial
certificate can exist. The remaining route is to consume a faithfully stated published effective
separation theorem as a named axiom or to formalize such a theorem. The former matches this
repository's policy for established literature; neither choice would prove the much stronger
global finiteness of acyclic paradoxical segments.

## What's happened (newest first)
- **2026-09-19 (attended Fable session + three one-lap Opus-low helpers — the first-crossing near-cycle route):**
  `StoppingCorrect` failures are *near-cycles*: `overshoot_identity` / `three_mul_overshoot_lt`
  (`D·n + 2^m·E = numer`, `3E < a`), the run-product bound `run_product_bound`
  (`2^m·n^(r−1)·y ≤ 3^K·(n+1)^r`, standard axioms), and the consequences `endpoint_mul_pow_lt`
  (overshoot ≤ about the run count) and `gap_mul_pow_le` (integer Simons–de Weger Lemma 4).
  Rungs: `stoppingCorrect_oneRun` (unconditional; `SteinerOneCircuit` discharged from
  `sep_two_three`), `descends_of_twoRun`, `descends_of_oddRunCount_le_four`,
  `descends_of_oddRunCount_le_fifty` — the last three under the explicit `def` `CSTVerified`
  (Rozier–Terracol Cor. 5.4).  The fifty-run rung replaces power-comparison certificates by
  44 verified digits of `log 2`, `log 3` (`LogTwoThreeDigits.lean`, Mathlib's series remainder
  bound) and certifies the `log₂3` bracket at denominators ~6·10^15 by rational arithmetic.
  `survivor_ones_pow_ge`: a CST failure satisfies `3·c·n ≤ K^437` (stopping-time outlier).
  Paper-level: Simons–de Weger's `m ≤ 68` pincer transfers verbatim to first-crossing
  near-cycles (closure enters only their Lemma 4 telescoping and the last chaining link, both
  on the harmless side), giving CST for at most 68 odd runs — the exact reach of the two-log
  pincer is logarithmically many runs, `r ≳ 2.17·ln K`; Collatz needs `r ≥ εK`.
  Experiments: `parity_reconstruction.py coalescence N` and `near-cycle N` with hand-computed
  pytest anchors.  The coalescence / smaller-start reduction route was measured and closed
  (zero gain at the stopping-time records 27, 871, 77031).  Later the same night the
  minimality lever (a smaller start with a same-shape ballot word into the same orbit would
  survive its first crossing) led to two conjectures about ballot coalescence, both refuted by
  the Φ-walk probes `ballot-nonmin` (length 29) and `ballot-walk` (length 34: starts 15231450875
  and 15231450879, both with 22 odd steps in 34 ballot letters, meet at 27822043514); the lever
  stands but is thin.  Rationale and the run-count-gap
  node: personal KB leaves `collatz-near-cycle-few-runs-2026-09-19.md`,
  `collatz-avenues-blueprint-2026-09-19.md`, `collatz-ballot-coalescence-2026-09-19.md`.
- **2026-09-13 (operator-assigned bounded node — min-term trunk bound):** new default-build module
  `FrontA/TrunkBound.lean`. Product identity `2^m·x_m·∏_{I}3x_i = 3^a·n·∏_{I}(3x_i+1)` over the
  odd-step set `oddSteps`; min-term inequality `2^m(3x_min)^a < 3^a(3x_min+1)^a` for every strictly
  climbing segment (odd or even start; `≤` form for cyclic endpoints); real form
  `x_min < a/(3(m log 2 − a log 3))` for subcritical segments; Rhin-lite corollary
  `x_min < a^437/(3·rhinLiteSepC) + a`, i.e. `x_min < 396^6000·6^436·a^437` in `ℕ`. (1)–(3) are
  trust-triple only; the corollary inherits the eleven allow-listed Rhin-lite native certificates.
  Kernel control on `(7,8)`: odd values `7,11,17,13,5`, `x_min=5`, `a=5`,
  `2^8·15^5 = 194400000 < 254803968 = 3^5·16^5`. Easy half of Rozier–Terracol Theorem 4.2; no
  novelty claimed. Gate `scripts/check-fixed-block-bound.sh` GREEN (8772 jobs).
- **2026-09-01 (review lap — fidelity bug caught at a headline's base, and repaired):**
  `Assumed.rozier_terracol_3_2` read *"for every `K` there are `k, m` with `K < 2^k n` and
  `Paradoxical (2^k n) m"`* — unboundedly large paradoxical starts.  Machine-checked that this
  form implies `NoNontrivialCycle` (from a start `2^k n` the shortcut orbit halves down to `n`
  then follows `n`'s orbit, so a *bounded* orbit admits no returning segment once `2^k n` exceeds
  the bound; a nontrivial cycle's minimum has infinite shortcut stopping time and a bounded orbit).
  No published theorem gives `NoNontrivialCycle`, so the axiom was strictly stronger than its
  source.  **Repaired**: the axiom now states Rozier–Terracol's cardinality claim
  (`{p | Paradoxical (2^p.1 * n) p.2}.Infinite`); the refutation stays in `src/` as a permanent
  guard (`UnboundedParadoxicalStarts`, `not_unboundedParadoxicalStarts_of_bounded`,
  `noNontrivialCycle_of_unboundedParadoxicalStarts`, all trust-base clean); non-vacuity is
  anchored by `infinite_paradoxical_of_tstep_cycle` (a shortcut cycle through `n > 2` really does
  give infinitely many paradoxical segments starting at `2^0 n`);
  `diverges_imp_infinite_acyclicParadoxical` re-derived through the injection
  `(k,m) ↦ (2^k m₀, m)`, so `finite_acyclicParadoxical_imp_noDivergent` is unchanged in statement
  and ledger.  Also pinned **sharpness** of the two-block exclusion:
  `acyclicParadoxical_seven_eight` (`n=7`, `m=8`, word `TTTFTFFT`, three odd blocks, kernel
  `decide`) — no three-block strengthening can exist.  Direction reset to discharging
  `rozier_terracol_3_2`, split bounded / unbounded orbit.
- **2026-08-26 (Lane 1 — the Furstenberg axiom is DISCHARGED):** Furstenberg's 1967
  topological ×p×q rigidity is now a **proved theorem**, axiom-clean
  (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, verified 2026-08-26):
  `Furstenberg.isClosed_invariant_finite_or_univ` in `Rigidity/Furstenberg.lean`
  (~900 lines, elementary — no measure theory, no entropy, no disjointness), plus the
  density corollary `dense_orbit_of_not_isOfFinAddOrder` (the ⟨p,q⟩-orbit of any
  non-torsion point is dense).  `Assumed/Furstenberg.lean` keeps the same name and
  statement as a theorem, so the 2⊥3 rigidity trinity's topological member no longer
  costs an axiom.  Route: Boshernitzan 1994 as presented in Manners arXiv:1305.1514 §4
  (pin note + chink ledger: `papers/arxiv-1305.1514-manners-pyjama-furstenberg-pin.md`;
  headline finding: the route survives formalization with zero errata — one glossed
  detail, the rational-limit-point case with denominator sharing factors with `pq`,
  filled by orbit-pigeonhole in `exists_fixed_in_orbit`).  Prior-art sweep says
  apparently first in any prover (hedge: survey-based; the lean-eval "furstenberg"
  problems are multiple recurrence, a naming trap).
- **2026-08-25 (public-readiness review):** stopped the treadmill and froze the release candidate.
  Reclassified the single-log work as ancillary formalization, removed corpus-wide novelty claims,
  and made the one `sorry`, named assumptions, computational evidence, and open fronts prominent.
  This entry supersedes older “MANDATED next chip” language below.
- **2026-08-25 (review lap ~2330 — direction KEPT, constants corrected, single-kernel leg 2 audited):**
  Reviewed the two GO-grind laps (2100 uniform-measure reduction; 2300 full single-kernel Legendre
  toolkit). Confirmed leg 1 (`Gelfond.lcmUpto_le`) and the entire leg-2 machinery in `Legendre.lean`
  — linear form `∫₀¹ P_n/(1−a·y)=A+B·log(1−a)`, geometric remainder bound, non-vanishing — are all
  trust-base clean. Findings landed the honest object: **Rhin 1987** `{1,log2,log3}` measure, explicit
  exponent `E=13.3 ⇒ C=15, k≥400` (`C=6` unprovable, illustrative only); leg 3 (two-*kernel* Rhin
  determinant) is a genuine multi-lap expedition (transfinite diameter, effective `n(ε)` asymptotics).
  Pinned the then-next chip: single-log denominator/integrality tracking. That auxiliary chip later
  landed but was reclassified at the public-readiness review; the Collatz crux stayed unchanged.
- **2026-08-25 (GO grind 2300 — full single-kernel effective-measure toolkit, `Legendre.lean`):**
  Built from scratch / faithfully ported (v4.18→v4.33) the whole single-Möbius-kernel machinery, all
  trust-base clean: `shiftedLegendre` + integer-coeff expansion; order-`n` Padé vanishing; the `n`-fold
  IBP identity `∫₀¹ P_n·f = ((−1)^n/n!)∫₀¹ (y(1−y))^n f⁽ⁿ⁾`; the kernel derivative `dⁿ[1/(1−a·x)]`;
  the Padé remainder form + geometric bound `|Λ_n| ≤ (|a|/4(1−a))^n/(1−a)`; moment closed form;
  **linear form `Λ_n = A + B·log(1−a)`**; and **non-vanishing `Λ_n ≠ 0`**. ⟹ all three effective-measure
  facts for a single kernel are machine-checked. Build 🟢 8754 jobs.
- **2026-08-25 (review lap 2100 — crux core reclassified 🟡 Gelfond; uniform-measure reduction proved):**
  Route-decisive source read: the sole open input `sep_two_three` ≡ an effective irrationality measure
  of `log₂3`, which is the classical **Gelfond 1935** effective bound on `|2ⁿ−3ᵐ|` (linear forms in
  *two* logs; explicit in **Bennett–Bugeaud** *Acta Arith.* 155 (2012) & Bugeaud's monograph §3.1) —
  a *polynomial* measure, exponentially stronger than the `2^(−k/3)` needed. So the core is 🟡
  project-scale (explicit hypergeometric/interpolation; formalizable), NOT 🟠 generational; the prior
  "multi-month, near-hopeless Baker" framing was too pessimistic. Landed (trust-base only): missing
  connective `poly_le_two_pow` (∀C ∃K, k^C ≤ 2^k for k≥K) and **`sep_of_uniform_measure`** —
  machine-checks that ONE uniform bound `3^k ≤ (2^m−3^k)·k^C` (large k) + crossover + finite check ⇒
  `sep_two_three` for every near-critical `k ≥ 6`. Then **discharged the finite check**:
  `sep_two_three_small` (via `native_decide`, ~7s) proves `sep_two_three` outright for near-critical
  `6 ≤ k < 130`. ⟹ The whole residual collapses to the pure uniform measure
  `∀ near-critical k ≥ 130, 3^k ≤ (2^m−3^k)·k^6` = the Gelfond bound. Build 🟢 8752 jobs.
- **2026-08-25 (lap 1600 — crux DECOMPOSED: reduction proved, one clean sorry isolated):** Replaced
  the bare `b+d ≤ 5` sorry with a machine-checked reduction. New module `FrontA/PowSeparation.lean`
  proves sorry-free `grow_two_three` (elementary induction), `finite_two_block_check` (k∈[6,14] via
  `native_decide`), and `bd_reduction` (β=1/3: window + (W) + (A) + separation ⇒ k≤5). In
  `near_critical_containment`, `b+d≤5` now derives (W)/(A) from the proved `hbracket`/¬A and calls
  `bd_reduction`. **Sole remaining `src/` sorry = `sep_two_three`**, the clean weak-Baker separation
  `3^(3k) ≤ (2^m−3^k)^3·2^k` for near-critical k≥6. Build 🟢 8752 jobs.
- **2026-08-25 (review lap 1500 — elementary route for the crux REFUTED, Baker confirmed):**
  The crux had been reduced (earlier laps) to the single inequality `b + d ≤ 5`, with a queued
  "MAJOR LEAD" claiming it closes elementarily via Aristotle's criteria A/B. This lap REFUTED
  that: proved (exact-rational witness at `g=41`, `experiments/two_block_relaxation.py`) that the
  real relaxation of `¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` is feasible at unbounded `g`, so no nlinarith/
  polynomial certificate exists (verified in-Lean: couplings compile, nlinarith fails). The
  integer-truth (exactly 4 pairs, all `b+d≤5`, to `g≤200`) is Baker-forced. Redirected DIRECTION
  to the sole GO path (build effective irrationality of `log₂3`); forbade further elementary
  attempts. Axiom audit re-run (below). Build 🟢 8751 jobs.
- **2026-08-25 (crux reduced to a FINITE containment — sharp gap closes all but 2 configs):**
  Sharpened `core_of_gap` to a division-free integer-ceiling `∀`-gap instantiated at the true
  `w₁`. Census (`b,c,d,e<34`): the sharp gap holds for EVERY subcritical tuple except exactly
  `(2,3,3,0)` and `(3,3,2,0)`, both proved closable by `omega` (`residue_core_exc1/2`). The
  sole `src/` sorry is now just the finiteness **containment** `¬gap ∧ U₁>0 → tuple ∈ {those 2}`.
  Aristotle working the full core async. Build 🟢 8751 jobs.
- **2026-08-25 (crux narrowed hard — elementary regime of the residue core PROVED):** Reduced
  the whole two-block exclusion to one self-contained ℕ lemma `two_block_residue_core`
  (submitted to Aristotle, job `4006e40e`), then PROVED its **elementary regime `core_of_gap`
  sorry-free**: a genuinely new contrapositive argument (exact identity `2^m·y + 2^(b+c+d) =
  3^(b+d)(n+1) + 3^d·2^b(2^c−1)`, no integrality) that a census shows covers ~99.7% of
  subcritical `(b,c,d,e)` (3791/3803 in range). The sole remaining `src/` sorry is the thin
  **residual** where the gap fails and a 3-adic least-residue bound on `w₂` is genuinely
  needed (the required bound grows with `b`). Build 🟢 8751 jobs.
- **2026-08-25 (review lap — two-block crux decomposed, Case A proved):** Made real crux
  progress on the sole `src/` sorry `le_two_blocks_not_acyclicParadoxical`. Split the
  `[T]^b[F]^c[T]^d[F]^e` itinerary at step `b+c` (`traceWord_add` + `List.append_inj`) into two
  head-block segments, then case-split on criticality. **Case A (both blocks subcritical) is now
  PROVED sorry-free** (`headBlock_endpoint_le` twice ⇒ `y ≤ X ≤ n`), and whole-word
  subcriticality is shown to forbid both-supercritical. The two residual cases B/C are reduced
  to ONE arithmetic core (`GOAL2'`, the joint 2-adic/3-adic residue force via relation (★)
  `3^b w₁ = 2^(c+d) w₂ − 2^c + 1`) with the reconstruction route + refuted simple bounds written
  into PENDING_WORK. Build 🟢 8751 jobs.
- **2026-08-24 (paradoxical-window project delivered → PROMISING EVIDENCE):** Executed
  `FRONT-A-PARADOXICAL.md` end to end. Landed `experiments/paradoxical.py` (exact source lock +
  two independent enumerators) and `CollatzMoonshot/FrontA/Paradoxical.lean` +
  `CollatzMoonshot/Assumed/Paradoxical.lean`. Formalized RT Appendix A sorry-free; proved the
  exact criterion (P)/slack (S) and few-block `numer` closed forms; discharged the entire
  Front-A consumption `finite_acyclicParadoxical_imp_noDivergent` down to the single cited RT
  Theorem 3.2 axiom (no `sorryAx`). New exhaustively-verified restriction: **≥ 3 odd blocks**
  for every acyclic paradoxical word (two independent implementations). Its full proof is a
  deep open sub-problem (2/3-adic residue interplay); proved the 2-adic foundation
  `headBlock_dvd_succ`. One disclosed active-crux `src/` sorry remains
  (`le_two_blocks_not_acyclicParadoxical`). Build 🟢 8751 jobs.
- **2026-08-24 (parity reconstruction complete + audited):** Landed the exact reconstruction
  experiment and the sorry-free cylinder-envelope/residue/eventual-periodicity Lean kernel.
  Added `normalized_endpoint_ne_start_one`, a permanent kernel-checked counterexample to a
  false normalized-endpoint claim. Corrected the broader overclaim too: same-suffix endpoint
  spread refutes suffix-only endpoint prediction, not every finite-state Lyapunov proof.
  Classified the result BASELINE / RE-SCOPE and opened `FRONT-A-PARADOXICAL.md`.
- **2026-08-24 (M2′ complete):** Proved
  `parityRigidityW1'_imp_noDivergent : ParityRigidityW1' → NoDivergentOrbit`, including
  arbitrary empirical cluster invariance/support, exact odd-frequency transport, the uniform
  sub-sharp `limsup`, and high-tail drift consumption. Full build green (8748 jobs); independent
  targeted rebuild and axiom audit report exactly `[propext, Classical.choice, Quot.sound]`.
  Re-pointed the live research pull to parity reconstruction/carries.
- **2026-08-24 (review lap, later):** **RE-SCOPED direction.** Established Front B
  `Compression` is Front B restated + source-blocked → on hold, no more block vocabulary.
  Redirected the binding crux to **Front A M2′** (`ParityRigidityW1' → NoDivergentOrbit`):
  confirmed mathlib has Prokhorov (`CompactSpace (ProbabilityMeasure ℤ₂)`) +
  Portmanteau-on-clopen; isolated the sole gap as a Krylov–Bogolyubov invariant-measure
  module; **landed the two pure M2′ endpoints** `exists_freqThreshold_gt` +
  `not_diverges_of_eventually_lt` (`Rigidity/Drift.lean`, trust-base clean) and the precise
  3-piece decomposition (`PENDING_WORK.md`, `DIRECTION.md`).
- **2026-08-24 (review lap):** Certified the harmonic-dual project COMPLETE. Diagnosed
  the `OneCircuit` a≥2 case as **Steiner's theorem (Baker/transcendence), not an `omega`
  leaf**, and **off the critical path** (Hercher covers all rungs ≤91). Resolved it via
  an explicit `SteinerOneCircuit` hypothesis — sorry removed, no new axiom, imported from
  root (`oneCircuitCanonical_trivial` is now `[propext, choice, Quot.sound]`). Created
  DIRECTION.md (binding directive → Front B `Compression`) + this STATUS.md.
- **2026-08-24:** Front B ladder-base probe: closed forms for the canonical one-circuit
  word `trueᵃfalseᵇ` (`numer = 3ᵃ−2ᵃ`, `den = 2^(a+b)−3ᵃ`), the `den ∣ numer ↔ den ∣ 2ᵇ−1`
  reduction, and the a=1 slice in full.
- **2026-08-24:** **Harmonic-dual obstruction PROVED** sorry-free & depth-uniform:
  `no_positive_harmonic_local_certificate` — the constant-lift-1 local-certificate
  architecture on floors `{1,7/4,3,6,12}` admits no positive certificate at any depth
  `k≥9` (memory-9 `native_decide` supersolution, contraction `0.99224<1`, Farkas dual).
  A no-go for one certificate scheme, NOT a Collatz-divergence claim.
- **2026-08-24:** Harmonic experiment made exact/reproducible
  (`experiments/barrier_harmonic_dual.py`): refutation surface for the α=1 gap; only
  `mod 3^9` memory suffices, no closed-form/rank-1 weight (the gap is real but structureless).
- **2026-08-23:** Exponent-4/5 backward-tree pipeline complete (2/3→3/4→4/5 rungs green);
  harmonic no-go then showed this local-certificate ladder cannot reach α=1.
- **2026-08-23:** Front B dictionary `noNontrivialCycle_iff_frontB` proved; `FrontB`
  threads restated over `Primitive` words (word-powers made the naive statements
  degenerate = `FrontB` in disguise); Route-1 gcd-harvest (Thread 7) KILLED.
- **2026-08-22:** Hercher 2023 verified firsthand (≥92 circuits, no transcendence);
  corrected the `abc`-closes-cycles overclaim (abc bounds `D` *below* only).

## Outstanding
### Short-term (mirror PENDING_WORK top)
- **2026-09-13 — reflection DONE; awaiting a new idea.** No current bounded
  objective clears the new-mathematics bar. The ranking in `DIRECTION.md` is
  not an execution queue. Reopening requires an exact statement and evidenced
  mechanism; the O.Finite→U.Finite route specifically requires a finite-to-one
  map. Both fronts and both finiteness predicates remain open. The cycle edge,
  A2, fixed-b Campaign B and rung 3 stay closed; finite-prefix follow-ups stay retired.
- The remaining short-term bullets below are historical, not current assignments.
- **2026-09-08 — the rung-3 window-node objective and front-normalized length-8 classification
  are COMPLETE.**  The exceptional lengths `5,16,27` are rejected in Lean by a kernel-checked
  finite residue certificate; `src/` remains at **0 sorries**.  Await an altitude-level retarget
  rather than following the now-stale rung-3 instructions in `DIRECTION.md`.
- **2026-09-01 — the binding objective is COMPLETE.**  `src/` has **0 sorries**;
  `finite_acyclicParadoxical_imp_noDivergent`, `rozier_terracol_3_2`,
  `two_pow_approx_three_pow_from_above` are trust-base clean.  Remaining non-trust-base
  dependencies anywhere: the 13 `native_decide` certificates under `sep_two_three` /
  `le_two_blocks_not_acyclicParadoxical` (hygiene), and the Front-B / computation citations
  (`hercher_*`, `eliahou_*`, `collatz_verified_*`, `tao_2019_*`, `abc`, `baker_bounded_difference`).
  The bullets below are the historical short-term list and are superseded.
- **Front A two-block exclusion** (binding): discharge the sole `src/` sorry `sep_two_three`
  (`PowSeparation.lean`). Reduced (sorry-free) to ONE **uniform Rhin measure**
  `3^k ≤ (2^m−3^k)·k^C` via `sep_of_uniform_measure`; the honest object is **Rhin 1987**'s
  `{1,log2,log3}` measure (explicit `E=13.3 ⇒ C=15, k≥400`; `C=6/k≥130` illustrative only).
  Legs 1–2 built trust-base clean (`Gelfond.lcmUpto_le`, all of `Legendre.lean`).
  The single-log denominator/integrality package has landed and is now classified ancillary:
  it gives small nonzero forms for `log 2`, not the simultaneous estimate. A future run must
  either consume a source-audited named literature axiom or explicitly scope the Rhin
  two-kernel determinant as a separate formalization project.
  **Refuted, do NOT retry:** any elementary `nlinarith`/`omega` bound on `b+d`/`d`
  (`experiments/two_block_relaxation.py`). Fallback (BASELINE, not for gate-clearing): cite the
  Rhin bound as a narrow, provenance-documented axiom.
- M2′ is complete. Do not rebuild measure plumbing or spend the next project only proving
  the converse calibration `NoDivergentOrbit → ParityRigidityW1'`.
- Front B `Compression` is **on hold** — source availability is resolved; a new
  mathematical idea is still needed. Fixed-circuit finiteness does not supply it.
- Historical optional target `SteinerOneCircuit` remains deferred. The effective
  separation input now exists; the old “multi-year” estimate from its absence is stale.
  This is a known theorem and is not the selected new-mathematics objective.
### Long-term
- Prove `ParityRigidityW1'` itself — the arithmetic intertwining making positive-orbit
  conditioning visible to ×2×3 rigidity (FRONT-A-ROUTES §A1, "no route close"). M2′ makes
  W1′ a valid sufficient condition; this is the genuinely-open new mathematics behind it.
- Discharge / narrow the Front B cited axioms (`baker_bounded_difference`, `eliahou`,
  `hercher_*`); consider adopting the stronger Hercher–Bařina unconditional bound.
- Reopen Front B `Compression` only for a new mathematical mechanism; the SdW
  source is already available.
### To completion
- Both fronts unconditional (or each conditional exactly where the mathematics is), all
  cited axioms discharged or reduced to trust base + `native_decide` + genuine citations.

## Axiom ledger (per headline theorem)
Trust base = `propext, Classical.choice, Quot.sound` (+ `native_decide` `ax_*` artifacts),
excluded from the math-axiom count below.  Re-run from real `#print axioms` on 2026-09-08.

| headline theorem | paper claim | `#print axioms` shows (beyond trust base) | math-axioms |
|---|---|---|---|
| `conjecture_iff_split` | uncond (finite wiring) | — | 0 ✅ |
| `run_product_bound` / `endpoint_mul_pow_lt` / `gap_mul_pow_le` | new: run-product bound at a first crossing | — | 0 ✅ |
| `stoppingCorrect_oneRun`, `steinerOneCircuit` | CST on one-run words; Steiner 1977 | Rhin-lite `native_decide` certificates only | 0 ✅ |
| `descends_of_twoRun`, `descends_of_oddRunCount_le_four`, `descends_of_oddRunCount_le_fifty` | CST on ≤ 2 / ≤ 4 / ≤ 50 runs | Rhin-lite certificates only | 0 ✅ (`CSTVerified` is an explicit `def` hypothesis) |
| `survivor_ones_pow_ge` | CST failure ⇒ `3cn ≤ K^437` | Rhin-lite certificates only | 0 ✅ |
| `finite_odd_acyclicParadoxical_imp_noNontrivialCycle` | new edge: O.Finite → no nontrivial cycle | — | 0 ✅ (`FiniteOddAcyclicParadoxical` is an explicit `def` hypothesis) |
| `finite_acyclicParadoxical_imp_conjecture` | U.Finite → Collatz (conditional) | — | 0 ✅ (`FiniteAcyclicParadoxical` is an explicit `def` hypothesis) |
| `conjecture_of_fronts` | uncond (finite wiring) | — | 0 ✅ |
| `noNontrivialCycle_iff_frontB` | uncond (dictionary) | — | 0 ✅ |
| `parityRigidityW1'_imp_noDivergent` | Front A conditional closer | — | 0 ✅ (`ParityRigidityW1'` is an explicit hypothesis/`def`, not an axiom) |
| `FrontA.sep_two_three` | effective 2/3 power separation | 13× `native_decide.ax` (Rhin-lite tower + the `k<450` table) | **0 math** ✅ 🟢 — the Rhin 1987 axiom is RETIRED |
| `le_two_blocks_not_acyclicParadoxical` | new: 2-block exclusion (generalizes RT App. A) | 13× `native_decide.ax` + `finite_two_block_check` | **0 math** ✅ 🟢 — and **sharp** (`acyclicParadoxical_seven_eight`) |
| `FrontA.threeBlock_not_acyclicParadoxical_of_exceptional` | rejects the exceptional lengths `5,16,27` | — | **0 math** ✅ 🟢 — nested ceilings + kernel finite residue certificate |
| `FrontA.threeBlock_length_eq_eight_of_acyclicParadoxical` | rung-3 front-normalized length classification | inherited Rhin-lite/window `native_decide.ax` artifacts only | **0 math** ✅ 🟢 — no new native artifact in the exceptional tail |
| `finite_acyclicParadoxical_imp_noDivergent` | Front A conditional closer (paradoxical) | — | 0 ✅ 🟢 — RT citation DISCHARGED **and** the Diophantine node PROVED (2026-09-01); trust base only |
| `Assumed.rozier_terracol_3_2` | RT 2026 Thm 3.2 (full) | — | 0 ✅ now a **THEOREM**, proved in-repo, trust base only |
| `infinite_paradoxical_of_bounded_orbit` | RT 2026 Thm 3.2, bounded case | — | 0 ✅ node-free, fully proved |
| `FrontA.two_pow_approx_three_pow_from_above` | `2^s` approximates `3^A` from above to relative `1/N`, infinitely often | — | 0 ✅ **PROVED** 2026-09-01 (multiplicative pigeonhole; no logs, no irrationality, no `native_decide`) |
| `frontB_of_compression_le_91` | Front B closer | `hercher_min_circuit_count` | 1 · 🟡 proved (Hercher 2023, no transcendence; `Compression` still an *open def*, not an axiom) |
| `Assumed.frontier_min_cycle_length` | cycle-length frontier | `hercher_odd_members_bound` | 1 · 🟡 proved (Hercher 2023 + Bařina 2025 compute) |
| `two_pow_68_lt_of_onCycle_nontrivial` | conditional demo | `collatz_verified_up_to_two_pow_68` | 1 · 🟢 finite computation |
| `no_positive_harmonic_local_certificate` | no-go (one scheme) | 4× `native_decide.ax` | 0 math · 🟢 finite checks |
| `Furstenberg.isClosed_invariant_finite_or_univ` | Furstenberg 1967 ×p×q rigidity | — | 0 ✅ **axiom DISCHARGED** (2026-08-26) |
| `noNontrivialCycle_of_unboundedParadoxicalStarts` | fidelity guard (this repo) | — | 0 ✅ trust base only |
| `infinite_paradoxical_of_tstep_cycle` | non-vacuity anchor (this repo) | — | 0 ✅ trust base only |
| `acyclicParadoxical_seven_eight` | sharpness witness | — | 0 ✅ kernel `decide`, no `native_decide` |

**Correction on record (2026-09-01).**  `rozier_terracol_3_2` previously claimed *unboundedly
large* paradoxical starts `2^k n`.  That is strictly stronger than Rozier–Terracol Thm 3.2:
in-kernel, it implies `NoNontrivialCycle`, an open problem
(`noNontrivialCycle_of_unboundedParadoxicalStarts`).  It now states the published cardinality
claim.  Treat this as the template for auditing every remaining cited axiom: *state exactly what
the source proves, then try to derive something famous from it.*

Cited axioms in `Assumed/` + `FrontB/Threads.lean` (the discharge frontier):
`eliahou_min_cycle_length` 🟡, `hercher_odd_members_bound` 🟡, `hercher_min_circuit_count` 🟡,
`baker_bounded_difference` 🟠 (Baker/Tijdeman), `tao_2019_almost_bounded` 🟠 (Tao 2019,
logarithmic density + Syracuse random variables), `rozier_terracol_3_2` (**discharged; listed historically**),
`collatz_verified_*` 🟢, `abc` 🔴 (open conjecture — used ONLY in results themselves stated
conditional on abc).  `furstenberg_topological_rigidity` is **discharged** (now a theorem).
No 🔴 appears on any unconditional headline.

## Pointers
- Binding directive: `DIRECTION.md` → CURRENT DIRECTIVE
- Routes: `FRONT-A-PARADOXICAL.md` (historical route; awaiting new mechanism), `FRONT-A-PARITY-RECONSTRUCTION.md` (done),
  `FRONT-A-ROUTES.md`,
  `FRONT-B-ROUTES.md`, `FRONT-A-HARMONIC-DUAL.md` (done)
- Newest baton: `HANDOFF-2026-09-13-whole-board-reflection.md` · scratchpad: `PENDING_WORK.md`
- Findings: `ON-LINE-FINDINGS-2026-08-25-log23-effective-measure.md`, `…-rhin-wu-explicit-construction.md`
