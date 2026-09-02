# STATUS — collatz-moonshot 📊
**Machine-checked conjecture graph for Collatz: two fronts, every edge axiom-audited.** ·
**Build**: 🟢 green (8766 jobs) · **Updated**: 2026-09-02 (odd-block ladder, rung 3 opened) · `0f9fde9`+


> **2026-09-02 (latest) — the odd-block ladder reaches RUNG 3, and its crux is a finite census.**
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
> `src/` sorry is that census.  It is already narrowed: `threeBlock_cascade_elim` and
> `threeBlock_gap_of_real` PROVE the whole `w₃ ≥ 1` half sorry-free, so the disclosed node is only
> `threeBlock_ceiling_gap` — the tuples where the two integer ceilings must do the work.


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
**Current (2026-09-01, review lap).**  The Front-A two-block exclusion
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

**Standing picture.**  The headline wiring is done and axiom-clean: `conjecture_iff_split` and
`conjecture_of_fronts` (`Conjecture.lean`, `Descent.lean`) reduce Collatz to two
front-hypotheses — `NoDivergentOrbit` (Front A, divergence) and `NoNontrivialCycle`
(Front B, cycles) — using only `propext/choice/Quot.sound`. Both fronts are open. Front B's closer needs `Compression` (an *upper*
bound on cycle circuit-count) — now diagnosed as Front B *restated* (no elementary/known
upper bound; the literature bounds circuits only below) and **source-blocked** (the needed
Simons–de Weger source is not included); its Lean apparatus is feature-complete and **on hold**. Front A milestone **M2′ is
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
- Front B `Compression` is **on hold** (blocked + mis-scoped) — do not extend until the
  SdW source lands or a new upper-bound idea appears.
- (Optional) Prove `SteinerOneCircuit` — Steiner 1977; needs an effective irrationality
  measure for `log₂3`. Multi-year; leave isolated.
### Long-term
- Prove `ParityRigidityW1'` itself — the arithmetic intertwining making positive-orbit
  conditioning visible to ×2×3 rigidity (FRONT-A-ROUTES §A1, "no route close"). M2′ makes
  W1′ a valid sufficient condition; this is the genuinely-open new mathematics behind it.
- Discharge / narrow the Front B cited axioms (`baker_bounded_difference`, `eliahou`,
  `hercher_*`); consider adopting the stronger Hercher–Bařina unconditional bound.
- Reopen Front B `Compression` if the SdW source or a new upper-bound idea arrives.
### To completion
- Both fronts unconditional (or each conditional exactly where the mathematics is), all
  cited axioms discharged or reduced to trust base + `native_decide` + genuine citations.

## Axiom ledger (per headline theorem)
Trust base = `propext, Classical.choice, Quot.sound` (+ `native_decide` `ax_*` artifacts),
excluded from the math-axiom count below.  Re-run from real `#print axioms` on 2026-09-01.

| headline theorem | paper claim | `#print axioms` shows (beyond trust base) | math-axioms |
|---|---|---|---|
| `conjecture_iff_split` | uncond (finite wiring) | — | 0 ✅ |
| `conjecture_of_fronts` | uncond (finite wiring) | — | 0 ✅ |
| `noNontrivialCycle_iff_frontB` | uncond (dictionary) | — | 0 ✅ |
| `parityRigidityW1'_imp_noDivergent` | Front A conditional closer | — | 0 ✅ (`ParityRigidityW1'` is an explicit hypothesis/`def`, not an axiom) |
| `FrontA.sep_two_three` | effective 2/3 power separation | 13× `native_decide.ax` (Rhin-lite tower + the `k<450` table) | **0 math** ✅ 🟢 — the Rhin 1987 axiom is RETIRED |
| `le_two_blocks_not_acyclicParadoxical` | new: 2-block exclusion (generalizes RT App. A) | 13× `native_decide.ax` + `finite_two_block_check` | **0 math** ✅ 🟢 — and **sharp** (`acyclicParadoxical_seven_eight`) |
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
logarithmic density + Syracuse random variables), `rozier_terracol_3_2` 🟡 (**current target**),
`collatz_verified_*` 🟢, `abc` 🔴 (open conjecture — used ONLY in results themselves stated
conditional on abc).  `furstenberg_topological_rigidity` is **discharged** (now a theorem).
No 🔴 appears on any unconditional headline.

## Pointers
- Binding directive: `DIRECTION.md` → CURRENT DIRECTIVE
- Routes: `FRONT-A-PARADOXICAL.md` (live), `FRONT-A-PARITY-RECONSTRUCTION.md` (done),
  `FRONT-A-ROUTES.md`,
  `FRONT-B-ROUTES.md`, `FRONT-A-HARMONIC-DUAL.md` (done)
- Newest baton: newest `HANDOFF-2026-*.md` (find with `ls HANDOFF-*.md | sort` — currently `HANDOFF-2026-09-01-rt-axiom-fidelity.md`) · scratchpad: `PENDING_WORK.md`
- Findings: `ON-LINE-FINDINGS-2026-08-25-log23-effective-measure.md`, `…-rhin-wu-explicit-construction.md`
