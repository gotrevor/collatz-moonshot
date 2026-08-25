# PENDING_WORK

## ★ REVIEW LAP 2026-08-25-2100 — crux core reclassified 🟡 (Gelfond), reduced to ONE uniform measure ★

**Route-decisive source read (WebSearch).** The sole open input `sep_two_three` ≡ an effective
irrationality measure of `log₂3`. This is NOT a hopeless multi-year wall — it is the **classical
Gelfond 1935** effective lower bound on the distance `|2ⁿ − 3ᵐ|` between powers of 2 and 3 (linear
forms in *two* logarithms; predates Baker's general theorem), with explicit constants in
**Bennett–Bugeaud, "Effective results for restricted rational approximation", Acta Arith. 155 (2012)**
and **Bugeaud, *Linear Forms in Logarithms and Applications*, §3.1**. Gelfond/Baker give a
*polynomial* irrationality measure `|log₂3 − m/k| ≥ c/k^μ` (finite μ; the proven value is small,
certainly < ~6). We need only the vastly weaker *exponential* `|log₂3 − m/k| ≳ 2^(−k/3)/k`, so ANY
finite measure suffices for all large k. ⟹ Core reclassified **🟡 project-scale** (explicit
hypergeometric/Padé/interpolation constructions — formalizable, no mathlib support yet), **not 🟠
generational**. The 2026-08-25-1900 handoff's "genuinely multi-month, no support, irreducible Baker"
framing was over-pessimistic about tractability (the *route* was right; the *difficulty tier* wasn't).

**Landed this lap (sorry-free, trust base only; `PowSeparation.lean`):**
- `poly_le_two_pow (C) : ∃ K, ∀ k ≥ K, k^C ≤ 2^k` — the missing poly≤exp connective (from mathlib's
  `tendsto_pow_const_div_const_pow_of_one_lt`).
- **`sep_of_uniform_measure (C K)`** — machine-checks that a SINGLE uniform bound
  `hmeas : ∀ near-critical k ≥ K, 3^k ≤ (2^m−3^k)·k^C`, plus the crossover `hK : ∀ k≥K, k^(3C)≤2^k`
  (dischargeable by `poly_le_two_pow`) and a finite check `hfin` on `6 ≤ k < K`, yields `sep_two_three`
  for EVERY near-critical `k ≥ 6`. So everything between the standard Gelfond object and the crux is
  now elementary and machine-checked at the *uniform-measure* level (complementing the earlier
  per-`k` `sep_of_measure` and bracket-level `sep_of_bracket_sharp`).

**Concrete next attack (in priority order):**
1. ✅ **DONE this lap — `hfin` discharged.** `sep_two_three_finite_check` (`native_decide`, ~7s) +
   `sep_two_three_small` prove `sep_two_three` outright for near-critical `6 ≤ k < 130` (m-range
   bounded by `2^m < 2·3^129 < 2^208`). This is the `hfin` input of `sep_of_uniform_measure` for
   `K = 130`, which pairs with any measure exponent `C ≤ 6` (then `k^(3C) ≤ k^18 ≤ 2^k` for `k ≥ 130`).
   ⟹ The ENTIRE residual of `sep_two_three` beyond elementary/finite parts is now the **single uniform
   Gelfond measure** `hmeas : ∀ near-critical k ≥ 130, 3^k ≤ (2^m−3^k)·k^6`. Axioms: trust base +
   native_decide artifact 🟢. (One loose end for a fully-concrete end-to-end corollary: a *concrete*
   crossover `∀ k ≥ 130, k^18 ≤ 2^k` — `poly_le_two_pow` gives only an existential threshold; the
   induction step `(k+1)^18 ≤ 2·k^18` is a degree-18 nlinarith, deferred as low-value plumbing.)
2. **Build the Gelfond/hypergeometric core toward `hmeas` (the true GO grind).** The formalizable entry point is Padé
   approximation to `(1−z)^ν` / the interpolation-determinant estimate; port the smallest sufficient
   piece. This is the true GO grind — genuinely multi-lap but 🟡, not 🟠.
3. Fallback (BASELINE, not gate-clearing): cite Gelfond/Bennett–Bugeaud as a narrow,
   provenance-documented axiom `gelfond_two_three_measure` in `Assumed/`, feeding `hmeas`.

**Sources:** Bennett–Bugeaud, Acta Arith. 155 (2012) 259–269 (`personal.math.ubc.ca/~bennett/BeBu.pdf`);
Bugeaud, *Linear Forms in Logarithms and Applications* §3.1; Gelfond (1935).

---

## ★ LAP 2026-08-25-1730 — crux narrowed to the textbook Baker linear form ★

**Advance (kernel-checked, NO new axiom):** added `sep_of_linear_form` to
`CollatzMoonshot/FrontA/PowSeparation.lean`, proving sorry-free that the deep obligation
`sep_two_three` (`3^(3k) ≤ (2^m−3^k)^3·2^k`) follows from the **standard** linear-forms-in-logs
lower bound
> `linear_form_lower_log23`:  `Real.exp(−(k/3)·log 2) ≤ (m:ℝ)·log 2 − (k:ℝ)·log 3`  (near-critical `k≥6`),
i.e. `Λ := |m·log 2 − k·log 3| ≥ 2^(−k/3)`.  The bridge is pure analysis: write
`D = 2^m−3^k = 3^k·(e^Λ−1) ≥ 3^k·Λ ≥ 3^k·2^(−k/3)` (using `e^Λ−1 ≥ Λ` and `2^k=e^{k log2}`),
cube, multiply by `2^k`; the LHS collapses to `3^(3k)` exactly.  So **everything between the
classical Baker object `Λ` and the two-block crux is now machine-checked**; the sole remaining deep
input is pinned to the textbook β=1/3 effective bound `Λ ≥ 2^(−k/3)`.

**Second narrowing (same lap, pure ℕ, no reals):** `sep_of_measure (k m C)` proves
`sep_two_three` from the *integer* irrationality-measure `3^k ≤ (2^m−3^k)·k^C` plus the elementary
`k^(3C) ≤ 2^k`, fully general in `C` (no committed constant), via a one-line cube.  So the deep
obligation is now pinned TWO equivalent ways: the real linear form `Λ ≥ 2^(−k/3)`, or the classical
Diophantine `|log₂3 − m/k| ≥ c/k^(C+1)` (finite irrationality measure of `log₂3`).

**Mathlib-gap finding (this lap):** `Mathlib/Algebra/ContinuedFractions/Computation/`
provides only convergence UPPER bounds (`of_convergence`), NOT the best-approximation LOWER bound
`‖kθ‖ ≥ ‖qₙθ‖`; and `LiouvilleWith`/`Measure.lean` give only a.e./generic results, no effective
irrationality measure for a specific number like `log₂3`.  So both routes' deep input must be
built from scratch (CF best-approx lower bound + effective partial-quotient control ⇒ Baker) or
cited.  The CF route's convergents ARE decidable integer facts `2^a ⋛ 3^b`, but bounding all
partial quotients forever is the effective-measure (Baker) content.

**CF-route foundation stones landed (sorry-free, trust base):**
- `irrational_logb_two_three : Irrational (Real.logb 2 3)` — mathlib lacks it; the unavoidable
  first lemma of any CF/effective-measure argument (rational ⇒ `2^a=3^b`, impossible).
- `lt_logb_two_three_iff (a b) : a/b < logb 2 3 ↔ 2^a < 3^b` and companion
  `logb_two_three_lt_iff : logb 2 3 < a/b ↔ 3^b < 2^a` — the workhorse bridge letting every
  CF convergent/semiconvergent inequality for `log₂3` be discharged by `decide`/`norm_num` on ℕ,
  with no real analysis in the loop.
- `denom_ge_of_between` (pure ℤ) — unimodular `a/b<p/k<c/d`, `b·c=a·d+1` ⇒ `k≥b+d`.
- `theta_dist_lower` (ℝ) — the best-approximation LOWER bound: for a unimodular bracket
  `a/b<θ<c/d`, any `p/k` with `1≤k<b+d` has `|θ−p/k| ≥ min(θ−a/b, c/d−θ)`.  **The `‖kθ‖≥‖qₙθ‖`
  engine is now built** (mathlib omits it).

  **Remaining (Baker content):** iterate `theta_dist_lower` over a sequence of unimodular brackets
  of `θ=log₂3` (convergents), each verified by `lt_logb_two_three_iff`/`logb_two_three_lt_iff` as
  `decide`-able `2^a⋛3^b` facts.  The effective *polynomial* measure needs the bracket denominators
  (convergent `q_n`) to grow controlled — i.e. partial quotients of `log₂3` polynomially bounded.
  The elementary `|2^p−3^q|≥1` gives only the Liouville-quality `q_{n+1}≲3^{q_n}` (base-3), too weak
  for the base-`2^{1/3}` threshold `2^{−k/3}`; the polynomial bound is the irreducible Baker step.
  Next lap: assemble the convergent recurrence `q_{n+1}=a_{n+1}q_n+q_{n-1}` and reduce the whole
  measure to the single clean hypothesis `a_{n+1} ≤ q_n^{C}` (polynomial partial quotients).
- `linForm_dist_lower` — scaled bound `|kθ−p| ≥ k·min-gap`, the linear-form form the pipeline uses.
- `linear_form_eq_logb` / `sep_of_logb_gap` — connect distance-to-θ to the linear form `Λ` and to sep.
- `convergent_det_step` / `convergent_denom_grow` — unimodularity + denominator growth along the CF.
- **`sep_of_bracket` (CAPSTONE, sorry-free):** for near-critical `(k,m)`, ANY unimodular bracket
  `a/b<log₂3<c/d` straddling `k` (`k<b+d`) whose scaled gap clears `2^(−k/3)` gives the full
  separation `3^(3k)≤(2^m−3^k)^3·2^k`.  **The crux is now reduced to producing, for each near-critical
  `k`, one convergent bracket of `log₂3` with a good-enough gap** — the effective separation at
  convergent denominators = the irreducible Baker core (base-3 elementary bound `|2^p−3^q|≥1` gives
  only `‖q_nθ‖≥c·3^{−q_n}`; the needed base-`2^{1/3}` improvement is exactly Baker for `log₂3`).
  This is the minimal, precisely-pinned deep input; a cited Baker/linear-forms axiom stays BASELINE.

**Sharp best-approximation bound — DONE** (`theta_dist_lower_sharp`): `|kθ−p| ≥ min(bθ−a, c−dθ)`,
a factor `b`/`d` sharper than the min-gap version, the tight `‖q_nθ‖`-quality bound (equality at
`k=b,p=a`).  Proof via the pure-ring identity `kθ−p = (kc−pd)(bθ−a)+(ka−pb)(c−dθ)` + `denom_ge`.

**Corrected diagnosis (2026-08-25):** the `k=15` "failure" is NOT an engine defect — it is a
finite-range artifact.  `sep_two_three` is *decidable per `k`*, so small `k` are `native_decide`
checks (`sep_two_three_below_500` already verifies every `k<500`, both here and via Aristotle).  The
CF/best-approximation route is the **large-`k`** tool: for large `k` the threshold `2^(−k/3)` is
super-tiny, and the floor `‖q_nθ‖·log2 ≥ 2^(−k/3)` (at `k≈q_{n+1}`, `‖q_{n+1}θ‖≈1/q_{n+2}`) reduces
to `q_{n+2} ≲ 2^{q_{n+1}/3}`, i.e. **sub-exponential partial quotients `a_{n+1} ≲ 2^{q_n/3}`** — the
sole irreducible Baker content.  (Elementary `|2^p−3^q|≥1` gives only `a_{n+1} ≲ 3^{q_n}`, base-3,
short of base-`2^{1/3}`; that exponential gap is Baker.)

**Structure of the finished proof (for a future lap that ports/proves the Baker input):**
`sep_two_three` = (finite `native_decide` for `6≤k≤K₀`) ∪ (for `k>K₀`: pick the convergent bracket
`(q_n,q_{n+1})` straddling `k`, apply `theta_dist_lower_sharp` + `sep_of_bracket`, with the gap
clearing the threshold *because* `a_{n+1} ≲ 2^{q_n/3}`).  Remaining to build: (i) the `log₂3`
convergent sequence as `native`-verified `2^a⋛3^b` data with the recurrence (`convergent_det_step`
gives unimodularity), (ii) the "straddling convergent exists" selection lemma, (iii) the Baker
partial-quotient bound (cite = BASELINE; prove = GO).

`sep_two_three` itself is deliberately LEFT as the disclosed `sorry` (ledger stays honest: an open
sorry, not a hidden axiom) — `bd_reduction` still consumes it unchanged, full build green (8752).

**Next attack on `linear_form_lower_log23`:** this is the classical effective irrationality of
`log₂3`.  Concrete routes: (a) continued-fraction best-approximation `‖kθ‖ ≥ 1/(q_{n+1}+q_n)` for
`θ=log₂3` — its convergents are decidable integer facts `2^a ⋛ 3^b`, but bounding all partial
quotients forever needs an effective measure (Baker); (b) a hypergeometric/Padé construction giving
a Liouville-then-improved bound; (c) Aristotle (job `7a593ec3`, isolated pure-ℕ `sep_two_three`,
submitted this lap — verify `#print axioms` if it returns).  A cited Baker axiom stays BASELINE.

## ★ IN PROGRESS: paradoxical finite trajectories (2026-08-24) ★

Executing `FRONT-A-PARADOXICAL.md`. `experiments/paradoxical.py` (exact integers) +
`CollatzMoonshot/FrontA/Paradoxical.lean` (trust-base clean, full build green 8750).

**Landed (sorry-free):**
- Source lock: iterate identity, `numer` defs, criterion (P), slack (S), `7→8` — all exact.
- `slack_identity`, `paradoxical_criterion`, `acyclicParadoxical_criterion`: endpoint `n≤y`
  ⟺ pure word inequality `d·n ≤ numer`.
- `numer_singleBlock = 2^s(3^q−2^q)`, `numer_twoBlock = 3^d(3^b−2^b)+2^(b+c)(3^d−2^d)` via a
  ℤ true-prefix recursion.
- **`headBlock_not_acyclicParadoxical` = Rozier–Terracol Appendix A, now formal.** The pure
  head block `[T]^q[F]^t` is never acyclic paradoxical, from `2^m y + 2^q = 3^q(n+1)` and
  `3^q<2^m` ⇒ `y ≤ n`. Needs NO residue bound.

**Discovery (experiment, exhaustive):** every acyclic paradoxical word has **≥3 odd blocks**
(all ≤2-block front-normalized words to length 30; two-block to 38 — zero paradoxical). Ratios
`5/8,17/27,29/46` (n≤200000) are all left convergents/semiconvergents of `log_3 2` (Niu,
no counterexample in range).

**Part C wiring landed (`CollatzMoonshot/Assumed/Paradoxical.lean`):**
- `Assumed.rozier_terracol_3_2` — RT Theorem 3.2 as a faithful THEOREM-grade axiom
  (infinite shortcut stopping time ⇒ infinitely many `Paradoxical` segments; NOT packaging
  `NoDivergentOrbit`).
- `finite_acyclicParadoxical_imp_noDivergent : FiniteAcyclicParadoxical → NoDivergentOrbit`,
  proved modulo one disclosed bridge `diverges_imp_infinite_acyclicParadoxical` (the
  standard/shortcut + acyclicity specialization). Ledger `[propext, sorryAx]`. This is BASELINE
  Front-A plumbing (the hypothesis is stronger than Collatz), not the novel content.

**Part C COMPLETE (modulo the one cited axiom).** `finite_acyclicParadoxical_imp_noDivergent`
`#print axioms` = `[propext, Classical.choice, Quot.sound, rozier_terracol_3_2]` — NO `sorryAx`.
The full consumption chain is machine-checked: `diverges_imp_infinite_acyclicParadoxical`
(running-min `exists_standardStop_of_diverges` + shortcut embedding
`tstep_iterate_eq_step_iterate`/`infiniteStoppingTime_of_diverges` + acyclicity
`not_tstep_fixed_of_diverges` via the standard↔shortcut peak invariant `step_le_shortcut`,
plus `diverges_two_pow_mul`/`step_iterate_two_pow_mul`). RT axiom is the faithful constructive
form `∀ K, ∃ k m, K < 2^k·n ∧ Paradoxical (2^k·n) m`.

**Only remaining open obligation on this front:** `le_two_blocks_not_acyclicParadoxical`.

**DECOMPOSED + Case A PROVED (lap 2026-08-25-0400).** The proof now splits the itinerary at
step `b+c` into two head-block segments (`traceWord_add` + `List.append_inj`), and case-splits
on which block is subcritical. Whole-word subcriticality `3^(b+d)<2^m` forbids both blocks
supercritical. Three cases:
- **Case A (both subcritical): PROVED, sorry-free.** `headBlock_endpoint_le` twice ⇒
  `y ≤ X ≤ n`. No residue needed. (`X := tstep^[b+c] n`.)
- **Case B (first super, second sub) / Case C (first sub, second super): 2 disclosed sorries.**
  Single-block bound closes one side (`y≤X` in B, `X≤n` in C) but NOT `y≤n`.

**The residue core (what B and C both reduce to).** Set `n+1 = 2^b w₁` (w₁ odd, from
`headBlock_dvd_succ`), interior odd `X = x_{b+c}` with `X+1 = 2^d w₂`, endpoint `2^e y =
3^d w₂ − 1`. The single relation linking them is
  **(★)  `3^b w₁ = 2^(c+d) w₂ − 2^c + 1`**  (from `3^b w₁ − 1 = 2^c X = 2^c(2^d w₂ − 1)`).
`y ≤ n` is then *equivalent* to either of the dual bounds (both ⟺ criterion (P)):
  **GOAL'  `(2^m − 3^(b+d))·w₁ ≥ 3^d·2^c − 3^d + 2^(c+d)(2^e − 1)`**
  **GOAL2' `(2^m − 3^(b+d))·w₂ ≥ 3^b·2^e − 3^b + 2^(b+e)(2^c − 1)`**.
The obstruction: `w₁ ≥ 1` (equiv `w₂ ≥ (3^b+2^c−1)/2^(c+d)`) is INSUFFICIENT — verified: for
`b=2,c=1,d=1,e=1` (barely subcritical 27<32, d_def=5) GOAL2' needs `w₂ ≥ 4` but `w₁≥1` only
forces `w₂ ≥ 3`; the true minimum `w₂=7` comes from the **3-adic congruence** `2^(c+d) w₂ ≡
2^c−1 (mod 3^b)` (unique class since `gcd(2,3)=1`). Same for Case C (`b=1,c=1,d=2,e=1`:
needs `w₁≥4`, forced by min `w₂=2`). So the crux = **the minimal `w₂` in its residue class mod
`3^b` satisfies GOAL2'** — a genuine joint 2-adic/3-adic statement. Monotonicity note: larger
realizing `n` in the class only make `y−n` MORE negative (`Δ(y−n)=−d_def` per `+2^m`), so it
suffices to prove GOAL2' at the class-minimal `w₂`.

### DONE (lap 2026-08-25-0500): reduced to ONE self-contained core + big elementary insight

**`two_block_residue_core` (LANDED, `FrontA/Paradoxical.lean` ~line 300, the SOLE `src/`
sorry).** Purely-ℕ statement: given the two exact segment identities
  `hI : 2^(b+c)·X + 2^b = 3^b·(n+1)`,  `hII : 2^(d+e)·y + 2^d = 3^d·(X+1)`,
`3^(b+d) < 2^m`, `n > 2`, then `y ≤ n`. Equivalent to the two-block claim (identities encode
the realizing residue exactly). Both B and C route through it; Case A stays sorry-free.
Validated on 1893 exact solutions. Submitted to **Aristotle** (project
`4006e40e-9588-4e7a-979e-ab1c7586cda8`) — verify any returned proof with `#print axioms`.

**KEY INSIGHT — the contrapositive lever (∗∗) closes ~99.7% ELEMENTARILY (no integrality).**
Assume `y ≥ n+1`. Using hI, hII as *equalities* (substitute `X+1 = (3^b(n+1)+2^b(2^c−1))/2^(b+c)`
into `3^d(X+1) ≥ 2^(d+e)(n+1)+2^d`) gives the exact upper bound
  **(∗∗)  `d_def·w₁ ≤ 3^d(2^c−1) − 2^(c+d)  =: U₁`**  (`n+1 = 2^b w₁`, `d_def = 2^m − 3^(b+d)`).
Meanwhile `w₂ ≥ 1` (from `2^d ∣ X+1`, `X ≥ 1`) gives via (★) the lower bound
  **`3^b·w₁ ≥ 2^(c+d) − 2^c + 1 =: L`**.
These CONTRADICT (⇒ `y ≤ n`) whenever  **`d_def·L > 3^b·U₁`  [NEEDED2]**. Brute-force
(`scratchpad/needed2.py`, all subcritical `b,d∈[1,8], c,e∈[0,8]`, 3803 configs): **NEEDED2
holds for 3791; only 12 fail** — `(b,c,d,e) ∈ {(2,2,3,1),(2,3,3,0),(3,2,2,1),(3,3,2,0),
(4,2,1,1),(4,3,1,0),(7,4,1,1),(7,5,1,0),(8,3,2,3),(8,4,2,2), …}`. So the residue/integrality
force is needed ONLY on this thin residual set (small `e`, moderate `b`, `U₁` large & positive).

**Residual growth (checked `scratchpad/kgrow.py`, `b,d<16`, `c,e<16`, 56 residual configs):**
the min-`w₂` bound `k` needed on the residual GROWS with `b` (2→3→4 up to `b=15`), so a fixed
finite `w₂ ≥ K` will NOT close it — the residual genuinely needs a least-residue bound. BUT
`w₂ = 1` is **never** a valid solution on the residual (0/56), consistent with `k ≥ 2` there.
The exact identity behind (∗∗): `2^m·y + 2^(b+c+d) = 3^(b+d)(n+1) + 3^d·2^b(2^c−1)` (MAIN).

**DONE (lap 2026-08-25-0600): `core_of_gap` LANDED sorry-free.** The elementary regime is
proved exactly as planned (MAIN via `linear_combination 3^d·hI + 2^b·2^c·hII`, `X ≥ 2^d−1`
from `2^d ∣ X+1`, UP/LOW chained + `2^b`-cancelled to contradict the gap; all exponents
normalized to atoms `{2^b,2^c,2^d,2^e,3^b,3^d}` via `simp only [pow_add]`; needs
`maxHeartbeats 1200000`). `two_block_residue_core` now `by_cases` on the gap → `core_of_gap`
(elementary, ~99%) or the residual `sorry`. **The residual is the SOLE remaining `src/` sorry.**

**DONE (lap 2026-08-25-0700): SHARPENED to the integer-ceiling gap → residual = exactly 2
configs.** `core_of_gap` now takes a division-free forall-form gap
`∀ w, 2^(c+d)-2^c+1 ≤ 3^b·w → U₁ < D·w` and instantiates it at the TRUE `w₁`
(`3^b·w₁ = 2^c·X+1`, `2^b ∣ n+1`). Using the integer `w₁` (vs real `t/3^b`) makes the gap
hold for EVERY subcritical `(b,c,d,e)` except exactly `(2,3,3,0)` and `(3,3,2,0)` (checked
`b,c,d,e<34`, `scratchpad/bigcheck.py`). Both proved closable by `omega`
(`residue_core_exc1/2`). **SOLE remaining `src/` sorry = the finiteness CONTAINMENT**
`¬gap ∧ U₁>0 → (b,c,d,e) ∈ {(2,3,3,0),(3,3,2,0)}`; then the residual branch closes by
`exact residue_core_exc1/2`.

**DONE (lap 2026-08-25-0830): crux decomposed into `near_critical_containment` + squeeze PROVED
sorry-free.** The opaque residual `sorry` inside `two_block_residue_core` is gone; that branch now
`push_neg`s `¬gap` to a witness `w` (`L ≤ 3^b·w`, `D·w ≤ U₁`) and calls the new self-contained
lemma `near_critical_containment (b c d e w …)`, then `residue_core_exc1/2`. Inside the new lemma
the **elementary squeeze is proved sorry-free**: from the two bounds (×D, ×3^b, cancel 2^c>0) we
get the division-free near-critical window `(2^m − 3^(b+d))·(2^d − 1) < 3^(b+d)` [`hsqueeze`] plus
the real bound `D·L ≤ 3^b·U₁`. The SOLE `src/` sorry is now `near_critical_containment:461` — the
finiteness *containment* with clean hyps `{hsub, hlo, hhi, hsqueeze}` (much more attackable).
Verified (`scratchpad/squeeze.py`, `<45`): tuples admitting such a `w` = exactly `(2,3,3,0)`,`(3,3,2,0)`.

**Why the window alone is infinite (why integrality is essential):** `hsqueeze` squeezes
`2^m/3^(b+d) ∈ (1, 2^d/(2^d−1))`, width `→1` as `d↑`; the real bound `D·L ≤ 3^b·U₁` fails on 883+
tuples with UNBOUNDED `b,e` (`scratchpad/contain.py`, LIM=60). Finiteness comes only from
`w ∈ ℕ` (`⌈L/3^b⌉ ≤ U₁/D`): a `3^b mod 2^(c+d)` least-residue growth = a `2^m` vs `3^k` separation
(effective irrationality of `log₂3`). Note both winning tuples sit on the SAME best approximation
`2^8/3^5` (b+d=5, m=8). Next: bound `b+d` via an explicit `|2^m−3^k|` separation (Baker-type,
likely a cited effective-irrationality lemma) → `interval_cases` + `decide` on the finite box.

**DONE (lap 2026-08-25-0900): REFUTED attack #1 + proved the clean power bracket.** Exhaustive
scan (`scratchpad/dbig.py`, `b+d ≤ 306`) shows the real-bound set `{D·L ≤ 3^b·U₁}` is infinite in
EVERY parameter: `d` grows to `9` (first at `b+d = 306`, tracking CF denominators of `log₂3`:
`k = 5,17,29,41,147,253,306` for `d = 3..9`); `b,c,e` unbounded. ⇒ **attack #1 (bound `b+d` via
ceiling-discreteness + the real bound) is DEAD**; the integrality `⌈L/3^b⌉ ≤ U₁/D` is strictly
essential. Also proved sorry-free the clean power bracket `hbracket : 2^m·(2^d−1) < 3^(b+d)·2^d`
(inside `near_critical_containment`), i.e. `2^m/3^(b+d) ∈ (1, 2^d/(2^d−1))` with `hsub`. The sole
`src/` sorry is unchanged in location (`near_critical_containment:418`) but its target is now the
sharp separation: a `2^m` vs `3^k` window that ONLY integrality closes.

**DONE (lap 2026-08-25-0930): dimension reduction — `window_unique_m` (sorry-free) + tight bracket.**
Proved sorry-free `window_unique_m`: the near-critical window `(3^k, 3^k·2^d/(2^d−1))` contains
**at most one** power of 2 (from `2^d ≤ 2(2^d−1)` for `d≥1` ⇒ `2^m < 2·3^k`, then `2·3^k < 2^(m'+1)`).
So `m` is a *function of* `(b,d)` — collapsing the containment search `(b,d,m) → (b,d)`, a reduction
ANY attack reuses. Also added to `near_critical_containment`'s context the tight two-sided bracket
`hupper : 2^m < 2·3^(b+d)` (with `hsub`: `3^(b+d) < 2^m < 2·3^(b+d)`). Mathlib confirmed to have NO
effective irrationality of `log₂3` / Baker / linear-forms-in-logs (only `LiouvilleWith` framework,
no specific measure) — so route (a) needs building that infrastructure, genuinely multi-lap.

**DONE (lap 2026-08-25-1000): CRUX REDUCED TO ONE INEQUALITY `b + d ≤ 5`.** The sole `src/` sorry
is now literally `have hbd : b + d ≤ 5 := by sorry` inside `near_critical_containment`. Everything
else is machine-checked: given `b+d ≤ 5`, the window `hupper` forces `2^m < 2·3^5 < 2^9` ⇒ `m ≤ 8`,
bounding `b,c,d,e` to a finite box; then `interval_cases b<;>d<;>c<;>e <;> norm_num <;> omega`
discharges every case (the integrality constraints `hlo/hhi` are inconsistent off the two tuples,
and true on them). Verified (`scratchpad/small.py`): under `b+d ≤ 5` the containment solutions are
exactly `(2,3,3,0)`,`(3,3,2,0)`. Needs `maxHeartbeats 4000000` (~800 finite cases). So the two-block
exclusion `le_two_blocks_not_acyclicParadoxical` is now PROVED modulo the single clean statement
`b + d ≤ 5` — the pure `2^m` vs `3^k` separation (effective irrationality of `log₂3`, Baker).

**★ REFUTED (review lap 2026-08-25-1500): the "elementary A/B route" for `b+d ≤ 5` is DEAD.**
The MAJOR LEAD below (2026-08-25-1230) conjectured `¬A ∧ ¬B ∧ subcritical ∧ U₁>0 ∧ b,d≥1 ⟹
b+d ≤ 5` closes ELEMENTARILY (nlinarith over the exponent atoms). The implication IS true over
integer powers (re-confirmed to `g=b+d ≤ 200`, exactly 4 pairs `(b,d)∈{(2,1),(2,3),(3,2),(4,1)}`),
but it is **NOT provable by any `nlinarith`/polynomial certificate**, because such a certificate is
a Positivstellensatz combination valid for all REAL atom values, and the **REAL RELAXATION is
FEASIBLE at unbounded `g`.** Fully-checked witness (`experiments/two_block_relaxation.py`, exact
rationals) at `b=18, d=23` (`g=41`): real `C=2^c ≈ 8.3·10⁶`, `V=2^m ≈ 3.647·10¹⁹` satisfy ALL of
`{subcrit, ¬A, ¬B, U₁, lever 2^m ≥ 2^(b+d)·2^c, couplings 3^(3d)≤2^(5d) & 3^(3b)≤2^(5b), size
2^g≥64 & 3^g≥729}`; feasible at every even `g∈[6,60]`. Confirmed in-Lean: the coupling `have`s all
compile, `nlinarith` (with the full curated hint set) fails as predicted (`linarith failed`).
**Why real-feasible but integer-empty:** the window `2^m/3^g ∈ (1, 2^d/(2^d−1))` has width `2^-d`;
an integer solution needs a power of 2 within `~2^-d` of `3^g`, i.e. `|m·log2 − g·log3|` tiny — an
effective irrationality of `log₂3` (Baker) lower bound. At `g=41` the closest is `2^65/3^41≈1.0117`,
far outside the `~2^-23` window; only at `g=5` (`2^8/3^5≈1.0535`, small-`d` wide window `≤8/7`) does
a power fit. **Diagnosis (final): `b+d ≤ 5` is genuinely Baker-grade** — matches Aristotle's
independent linear-forms-in-logs verdict and the earlier `dbig.py` "real bound infinite" finding.
The prior lead's error: conflating "true over integer powers" (integrality-forced) with "nlinarith-
provable" (needs a real certificate). **DO NOT re-attempt an elementary `nlinarith`/`omega` bound on
`b+d ≤ 5`, nor the `le_of_gap_A/B` + `¬A∧¬B⇒b+d≤5` plan below — refuted.**

### ★ DONE (lap 2026-08-25-1600): crux DECOMPOSED — reduction PROVED, one clean sorry isolated ★
The bare `have hbd : b+d ≤ 5 := sorry` is GONE. New module `CollatzMoonshot/FrontA/PowSeparation.lean`
proves sorry-free: `grow_two_three` (3^(k+2)≤2^(2k−3) for k≥15, induction), `finite_two_block_check`
(6≤k≤14 residue, `native_decide`), and `bd_reduction` (the β=1/3 reduction: window + (W) + (A) +
`sep_two_three` ⇒ k≤5). In `near_critical_containment`, `hbd` now derives `(W) 2^d·(2^m−3^k)<2^m`
(from `hbracket`) and `(A) (2^m−3^k)·2^k ≤ 2^m·3^d` (from ¬A `D≤3^d·2^c` via `hhi`/`w≥1`/`hU1lt`,
plus `2^c ≤ 2^(c+e)`), then calls `bd_reduction`. Build 🟢 8752 jobs. **The SOLE remaining `src/`
sorry is now `sep_two_three`** — the clean, weak, TRUE separation `3^(3k) ≤ (2^m−3^k)^3·2^k`
(β=1/3) for near-critical k≥6. Axiom audit: `le_two_blocks_not_acyclicParadoxical` =
`[propext, sorryAx (=sep_two_three), Classical.choice, Quot.sound, finite_two_block_check native_decide
ax]` (the native_decide artifact is 🟢 finite). **NEXT = discharge `sep_two_three`** (the GO prize)
via mathlib CF convergent bounds for `log₂3`; see scoping below.

### ★ GO ROUTE FULLY SCOPED (review lap 2026-08-25-1500) — the exact minimal effective input ★

The crux `b+d ≤ 5` closes from a WEAK separation bound (far weaker than full Baker) plus a finite
check plus an elementary reduction. All three parts verified numerically
(`experiments/two_block_relaxation.py` + scratch `beta38.py`,`binding.py`,`sep.py`).

**The reduction chain (elementary; formalizable now):** at `Paradoxical.lean:515`, set `k=b+d`,
`D=2^m−3^k` (`m=b+c+d+e`). Already proved sorry-free in context: `window_unique_m` (⇒ `m` is the
UNIQUE power in `(3^k, 2·3^k)`), `hupper : 2^m < 2·3^k`, `hbracket : 2^m(2^d−1)<3^k·2^d`. Two clean
facts follow:
  - **(W)** `2^d·D < 2^m`   (from `hbracket`; ⇒ `2^d·D < 2·3^k`).
  - **(A)** `D·2^k ≤ 2^m·3^d`  (¬A `D ≤ 2^c·3^d` + `2^c ≤ 2^(c+e)=2^(m−k)` since `e≥0`;
    ⇒ `D·2^k < 2·3^(k+d)`).
`(W) ∧ (A) ∧ near-critical` is REAL-consistent (that is why the elementary route died), so the
integrality of `2^m` (nearest power to `3^k`) is essential and enters ONLY via:

**The separation lemma (THE disclosed effective input; β = 3/8, integer form):**
  `∀ k m, 6 ≤ k → 3^k < 2^m → 2^m < 2·3^k → (2^m − 3^k)^8 · 2^(3k) ≥ 3^(8k)`.
Equivalent to `D ≥ 3^k·2^(−3k/8)`. VERIFIED true for all near-critical `6 ≤ k < 500` (min `D/3^k`
is `0.001` at `k=306`, hugely above `2^(−3k/8)`). β=3/8 is inside the feasible window
`[0.319, 0.387)`: β≥0.319 needed for the bound to be TRUE (worst at `k=10`), β<log2/log6=0.3869
needed for the reduction (asymptotic). NOTE: with β=3/8 the loose reduction only yields `k ≤ 83`
(constants), so it must be paired with:

**Finite check (native_decide) for `k ∈ [6, 83]`:** for each such `k`, the near-critical `m` and
`D` are concrete; `¬((W) ∧ (A))` holds (verified). ~78 values; `3^83`≈40 digits — `native_decide`
on a per-k table should handle it (or `interval_cases k` + `decide`/`omega` with the explicit `m`).

**So the crux = [reduction: elementary, formalize] + [separation lemma: β=3/8, DISCLOSED] +
[finite check k≤83: native_decide].** Everything except the separation lemma is machine-reachable now.

**Proving the separation lemma (the multi-lap GO prize):** mathlib HAS the continued-fraction
convergent-bound API — `Mathlib/Algebra/ContinuedFractions/` (`Determinant.lean` gives
`|pₙqₙ₊₁ − pₙ₊₁qₙ| = 1`, `ContinuantsRecurrence.lean`, `ConvergentsEquiv.lean`), the standard tool
for effective `|α − pₙ/qₙ| ≥ 1/(qₙ(qₙ+qₙ₊₁))` lower bounds. It has NO ready-made effective
irrationality measure for `log₂3` (only the `LiouvilleWith` framework + a.e. results, no specific
constant). Route: realize the relation `|k·log3 − m·log2|` as a CF-convergent gap for `log₂3` (or
`log₃2`), extract an explicit lower bound `≥ c·2^(−3k/8)` (β=3/8 is weak, so even a crude convergent
argument with a computed initial segment of the CF `[1;1,1,2,2,3,1,5,2,23,...]` of `log₂3` should
suffice), yielding the separation. This is the genuine effective-irrationality build; narrow it lap
by lap. Discharging it → `b+d≤5` is real-proved → PROMISING EVIDENCE → GO.

**Remaining honest routes for the crux (both leave everything else machine-checked):**
- **(a) GO route — build effective irrationality of `log₂3` in Lean.** An explicit linear-forms-in-
  logs / irrationality-measure bound `|2^m − 3^k| ≥ 3^k · c/k^κ` (or a direct `|m log2 − k log3|`
  gap) discharges the window ⇒ `b+d ≤ 5` ⇒ the sorry becomes a real proof. Mathlib LACKS this
  (only `LiouvilleWith`, no specific effective measure for `log₂3`). Genuinely multi-lap; THIS is
  the GO prize. Narrow it lap by lap (see below).
- **(b) BASELINE route — cite a narrow effective-gap axiom** (like `rozier_terracol_3_2`), stated
  as `∀ m k, k ≥ 6 → <explicit gap>`, and derive `b+d ≤ 5`. Auditable, keeps the classification at
  BASELINE for this step. Per DIRECTION, do NOT do this merely to clear the src-sorry gate.

--- superseded lead (kept for provenance) ---
**MAJOR LEAD (lap 2026-08-25-1230): `b+d ≤ 5` may be ELEMENTARY via Aristotle's own criteria A/B.**
Aristotle proved (sorry-free) two ELEMENTARY sufficient conditions for `y ≤ n`:
  A: `3^(b+d) + 2^c·3^d < 2^m`   B: `(2^m − 3^(b+d))·(2^d − 1) ≥ 3^b·(3^d − 2^d)`
then declared the residual `¬A ∧ ¬B` needs Baker. The lead observed `¬A∧¬B∧subcrit∧U₁>0∧b,d≥1
⟹ b+d≤5` holds over integer powers with zero exceptions and hoped nlinarith could prove it.
**REFUTED above** — the real relaxation is feasible at unbounded `g`, so no nlinarith certificate
exists; the integer-truth is Baker-forced. Next was going to be: (1) `le_of_gap_A/B`; (2) the
elementary `⇒ b+d≤5`; (3) route through A∨B∨finite. All void.

**INDEPENDENT CORROBORATION (Aristotle, job `4006e40e…`, COMPLETE_WITH_ERRORS, ~1h30m).** Handed
the `two_block_residue_core` statement, Aristotle independently reproduced the ENTIRE reduction and
hit the identical wall — strong faithfulness evidence for our reduction:
- It proved (sorry-free) the same criteria: `key_identity` (eliminating `X`), the forced
  divisibilities, criterion A (`3^(b+d)+2^c·3^d < 2^m ⇒ y≤n`), criterion B (= our `hsqueeze`
  region, subtraction-free), and "neither block expands ⇒ y≤X≤n" (= our Case A). Its
  `two_block_residue_core` is a sorry-free case split onto A ∨ B ∨ C leaving ONE residual lemma.
- Its residual (`le_in_residual_region`) is EXACTLY ours: it states the conclusion as
  `D·w₁ ≥ 3^d(2^c−1) + 2^(c+d)(2^e−1)` and concludes it "is an effective lower bound for the
  linear form `|m·log2 − g·log3|` (Baker-type); … no effective theory of linear forms in
  logarithms is available in Mathlib." Matches our `b+d ≤ 5` diagnosis.
- Independent evidence (unverified, exact-int): criteria A/B/C settle all `b,d≤30, c,e≤45` except
  the same ten tuples (all at `2^5>3^3` / `2^8>3^5`); near-equality band `3^g<2^m≤2·3^g` swept to
  `g ≤ 119` with NO failure; 1,353,014 genuine two-block solutions enumerated, NO counterexample.
- **Faithfulness note:** Aristotle reports the hypothesis `2 < n` "appears unnecessary" — worth
  removing `hn` from `two_block_residue_core` on a cleanup lap (minor; does not affect the crux).
Do NOT resubmit (job done, reached the wall). Our 3-adic reframing (below) is a DIFFERENT angle
(`L mod 3^b` via `orderOf 2 mod 3^b`) than Aristotle's log-form view — possibly more mathlib-reachable,
but note the hard set has UNBOUNDED `b,d` (checked to 19/29), so it is a uniform 3-adic theorem, not
a finite `decide`. Both views agree the missing input is genuinely Baker-grade.

**REFRAMED (lap 2026-08-25-1130) — the crux is a 3-adic residue fact, NOT `log₂3` irrationality.**
Exact restatement (containment ⟺ integer `w` in `[⌈L/3^b⌉, U₁/D]`, nonempty since `D·L ≤ 3^b·U₁`
whenever `w` exists): with `t := L mod 3^b` and `r := (−L) mod 3^b = 3^b − t` (for `t>0`),
  **containment ⟺ `D·r ≤ 3^b·U₁ − D·L`**  ⟺  **`D·⌈L/3^b⌉ ≤ U₁`**.
So the b+d≥6 elimination is exactly **`b+d ≥ 6 ⟹ D·⌈L/3^b⌉ > U₁`**, a statement about `L mod 3^b`
(= `(2^c(2^d−1)+1) mod 3^b`, a power-of-2 residue mod `3^b`) — the order of 2 mod `3^b` is the
natural tool, NOT effective irrationality of `log₂3`. Numerics (`scratchpad/reframe.py,tadic.py`):
in the b+d≥6 failure region `r/3^b ∈ [0.971, 1.0]` (mean 0.999, i.e. `L mod 3^b` is tiny) and
`t < D` holds throughout (99/99). CAVEAT: `t < D` also holds for the WINNING `b+d=5` tuples
(e.g. `(2,3,3,0)`: `t=3 < D=13`), so `t<D` is necessary-ish but NOT the discriminator; the flip
at `b+d: 5→6` is genuinely quantitative in `D·⌈L/3^b⌉` vs `U₁`. Next: bound `L mod 3^b` from
below/above in the near-critical regime via `orderOf (2 : ZMod (3^b)) = 2·3^(b-1)` (mathlib HAS
`ZMod`, `orderOf`, and lifting-the-exponent) — a potentially-elementary 3-adic route worth a real
attempt before conceding Baker. This supersedes the "effective irrationality of log₂3" framing.

**REFUTED (lap 2026-08-25-1030) — three elementary bounds for `b+d ≤ 5`, all fail (do NOT retry):**
Exhaustive scan (`scratchpad/elem.py`,`elem2.py`,`hard.py`, ranges to 80):
- `D > U₁` for `b+d ≥ 6`? NO — `D ≤ U₁` holds for 84914 tuples with `b+d ≥ 6` (`w=1` is feasible).
  So a `|2^m−3^k|` separation *lower bound* on `D` cannot force `b+d ≤ 5`.
- `2D > U₁` (with `⌈L/3^b⌉ ≥ 2`) for `b+d ≥ 6, D ≤ U₁`? NO — 397604 counterexamples; the ceiling is
  often huge (`⌈L/3^b⌉` up to `10^35`), so containment fails by ceiling *size*, not a factor of 2.
- real bound `D·L > 3^b·U₁` for `b+d ≥ 6`? NO — fails on the same infinite strip.
- **Positive structural fact:** for `b+d ≥ 6, subcritical, U₁>0, D ≤ U₁`, the ceiling `⌈L/3^b⌉` is
  NEVER `≤ 3` (0 cases with `ceil ≤ 3`) — it is always `≥ 4` and grows. The hard region (small
  ceiling ≈ near-critical large `b`) is *empty* for `b+d ≥ 6`. This is the cleanest elementary
  handle found; whether `⌈L/3^b⌉·D > U₁` admits an elementary proof from it is the open question.
Net: `b+d ≤ 5` is genuinely the least-residue/Baker content; every one-inequality shortcut is dead.

**Attack on `b + d ≤ 5` (next lap):** This is exactly: for which `(k,d)` (k=b+d≥2, 1≤d<k) does the
near-critical window `3^k < 2^m < 3^k·2^d/(2^d−1)` admit an integer `w` with `L ≤ 3^b w ≤ …`? The
answer (k=5 only) is a linear-form-in-logs bound. Routes: (a) DISCHARGE via building an explicit
irrationality-measure/continued-fraction bound for `log₂3` in Lean (multi-lap; mathlib lacks it) —
this is the GO upgrade; (b) cite an effective `|2^m − 3^k|` gap as a named axiom and derive `b+d≤5`
(BASELINE). Note both winning tuples share `(k,m)=(5,8)`; the CF convergents of `log₂3` giving
`2^m>3^k` closest are at `k = 5,17,29,41,…` and only `k=5` is loose enough for the window+integrality.

**Attack on the containment (superseded):** The remaining obligation is now provably NOT elementary
in `(b,d,m)` alone — it needs effective irrationality of `log₂3` (Baker). Two honest routes:
(a) **discharge attempt**: formalize/derive from an explicit irrationality measure `μ(log₂3)` (or
an explicit `|2^m − 3^k|` gap) that the window `(1, 2^d/(2^d−1))` admits an integer `w` only for
`b+d = 5` — large but real Lean work via mathlib's `Nat.log`/rpow-irrationality API; (b) **cited
route** (BASELINE, like `rozier_terracol_3_2`): state the effective-gap fact as a named axiom and
derive the containment, closing the src sorry into an auditable axiom. GO upgrade requires (a).

**Attack on the containment (superseded — see above):** quantitative near-critical bound. Crude inequalities
only give `2^(m-1) < 3^(b+d) < 2^m` (infinite strip, `c+e ≈ 0.585(b+d)`); the reason only 2
tuples fail is that `⌈t/3^b⌉` grows along the strip — a `3^b mod 2^(c+d)` least-residue fact,
same hardness as before but now a FINITE target. Options:
1. Prove `¬gap → b+d ≤ 5` via ceiling discreteness (`3^b·⌈t/3^b⌉ < t + 3^b`) + a least-residue
   growth bound, then `interval_cases`/`decide`.
2. `ZMod (3^b)` least-residue lemma: min `w₁` with `3^b w₁ ≡ 1-2^c (mod 2^(c+d))` is large.
3. Aristotle (`4006e40e-9588-4e7a-979e-ab1c7586cda8`, ~7% at 32min, same structure numerically)
   — if a clean full-core proof returns, kernel-verify (`#print axioms`) + inline it.

Also (lower priority): extend the ratio census past `41/65` (word-BnB or n≳10^8) to harden the
Niu CF falsification test.

## ★ NEXT: paradoxical finite trajectories (2026-08-24) ★

The parity-reconstruction pull below is complete and classified **BASELINE / RE-SCOPE**.
The next funded mathematical project is `FRONT-A-PARADOXICAL.md`, based on Rozier--Terracol
(Discrete Mathematics 2026) and Niu (arXiv 2026). A paradoxical segment has multiplicative
coefficient `3^q/2^m < 1` but nevertheless ends at or above its start because the exact
additive numerator wins. The literature proves that an infinite-stopping-time orbit creates
infinitely many such finite witnesses. The project must reproduce the known fixed-length
facts, then seek genuinely new restrictions (word shape, continued-fraction ratios, or exact
branch-and-bound pruning). The cited theorem/wiring is BASELINE; finite computation alone is
not a Collatz advance. See the project doc for the strength audit and stop/go bars.

## ★ Parity-reconstruction pull — CLASSIFIED BASELINE / RE-SCOPE (2026-08-24) ★

Executed `FRONT-A-PARITY-RECONSTRUCTION.md` (experiment + Lean kernel + strength audit).
New module `CollatzMoonshot/FrontA/ParityReconstruction.lean` (all trust-base clean
`[propext, Classical.choice, Quot.sound]`, full build green 8749 jobs) and
`experiments/parity_reconstruction.py` (exact, exhaustive to depth 16).

**What was PROVED (Lean, sorry-free):**
- `tstep_iterate_lt` — the **carry invariant**: `tstep^[m] n < 3^(ones(traceWord n m))·(n/2^m+1)`
  for ALL n (strengthened form absorbing the odd step where the naive induction breaks).
- `tstep_iterate_lt_pow_ones` — for `n < 2^m`, `tstep^[m] n < 3^(ones)` (normalized endpoint
  `q/3^a < 1`, tight at all-ones). First such archimedean word↔size theorem in this repo.
- `normalized_endpoint_ne_start_one` — a permanent counterexample to the false claim that
  `q/3^a` stabilizes to the natural start when reconstruction output stabilizes. For `n=1`
  and every positive depth, the denominator-free equality already fails.
- `two_pow_mul_gap` — exact carry-gap identity `2^m(3^a−q) = 3^a(2^m−n) − numer`.
- `pow_ones_mul_le` — matching lower bound `3^a·n ≤ 2^m·tstep^[m] n` (the drift bracket).
- `traceWord_eq_imp_modEq`, `eq_of_forall_traceWord_eq` — residue determinacy (a natural is
  determined by its parity itinerary).
- `tstep_repeat_of_eventually_periodic_parity` + `..._periodic_...` — eventually-periodic
  parity ⇒ the accelerated orbit repeats/is bounded (restricted no-divergence baseline).

**Strength-audit findings (experiment, exhaustive):**
- Exact gap `3^a − q` bottoms out at **1** for every depth ⇒ `q < 3^a` is the SHARPEST
  uniform bound; no depth-independent inequality strictly tighter exists.
- **Bounded-suffix endpoint collision:** at depth 16 two words sharing their last 3 bits
  have `q/3^a` spread `≈ 0.9997`. This proves that the suffix alone neither determines nor
  uniformly approximates the endpoint. It does **not** rule out every finite-state
  Lyapunov certificate, which may prove aggregate transition inequalities.
- **A particular positivity proxy fails:** restricting to words with top output bit zero
  (`r < 2^{m-1}`) still admits odd density `(m−1)/m`, above `log2/log3`. This establishes
  the failure of that proxy, not a universal theorem about every finite-prefix condition.

**CLASSIFICATION: BASELINE / RE-SCOPE (corrected strength audit).**
The exact reconstruction API is complete in Python; Lean contains the load-bearing forward
residue and orbit consequences, not an explicit `R(v)` construction. The certified
depth-independent inequality `q < 3^a` is the known critical envelope, not a divergence
obstruction, and no invariant stronger than eventual-periodicity appeared. The adversarial
pair is a precise endpoint-prediction collision, not a universal finite-state no-go.
**Do not manufacture more routine Lean plumbing on this coordinate.** Move to the finite
paradoxical-window project above, where the same additive numerator is load-bearing and
the outputs are exact, falsifiable structural claims. Front B `Compression` remains blocked.

---

## ★ M2′ COMPLETE (2026-08-24) ★

**`parityRigidityW1'_imp_noDivergent : ParityRigidityW1' → NoDivergentOrbit` is PROVED,
sorry-free, `#print axioms = [propext, Classical.choice, Quot.sound]`** (trust base only),
in `Rigidity/Empirical.lean`. Full `lake build` green (8748 jobs). The Krylov–Bogolyubov
measure-rigidity crux DIRECTION.md mandated is discharged: the entire chain (empirical
Cesàro measures → weak-* cluster invariance + orbit-closure support → clopen/closed
Portmanteau → uniform sub-sharp `limsup` of the odd-frequency → drift descent of the
divergent tail → contradiction) is machine-checked. This means **Front A now reduces to the
single keystone conjecture `ParityRigidityW1'`** (a `def`, honestly a working conjecture):
if W1′ holds, `NoDivergentOrbit` follows, and with `NoNontrivialCycle` the headline closes.

Landed pieces (all `Rigidity/Empirical.lean`, all trust-base clean):
- `cluster_isT2Invariant_orbitClosure` — KB invariance + orbit-closure support for ANY
  convergent empirical subsequence φ→∞;
- `exists_isT2Invariant_orbitClosure` — the existence corollary;
- `empiricalMeasure_oddSetZ2` / `empiricalPM_oddSetZ2_real` — frequency link (odd-mass =
  odd-step count / N);
- `limsup_oddFreq_lt_sharp` — the uniform measure-theory crux (every subsequential limit
  is an invariant measure's odd-mass, W1′-bounded);
- `oddSteps_iterate_add` — tail odd-step additivity;
- `parityRigidityW1'_imp_noDivergent` — the assembly.

**Next-value work now (Front A is measure-side-complete):** the remaining Front-A obligation
is `ParityRigidityW1'` ITSELF (the keystone working conjecture) — genuinely open research.
The funded concrete probe is `FRONT-A-PARITY-RECONSTRUCTION.md`: reconstruct the unique
starting residue from each shortcut parity prefix, expose its next binary digit as an exact
carry update, and test whether critical odd density is incompatible with eventually-zero
output. Every finite parity word occurs, so bounded suffix memory / forbidden words alone
cannot work. Front B `Compression` remains blocked on the SdW source.

## Status (2026-08-24, review lap — RE-SCOPED) [SUPERSEDED by M2′ completion above]

- **Direction changed (see `DIRECTION.md`).** Front B `Compression` is BLOCKED and was
  mis-scoped as tractable; the binding crux is now **Front A M2′**
  (`ParityRigidityW1' → NoDivergentOrbit`), whose sole gap is a Krylov–Bogolyubov measure
  module. Decomposition below. **[M2′ NOW COMPLETE — see top of file.]**
- **Harmonic-dual obstruction project: COMPLETE** (`no_positive_harmonic_local_certificate`,
  sorry-free, axiom-clean). Do not re-run/port. See `FRONT-A-HARMONIC-DUAL.md`.
- **This lap landed** the two pure M2′ endpoints in `Rigidity/Drift.lean`
  (`exists_freqThreshold_gt`, `not_diverges_of_eventually_lt`; both trust-base clean) and
  wrote the M2′ decomposition (below). `src/` sorry-free; full `lake build` green.

## THE CRUX (binding, per `DIRECTION.md`): Front A M2′ measure module

**Goal:** `theorem parityRigidityW1'_imp_noDivergent : ParityRigidityW1' → NoDivergentOrbit`
(milestone M2′, `Rigidity/Invariant.lean`). This is the live Front-A route: the
local-certificate lane is harmonic-capped below α=1 (proved, complete), so M2′ (turning the
parity-rigidity keystone W1′ into `NoDivergentOrbit`) is how Front A would close.

**The argument (worked out this lap; the contradiction is against the TAIL, not the start):**
Suppose `Diverges n` (`1 ≤ n`).
1. **[gap: Krylov–Bogolyubov]** The Cesàro empirical measures `μ_N = (1/N)Σ_{k<N} δ_{T2^k n}`
   live in the weak-*-compact `ProbabilityMeasure ℤ₂` (mathlib: Prokhorov,
   `CompactSpace (ProbabilityMeasure ℤ₂)`); any cluster point `μ` is `T2`-**invariant**
   (telescoping `T2∗μ_N − μ_N = (1/N)(δ_{T2^N n} − δ_n)`, total mass `≤ 2/N → 0`, plus weak-*
   continuity of pushforward under the continuous `T2`). `μ` is supported on `orbitClosure n`.
   **This invariance step is the only piece absent from mathlib.**
2. **[gap: uniformity]** The invariant-measure set on `orbitClosure n` is weak-* compact and
   `ν ↦ ν oddSetZ2` is continuous (the parity set is clopen, `isClopen_oddSetZ2`), so W1′
   (`ν oddSetZ2 < sharpThreshold` for *each* such `ν`) gives a **uniform** `M* < sharpThreshold`
   bounding all of them, hence `limsup_N (μ_N oddSetZ2).toReal ≤ M*`. Via Portmanteau on the
   clopen set (mathlib: `ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto`) and the
   identity `(μ_N oddSetZ2).toReal = oddSteps n N / N`, this reads
   `limsup_N (oddSteps n N / N) ≤ M* < sharpThreshold`.
3. **[DONE]** `exists_freqThreshold_gt`: pick floor `N₀ ≥ 1` with `freqThreshold N₀ > M*`.
   `exists_floor_of_diverges` gives `K` with the orbit `≥ N₀` for indices `≥ K`; set the
   high tail `m = step^[K] n` (divergent, orbit `≥ N₀` forever). Since
   `limsup (oddSteps m k / k) = limsup (oddSteps n · / ·) ≤ M* < freqThreshold N₀`, for all
   large `k` the window `[0,k)` from `m` stays `≥ N₀` and `oddSteps m k / k < freqThreshold N₀`,
   so `lt_of_oddSteps_freq_lt` gives `step^[k] m < m`. Then **`not_diverges_of_eventually_lt`**
   ⟹ `¬ Diverges m` — contradicting divergence of the tail `m`. ∎

**State:** step 3 endpoints DONE; step 1's **computational core is now landed** in
`Rigidity/Empirical.lean` (all `[propext, choice, Quot.sound]`):
- `empiricalMeasure x N := N⁻¹ • Σ_{k<N} dirac (T2^[k] x)` (Cesàro empirical measure);
- `empiricalMeasure_isProbabilityMeasure` (N ≥ 1);
- `integral_empiricalMeasure` — `∫ f dμ_N = N⁻¹ Σ_{k<N} f (T2^[k] x)` (Birkhoff average);
- `integral_empiricalMeasure_comp_T2_sub` — the **telescoping identity**
  `∫ f∘T2 dμ_N − ∫ f dμ_N = N⁻¹ (f (T2^[N] x) − f x)` (the `O(1/N)` that forces cluster-point
  invariance).

**Krylov–Bogolyubov DONE (2026-08-24):** `exists_isT2Invariant_of_empirical`
(`Rigidity/Empirical.lean`, `[propext, choice, Quot.sound]`): **every `x : ℤ_[2]` admits a
`T2`-invariant probability measure**, obtained as a weak-* cluster point of the empirical
`empiricalPM x`. Proof = subsequence (Prokhorov compactness + `MapClusterPt.tendsto_subseq`,
`ProbabilityMeasure ℤ_[2]` metrizable) with `(empiricalPM x (ψk)).map T2 → μ.map T2`
(`tendsto_map_of_tendsto_of_continuous`) and `→ μ` (telescoping
`integral_empiricalMeasure_comp_T2_sub` + `tendsto_iff_forall_integral_tendsto`), then
`tendsto_nhds_unique`. This is milestone M2′ piece **(b)** (the invariance transfer).

**Remaining M2′ pieces (grind laps), in order:**
1. **Support on the orbit closure. DONE (2026-08-24, this lap).**
   `exists_isT2Invariant_orbitClosure (n : ℕ) : ∃ μ : ProbabilityMeasure ℤ_[2],
   IsT2Invariant μ ∧ (μ : Measure) (orbitClosure n) = 1` (`Rigidity/Empirical.lean`,
   `[propext, choice, Quot.sound]`). Supporting lemmas landed:
   - `T2_iterate_natCast : T2^[k] (↑n) = ↑(step^[k] n)` (iterated base intertwining);
   - `T2_iterate_natCast_mem_orbitClosure` (each orbit point ∈ closed `orbitClosure n`);
   - `empiricalMeasure_orbitClosure : empiricalMeasure (↑n) N (orbitClosure n) = 1` (N≥1).
   The invariance half reuses the KB argument; the support half is closed-set Portmanteau
   (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` on `isClosed_closure`): every
   empirical gives the closed orbit closure mass `1`, so `1 = limsup ≤ μ(orbitClosure n) ≤ 1`.
   **Frequency link landed (2026-08-24, this lap):** `empiricalMeasure_oddSetZ2 (n N) :
   empiricalMeasure (↑n) N oddSetZ2 = N⁻¹ * (oddSteps n N : ℝ≥0∞)` plus
   `T2_iterate_natCast_mem_oddSetZ2 (n k) : T2^[k] ↑n ∈ oddSetZ2 ↔ step^[k] n % 2 = 1`
   (`Rigidity/Empirical.lean`, `[propext, choice, Quot.sound]`). This is the exact identity
   `(μ_N oddSetZ2) = oddSteps n N / N` piece 2 needs; the empirical odd-mass IS the odd-step
   count. Remaining in piece 2: clopen Portmanteau `(empiricalPM (↑n)(ψk)) oddSetZ2 →
   μ oddSetZ2` + W1′ to bound the limit `< sharpThreshold`.
   **Uniformity DONE (2026-08-24, this lap):** `limsup_oddFreq_lt_sharp (hW1) (n) (hn) :
   Filter.limsup (fun i => oddSteps n (i+1)/(i+1)) atTop < sharpThreshold`
   (`Rigidity/Empirical.lean`, `[propext, choice, Quot.sound]`). Every subsequential limit
   of the odd-frequency is realised — via a Prokhorov sub-subsequence of the empiricals +
   clopen Portmanteau (`tendsto_measure_of_isClopen_of_tendsto`) — as the odd-mass of a
   `T2`-invariant measure supported on `orbitClosure n`, which W1′ bounds `< sharpThreshold`;
   `limsup` is such a subsequential limit (`exists_seq_tendsto_limsup`). Supporting refactor:
   `cluster_isT2Invariant_orbitClosure` (KB invariance+support for an ARBITRARY convergent
   subsequence φ→∞) and `empiricalPM_oddSetZ2_real` (empirical odd-mass in ℝ = odd-freq).
   **This is the load-bearing measure-theory crux of M2′.** Remaining: the tail assembly
   (piece 3) into `parityRigidityW1'_imp_noDivergent`.
2. **Frequency link + uniformity.** `(empiricalPM x N) oddSetZ2 = oddSteps? / (N+1)` via
   Portmanteau on the clopen `oddSetZ2`; the invariant-measure set is weak-* compact and
   `ν ↦ ν oddSetZ2` continuous, so W1′ ⟹ uniform `M* < sharpThreshold`, hence
   `limsup (oddSteps n · / ·) ≤ M*`.
3. **Assemble** with `exists_freqThreshold_gt` + `not_diverges_of_eventually_lt` +
   `lt_of_oddSteps_freq_lt` ⟹ `parityRigidityW1'_imp_noDivergent`.

Key mathlib API confirmed present: `ProbabilityMeasure.map`, `.continuous_map`,
`tendsto_map_of_tendsto_of_continuous`, `tendsto_iff_forall_integral_tendsto`,
`tendsto_measure_of_isClopen_of_tendsto`, `MetrizableSpace (ProbabilityMeasure ℤ_[2])`.

**Note (converse calibration, lower value):** `NoDivergentOrbit → ParityRigidityW1'` has its
arithmetic done (`repeat_cycle_oddFreq_lt_sharp`); its gap is "invariant measure on a *finite*
orbit closure = uniform cycle measure". It only calibrates that W1′ isn't too strong (change of
language), so it is NOT the funded direction — M2′ (forward/consumption) is.

---

## Front B (ON HOLD — blocked + mis-scoped; do NOT extend)

`Compression` (`FrontB/Threads.lean`): `∃ C, ∀ v, Primitive v → IntegerCycle v →
¬ IsTrivial v → circuits v ≤ C` — an **upper** bound on the circuit count of a
primitive nontrivial integer cycle. With `hercher_min_circuit_count` (≥92) any `C ≤ 91`
closes Front B via `frontB_of_compression_le_91`. **Review finding (2026-08-24):** this is
Front B *restated*, not a sub-lemma — an upper bound on `m` is as hard as the cycles problem,
is **absent from the literature** (which bounds `m` only below), and is **source-blocked** (SdW
2005 not on box, `ON-LINE-REQUEST.md` unanswered). The block apparatus below is feature-complete;
**do not add more vocabulary.** Resume only when the SdW source lands or a genuinely new
upper-bound idea appears. The completed apparatus (kept for that day):

**Why this is the route-decisive blocker, not a leaf:**
- Every literature tool bounds circuits (≡ `m`, local minima ≡ `D` proxy) **from
  below** (Simons–de Weger 68→76, Hercher 77→91→"≥92"). That direction "never finishes"
  (`FRONT-B-ROUTES.md` §filter: `log₂3` irrational ⇒ arbitrarily good approximations).
- The *upper* bound is **absent from the published record** — it is the one missing
  ingredient. It is an integrality/divisibility statement (pure combinatorics on words +
  `2^i 3^j` lattice), no analysis. Route 2 in `FRONT-B-ROUTES.md`.

**Progress (2026-08-24):** source request filed (`ON-LINE-REQUEST.md`, SdW method).
Built the circuit-block normal form the compression argument runs on
(`OneCircuit.lean`, all `[propext, Quot.sound]`):
- `circuits_oneCircuitWord : circuits (oneCircuitWord a b) = 1`;
- `def blockWord [(a₁,b₁),…,(aₘ,bₘ)] = trueᵃ¹falseᵇ¹…` and
  **`circuits_blockWord : (∀ blk∈L, 1≤blk.1 ∧ 1≤blk.2) → circuits (blockWord L) = L.length`**
  — a block word has exactly `m` circuits (one falling edge per block), via the
  `cpairs`/`countP` peeling helpers `countP_falls_cpairs_{replicate_true, replicate_false,
  false_cons, false_prefix}` and `cpairs_true_falls_blockWord`.

Also proved the **S-unit structure of `numer`** on the normal form:
`numer_blockWord_cons : numer(blockWord ((a,b)::L)) = 2^(a+b)·numer(blockWord L)
+ 3^(ones (blockWord L))·(3^a − 2^a)` (ℤ), via `numer_replicate_{true,false}_prefix`.
Each block contributes exactly one collapsed odd-run term `3^{aⱼ}−2^{aⱼ}` — so the cycle
equation `numer = N·den` has **`m = circuits` S-unit terms**, not cycle-length-many. This
is the Route-2 leverage made precise: bounding `m` bounds the term count, which is what
would let ESS/Baker apply.

Completed the block-form **arithmetic dictionary** (exponent vectors explicit):
`ones_blockWord = Σ aⱼ`, `length_blockWord = Σ(aⱼ+bⱼ)`,
`den_blockWord = 2^{Σ(aⱼ+bⱼ)} − 3^{Σ aⱼ}`. With `numer_blockWord_cons` the entire cycle
equation `numer = N·den` is now read off the `m` blocks — the bounded S-unit datum a
fixed-`m` argument works from.

**State of the Front B block vocabulary:** coherent + complete for the block form —
`blockWord`, `circuits = m`, `numer = m`-term S-unit recurrence, `ones/length/den`
explicit. The SUMMIT (bound `m` by a constant = `Compression`)
is genuinely open (no known handle; ESS not in mathlib) and **blocked on the SdW source
read** (`ON-LINE-REQUEST.md`, awaiting `ON-LINE-FINDINGS-*`). Further speculative
vocabulary should wait for SdW's actual method, lest we build the wrong reduction.

**Converse DONE (canonical case):** `exists_blockWord_canonical_circuits` — a word with
`head = true`, `last = false` decomposes as `v = blockWord L` with `circuits v = L.length`
(all blocks nonempty), via structural run-peeling (`peel_true_run`/`peel_false_run`) +
strong induction. So "bound `circuits v`" (for canonical cycle words) is literally "bound
the block count `L.length`" — exactly the `Compression` shape. `[propext, choice, Quot.sound]`.

**Reduction to ALL cycles DONE (2026-08-24, this lap):** the canonical restriction is now
removed. New in `OneCircuit.lean` (all `[propext,(choice,)Quot.sound]`):
- `circuits_rot`/`circuits_rotate` — `circuits` is rotation-invariant (the `cpairs`
  cyclic-adjacency list merely cycles by one entry under `rot`; falling-edge count fixed,
  proved by peeling the head pair via `cpairs_append`).
- `rotate_canonical_of_head_false` — a `false`-headed word containing a `true` rotates to
  canonical form (rotate to first `true`; its predecessor precedes the first `true`, hence
  is `false`). Uses `findIdx`/`lt_findIdx_iff` + `head?_rotate`/`getLast?_take`.
- `exists_rotate_canonical` — ANY word with both a `true` and a `false` rotates to canonical.
- **`exists_blockWord_of_integerCycle`** — every integer-cycle word, after a rotation
  `v.rotate k`, IS a genuine `blockWord L` (all blocks nonempty) with `circuits v = L.length`.
  Membership from `true_mem_of_ones_pos` (`ones≥1`) + `false_mem_of_den_pos` (`0<den` rules
  out all-`true` since `2ⁿ<3ⁿ`). **So "bound `circuits` for integer cycles" ⟺ "bound the
  block count" is now fully machine-checked for ALL cycles** — the reduction plumbing for
  `Compression` is complete. What remains is the SUMMIT: bound the block count by a constant.

**Explicit S-unit closed form (2026-08-24, this lap):** `numer_blockWord_explicit` —
`numer (blockWord L) = Σ_{j<m} 2^{Σ_{i<j}(aᵢ+bᵢ)}·3^{Σ_{i>j}aᵢ}·(3^{aⱼ}−2^{aⱼ})`, exactly `m`
monomial-difference terms (one per circuit), each a `{2,3}`-unit coefficient times the
collapsed odd-run difference. This is the canonical S-unit datum ANY Diophantine bound on `m`
(subspace theorem / Baker / SdW) consumes — method-independent, so a genuine prerequisite,
not speculative reduction-vocabulary. `[propext, choice, Quot.sound]`. **It does NOT bound
`m`** — the summit (bound the S-unit rank = block count) remains the open Diophantine wall,
source-blocked on the SdW method read (`ON-LINE-REQUEST.md`, unanswered).

**Cycle predicate rotation-invariant (2026-08-24, this lap):** `integerCycle_rot` /
`integerCycle_rotate` — `IntegerCycle` is preserved under rotation (`ones`/`den` invariant,
`den∣numer` transfers via `dvd_numer_rot_iff`). `exists_blockWord_of_integerCycle` now
delivers `IntegerCycle (blockWord L)` too, so a Diophantine argument on the block form has the
**full cycle hypothesis** on the block word, not just the circuit count. `[propext,choice,Quot.sound]`.

**Member-value Diophantine equation (2026-08-24, this lap):** `blockWord_cycle_diophantine`
— a block-form integer cycle satisfies `Σⱼ (S-unit term j) = N·(2^{Σ(aᵢ+bᵢ)} − 3^{Σaᵢ})` with
member `N ≥ 1`. This is the EXACT `{2,3}`-S-unit equation any Diophantine method must solve:
`m = circuits` terms on the left, one linear form on the right. `Compression` = bound the
number of S-unit terms `m` in this equation. The Front B block/S-unit/rotation apparatus is
now feature-complete: normal form, circuit count, explicit numer/den, cycle hypothesis
transport, and the packaged Diophantine equation. `[propext,choice,Quot.sound]`.

**Crux feasibility test (recorded — the wall is real, not a config artifact):** attempted
the cheap version of the Compression summit. The per-`m` case needs transcendence, verified
by inspection: `m=1` is Steiner 1977 (`SteinerOneCircuit`, effective irrationality of
`log₂3`); `m=2` is also Baker/Steiner (2-circuit cycles ruled out via continued fractions,
not elementary). The S-unit view confirms it: bounding the block count = bounding the S-unit
RANK, and ESS/subspace bounds the number of *solutions* given the rank, never the rank — so
there is no elementary handle; this is the cycles problem. The uniform bound over all `m` is
the open Diophantine wall. **Concrete attack:** read SdW's per-`m` elimination method
(source-blocked, `ON-LINE-REQUEST.md`) to formalize the cycle→Baker instance reduction that
makes `baker_bounded_difference` (or a Steiner-type input) the single narrow cited input per
`m`. Until the source lands, the block/S-unit/rotation apparatus is complete and correct.

**Next lap options:** (a) ~~rotate arbitrary integer-cycle word to canonical form~~ —
**DONE this lap** (`exists_blockWord_of_integerCycle`). (b) if SdW findings landed, formalize
their fixed-`m` reduction on the block datum. (c) **pivot to the alternate crux, Front A
itinerary-rigidity** (per `DIRECTION.md`) — both fronts' SUMMITS (bound `m`; build a
divergence certificate) are open research, so weigh whether more Front B reduction-plumbing
or a Front A prerequisite is the higher-value next advance.

**Attack paths (each lap: the smallest source-/compiler-grounded probe):**
1. **Source read (filed):** Simons–de Weger 2005/2010 — do they bound circuit count
   above for any cycle family, or only rung-by-rung? Awaiting `ON-LINE-FINDINGS-*`.
2. **Decompose in Lean:** state `Compression` via the S-unit equation
   `Σ 3^{a−1−i} 2^{E_i} = N·D` (ESS/subspace theorem bounds solution count by term count
   `= a` — vacuous unless `a` compresses). Name the missing "few circuits" sub-lemma as a
   `def`, prove the wiring around it. Do NOT manufacture vacuous sorries.
3. **Refuted already — do not retry:** Route-1 gcd-harvest over rotations (Thread 7,
   `route1_gcdHarvest_false`): all rotations give ONE divisibility condition mod `D`.

## Front A progress (2026-08-24, this lap): W1′ converse arithmetic

`cycle_three_pow_lt_two_pow` / `cycle_oddFreq_lt_sharp` (`Rigidity/Drift.lean`, axiom-clean):
a genuine `step`-cycle `step^[p] n = n` (`n≥1`, `≥1` odd step) has `3^oddSteps < 2^evenSteps`
(via the existing exact `mul_three_pow_le` + parity: `3^a` odd, `2^b` even), hence odd-step
frequency `oddSteps/period < log2/log6 = sharpThreshold`. This is the **converse-direction
arithmetic** of the `ParityRigidityW1' ↔ NoDivergentOrbit` calibration
(`W1PrimeIffFrontA`, `Rigidity/Invariant.lean` milestone note): every eventual cycle of a
non-divergent orbit sits below the drift ceiling. **Remaining converse gap = the MEASURE
plumbing** (a `T2`-invariant probability on a finite orbit closure is the uniform cycle
measure; then `μ(odd) = oddFreq`), plus Krylov–Bogolyubov for the forward M2′ direction. That
plumbing is genuine ℤ₂ measure theory (likely mathlib-gappy) — a multi-lap build, not a probe.

**Arithmetic side FULLY ASSEMBLED (later same lap):** `step_zero`/`iterate_step_zero`
(0 absorbing), `periodic_point_of_repeat` (a repeat → genuine periodic point of period `j-i`),
`oddSteps_pos_of_cycle` (a positive cycle takes ≥1 odd step — all-even would force `m·2^p≤m ⇒
p=0` via the drift bound), and **`repeat_cycle_oddFreq_lt_sharp`**: every eventual cycle of a
positive orbit has odd frequency `< log2/log6 = sharpThreshold`. So the ENTIRE arithmetic side
of the W1′ converse is done. **The sole remaining gap is the ℤ₂ measure identification**: a
`T2`-invariant probability on the finite orbit closure of an eventually-periodic orbit is the
uniform measure on the cycle, and its `oddSetZ2`-mass equals `oddSteps/period`. Next Front A
lap: attack THAT (needs `orbitClosure` of an eventually-periodic point = finite cycle set in
ℤ₂ + invariant-measure-on-finite-set = weighted-by-visit; check mathlib for
`MeasurePreserving` on finite sets / periodic points).

## Alternate crux: Front A itinerary-rigidity

`NoDivergentOrbit` needs a `DivergentDescentCertificate` (`FrontA/Threads.lean`
`noDivergent_of_certificate`). The local-certificate constructive ladder (2/3→3/4→4/5
rungs green) is **capped below α=1** by the harmonic no-go, so it cannot complete the
certificate alone. Redirect: build the certificate from `tao_2019_almost_bounded`
(🟡 proved upstream) + `furstenberg_topological_rigidity` (🟠 proved 1967). See
`FRONT-A-ROUTES.md` (A1/A3). Pick this if Front B `Compression` stalls.

## Longer horizon — narrow the cited axioms
- `baker_bounded_difference` (🟠): formalize the elementary cycle→S-unit reduction so
  Baker/Tijdeman is the single narrow cited input.
- Adopt the Hercher–Bařina unconditional bound (`K > 1.375×10¹¹`, supersedes Eliahou by
  4 orders) into `Assumed/Cycles.lean` — an axiom-strengthening, deliberate step.
- `SteinerOneCircuit`: provable only via an effective irrationality measure for `log₂3`
  (multi-year). Leave isolated.
