# PENDING_WORK

## ★ Parity-reconstruction pull — CLASSIFIED (2026-08-24, this session) ★

Executed `FRONT-A-PARITY-RECONSTRUCTION.md` (experiment + Lean kernel + strength audit).
New module `CollatzMoonshot/FrontA/ParityReconstruction.lean` (all trust-base clean
`[propext, Classical.choice, Quot.sound]`, full build green 8749 jobs) and
`experiments/parity_reconstruction.py` (exact, exhaustive to depth 16).

**What was PROVED (Lean, sorry-free):**
- `tstep_iterate_lt` — the **carry invariant**: `tstep^[m] n < 3^(ones(traceWord n m))·(n/2^m+1)`
  for ALL n (strengthened form absorbing the odd step where the naive induction breaks).
- `tstep_iterate_lt_pow_ones` — for `n < 2^m`, `tstep^[m] n < 3^(ones)` (normalized endpoint
  `q/3^a < 1`, tight at all-ones). First rigorous archimedean word↔size coupling here.
- `two_pow_mul_gap` — exact carry-gap identity `2^m(3^a−q) = 3^a(2^m−n) − numer`.
- `pow_ones_mul_le` — matching lower bound `3^a·n ≤ 2^m·tstep^[m] n` (the drift bracket).
- `traceWord_eq_imp_modEq`, `eq_of_forall_traceWord_eq` — residue determinacy (a natural is
  determined by its parity itinerary).
- `tstep_repeat_of_eventually_periodic_parity` + `..._periodic_...` — eventually-periodic
  parity ⇒ the accelerated orbit repeats/is bounded (restricted no-divergence baseline).

**Strength-audit findings (experiment, exhaustive):**
- Exact gap `3^a − q` bottoms out at **1** for every depth ⇒ `q < 3^a` is the SHARPEST
  uniform bound; no depth-independent inequality strictly tighter exists.
- **Bounded-suffix Lyapunov NO-GO** (the load-bearing negative result): at depth 16 there
  are two words sharing their last 3 bits with `q/3^a` spread `≈ 0.9997` (nearly the full
  range). Any potential reading only a bounded parity suffix cannot separate them. This is
  the forward analogue of the 3-adic adversary that capped the backward local-potential lane
  — a working carry Lyapunov function MUST read unbounded archimedean state (`q` itself).
- **Positivity is genuinely asymptotic**: restricting to small-start words (top output bit
  zero, `r < 2^{m-1}`) still admits odd density `(m−1)/m → 1`, well above critical
  `log2/log3 ≈ 0.6309`. No finite-prefix output condition forces sub-critical density; the
  positivity constraint (output bits *eventually* zero) is irreducibly a tail statement.

**CLASSIFICATION: BASELINE / REDIRECT (honest).**
The reconstruction API is complete and one certified depth-independent carry invariant was
found (`q < 3^a`), but it is the KNOWN critical-drift envelope, not a new divergence
obstruction; combined with the lower bound it only re-derives "divergence ⇒ odd density
> log2/log3". No invariant strictly stronger than eventual-periodicity kills divergence.
The audit turned DIRECTION.md's guardrail from conjecture into a proved obstruction:
bounded carry/memory potentials provably FAIL (explicit adversarial pair), so `ParityRigidityW1'`
cannot be reached by any finite-state / bounded-suffix certificate — success must be
asymptotic (control eventual-output-zero jointly with critical density) or use the unbounded
endpoint `q` as archimedean state. **Do not manufacture more Lean plumbing on this coordinate
(e.g. the full online R-recurrence is API-complete in Python and would be routine in Lean —
not load-bearing given this verdict).** Next mathematical re-scope: a *tail* statement
coupling `q`'s growth to output-bit-zero, i.e. an asymptotic density/aperiodicity argument,
not a bounded certificate. Front B `Compression` remains blocked on the SdW source.

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
