# PENDING_WORK

## Status (2026-08-24, review lap)

- **Harmonic-dual obstruction project: COMPLETE.**
  `no_positive_harmonic_local_certificate` proved sorry-free, depth-uniform,
  axiom-clean (trust base + 4 `native_decide`). See `FRONT-A-HARMONIC-DUAL.md`.
- **`OneCircuit` a≥2 resolved honestly** (this lap): NOT an `omega` leaf — it is
  **Steiner's theorem (1977) = Baker/effective-irrationality of `log₂3`**, and it is
  **off the ladder's critical path** (`hercher_min_circuit_count` already covers every
  circuit count ≤91, this rung included). Isolated as the explicit hypothesis
  `SteinerOneCircuit` (a `def`, no new axiom); `sorry` removed; module imported from
  root and green. `#print axioms oneCircuitCanonical_trivial = [propext, choice, Quot.sound]`.
- `src/` root chain sorry-free; full `lake build` green (8747 jobs).

## THE CRUX (binding, per `DIRECTION.md`): Front B `Compression`

`Compression` (`FrontB/Threads.lean`): `∃ C, ∀ v, Primitive v → IntegerCycle v →
¬ IsTrivial v → circuits v ≤ C` — an **upper** bound on the circuit count of a
primitive nontrivial integer cycle. With `hercher_min_circuit_count` (≥92) it closes
Front B outright via `frontB_of_compression_le_91` (any `C ≤ 91` suffices).

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
