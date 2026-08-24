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

**Attack paths (each lap: the smallest source-/compiler-grounded probe):**
1. **Source read (do first):** Simons–de Weger 2005/2010 — do they bound circuit count
   above for any cycle family, or only rung-by-rung? The PDF is NOT on-box; append a
   dated request to `ON-LINE-REQUEST.md` (check `archive/findings/` first).
2. **Decompose in Lean:** state `Compression` via the S-unit equation
   `Σ 3^{a−1−i} 2^{E_i} = N·D` (ESS/subspace theorem bounds solution count by term count
   `= a` — vacuous unless `a` compresses). Name the missing "few circuits" sub-lemma as a
   `def`, prove the wiring around it. Do NOT manufacture vacuous sorries.
3. **Refuted already — do not retry:** Route-1 gcd-harvest over rotations (Thread 7,
   `route1_gcdHarvest_false`): all rotations give ONE divisibility condition mod `D`.

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
