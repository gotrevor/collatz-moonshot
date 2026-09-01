# HANDOFF 2026-09-01 (review lap) — RT axiom fidelity bug caught & repaired; two-block exclusion proved SHARP

## State
- Branch `main`, working tree committed, `lake build` 🟢 **8764 jobs**, `check-proof-debt.sh` → **0
  sorries**, `src/` (`CollatzMoonshot/`) sorry-free.
- **Binding directive changed** — see `DIRECTION.md` → CURRENT DIRECTIVE.  New objective:
  discharge `Assumed.rozier_terracol_3_2`.

## What this lap found (the headline)
`Assumed.rozier_terracol_3_2` was stated as
`∀ K, ∃ k m, K < 2^k n ∧ Paradoxical (2^k n) m` — *unboundedly large* paradoxical starts.
**That form implies `NoNontrivialCycle`**, an open problem, so it was strictly stronger than the
cited Rozier–Terracol 2026 Thm 3.2 (a *cardinality* claim: infinitely many paradoxical segments
starting at numbers `2^k n`).  Machine-checked, not argued:

    #print axioms noNontrivialCycle_of_unboundedParadoxicalStarts
    → [propext, Classical.choice, Quot.sound]

Mechanism: from `2^k n` the shortcut orbit does `k` pure halvings to `n`, then follows `n`'s orbit.
If that orbit is bounded by `B`, then once `2^k n > B` *no* segment from `2^k n` returns to its
start.  A nontrivial cycle's minimum has infinite shortcut stopping time and a bounded orbit.

## What landed
1. **Axiom repaired** to the published form
   `{p : ℕ × ℕ | Paradoxical (2 ^ p.1 * n) p.2}.Infinite`.
2. **Refutation kept in `src/` as a permanent guard** (all trust-base clean):
   `UnboundedParadoxicalStarts` (named, never axiomatized),
   `not_unboundedParadoxicalStarts_of_bounded`,
   `noNontrivialCycle_of_unboundedParadoxicalStarts`,
   plus `tstep_iterate_two_pow_mul{,_le,_ge}`, `step_orbit_bounded_of_onCycle`.
3. **Non-vacuity anchor** (trust-base clean): `infinite_paradoxical_of_tstep_cycle` — a shortcut
   cycle through `n > 2` really does give infinitely many paradoxical segments starting at `2^0 n`.
   With `subcritical_of_tstep_cycle`, `ones_traceWord_mul_of_cycle`.
4. **Consumption re-derived** from the cardinality form: `diverges_imp_infinite_acyclicParadoxical`
   now maps the axiom's infinite pair set through the injection `(k,m) ↦ (2^k m₀, m)`.
   `finite_acyclicParadoxical_imp_noDivergent` unchanged in statement *and* ledger.
5. **Two-block exclusion proved SHARP**: `acyclicParadoxical_seven_eight` (`n = 7`, `m = 8`, word
   `TTTFTFFT`, three odd blocks) by kernel `decide` — so no three-block strengthening exists and
   the "≥ 3 odd blocks" discovery result is exactly sharp.  Brute scan to `n ≤ 200000` agrees.
6. Docs: `DIRECTION.md` (new CURRENT DIRECTIVE + history line), `STATUS.md` (spine + axiom ledger
   re-run from real `#print axioms`), `PENDING_WORK.md` (finding + next attack), `README.md`
   (two new rows), `scripts/AxiomAudit.lean` (5 new declarations).

## Axiom audit (real `#print axioms`, this HEAD)
- `conjecture_iff_split`, `parityRigidityW1'_imp_noDivergent` → trust base.
- `FrontA.sep_two_three`, `FrontA.le_two_blocks_not_acyclicParadoxical` → trust base + 13
  `native_decide` artifacts.  **No literature axiom.**
- `finite_acyclicParadoxical_imp_noDivergent` → trust base + `Assumed.rozier_terracol_3_2` (the
  one remaining cited axiom under a Front-A headline).
- `FrontB.frontB_of_compression_le_91` → trust base + `FrontB.hercher_min_circuit_count`.
- `noNontrivialCycle_of_unboundedParadoxicalStarts`, `not_unboundedParadoxicalStarts_of_bounded`,
  `infinite_paradoxical_of_tstep_cycle`, `acyclicParadoxical_seven_eight` → trust base only.

## Next actions (obey `DIRECTION.md`)
Discharge `rozier_terracol_3_2`, split by orbit boundedness.  The exact algebra is in
`PENDING_WORK.md`; the short version is that the `2^k` prefix cancels out of the iterate identity,
leaving

    Paradoxical (2^k n) (k+j)  ⟺  ρ_j < 2^k ≤ (tstep^[j] n)/n,   ρ_j = 3^(ones (traceWord n j)) / 2^j

so the theorem is "infinitely often a power of 2 separates the coefficient from the normalized
endpoint".
- **(A) bounded orbit — do this first, fully elementary.**  Orbit enters a cycle; the cycle block
  is subcritical, so `ρ → 0` and `k = 0` works for large `j`.
- **(B) unbounded orbit — the Diophantine node.**  Needs a left approximation `3^a/2^b < 1` of `1`
  within `1/n`; feed it the repo's `log₂3` convergent machinery.  State as a disclosed `sorry` in
  `src/` and chip it.

No in-flight Aristotle job.

## Corpus-worthy gotchas
- `set x := sInf S` leaves hypotheses phrased in `sInf S`, not `x`; `rw [← h]` then fails.  Package
  the minimum with `obtain ⟨m₀, k₀, hk₀, hmin⟩ : ∃ m₀ k₀, step^[k₀] n = m₀ ∧ ∀ j, m₀ ≤ step^[j] n`
  instead — the `∃` intro beta-reduces and the two facts come out already in terms of `m₀`.
- `Function.iterate_mul f m n : f^[m*n] = (f^[m])^[n]` — the *left* factor is the inner map, so
  `tstep^[L*j] n = (tstep^[L])^[j] n`; no `Nat.mul_comm` needed (and adding one breaks it).
- `ones_append` is ambiguous when both `FrontA` and `FrontB` are open; qualify it.
- `AcyclicParadoxical 7 8` closes by plain kernel `decide` (`refine ⟨_,_,?_,?_⟩ <;> decide`) — small
  `tstep` iterates and `3^5 < 2^8` need no `native_decide`.
