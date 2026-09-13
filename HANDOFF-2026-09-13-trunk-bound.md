# Handoff: min-term trunk bound landed (operator-assigned bounded node)

Date: 2026-09-13. Branch: `main`. Starting HEAD: `571214e`.
Scope: the one-lap operator assignment (Trevor, 2026-09-13) superseding the
"awaiting a new mechanism" pause for this node only. DIRECTION.md carries a
one-line history note; its directive otherwise stands.

## What landed

New default-build module `CollatzMoonshot/FrontA/TrunkBound.lean` (imported from
the root `CollatzMoonshot.lean`). Notation: `x_i = tstep^[i] n`,
`I = oddSteps n m = {i < m | x_i odd}`, `a = ones (traceWord n m) = |I|`
(`card_oddSteps`), `x_min = segMin n m` (the `Finset.inf'` of the odd-step values).

| Declaration | Statement | Trust |
|---|---|---|
| `tstep_iterate_prod_identity` | `2^m·x_m·∏_I 3x_i = 3^a·n·∏_I (3x_i+1)`, all `n m` | triple |
| `min_term_inequality_le` | `1 ≤ n`, `n ≤ x_m`, `x ≤ x_i ∀ i∈I` → `2^m(3x)^a ≤ 3^a(3x+1)^a` | triple |
| `one_le_ones_of_lt` | `n < x_m → 1 ≤ a` | triple |
| `min_term_inequality` | `n < x_m`, `x ≤ x_i ∀ i∈I` → `2^m(3x)^a < 3^a(3x+1)^a` | triple |
| `min_term_inequality_segMin` | the same at `x = x_min` | triple |
| `lowerBound_lt_of_subcritical` | plus `3^a < 2^m`, `1 ≤ x` → `x < a/(3(m log 2 − a log 3))` in `ℝ` | triple |
| `segMin_lt_of_subcritical`, `acyclicParadoxical_segMin_lt` | `x_min < a/(3Λ)` | triple |
| `segMin_lt_poly_of_acyclicParadoxical` | `AcyclicParadoxical n m → x_min < a^437/(3·rhinLiteSepC) + a` | inherits Rhin-lite natives |
| `segMin_lt_nat_poly_of_acyclicParadoxical` | `→ x_min < 396^6000·6^436·a^437` in `ℕ` | inherits Rhin-lite natives |
| `trunkBound_control_seven_eight` | `oddSteps 7 8 = {0,1,2,4,7}`, values `{7,11,17,13,5}`, `segMin = 5`, `a = 5`, `2^8·15^5 = 194400000 < 254803968 = 3^5·16^5` | triple (`decide +kernel`) |
| `prod_identity_control_seven_eight` | identity instantiated on `(7,8)` | triple (`decide +kernel`) |

Proof shape. (1) Induction on `m`, appending index `m` via `Finset.range_add_one`;
odd step `2·tstep X = 3X+1` multiplies the identity by `3(3X+1)`, even step
`2·tstep X = X` leaves it. (2) `n·2^m·∏3x_i ≤ x_m·2^m·∏3x_i = 3^a·n·∏(3x_i+1)`,
cancel `n`; then `∏(3x_i+1)·(3x)^a ≤ (3x+1)^a·∏3x_i` termwise
(`Finset.prod_le_prod`, each factor is `x ≤ x_i`), cancel `∏3x_i > 0`.
No subcriticality is used in (2), and the `≤` form covers cyclic endpoints.
(3) logs of (2) plus `Real.log_le_sub_one_of_pos` on `(3x+1)/(3x)`. (4) window
`2^m < 2·3^a`: `rhinLite_log23_measure a m` gives `Λ ≥ c/a^436`; off window
`Λ ≥ log 2 > 1/3` so `a/(3Λ) < a`.

Docstring states this is the easy (min-term) half of Rozier–Terracol Theorem 4.2
(harmonic-mean form); no novelty is claimed. Its value is the exact
trajectory-side foothold DIRECTION.md names: every paradoxical segment dips to an
odd value below `a/(3Λ)`. Host exact controls (2026-09-13) on all 320 census
segments at lengths 8, 27, 46, 65, 73 agree with the formal statements.

## Verification actually run

1. `lake build` — 8772 jobs, success, no warnings from the new file.
2. `#print axioms` on all 20 new declarations (via `lake env lean --stdin`,
   `import CollatzMoonshot`): every declaration except the two Rhin-lite
   corollaries reports exactly `propext, Classical.choice, Quot.sound`; the two
   corollaries additionally report exactly the eleven
   `..._native.native_decide.ax_*` certificates already allow-listed in
   `scripts/check-fixed-block-bound.sh` (the same set as
   `acyclicParadoxical_length_lt_of_oddRunCount`). No new axiom, no `sorry`.
3. `bash scripts/check-fixed-block-bound.sh` — real full `lake build`, 8772 jobs,
   **FORMALIZE-TIER GREEN**; its six-declaration audit unchanged.

## Not done / next

No push (host pushes). The hard half of RT 4.2 (all-terms harmonic-mean form)
and any use of the dip `x_min < a/(3Λ)` against full admission `D·c_m < N`
remain unspecified; DIRECTION's pause stands until a mechanism is proposed.
