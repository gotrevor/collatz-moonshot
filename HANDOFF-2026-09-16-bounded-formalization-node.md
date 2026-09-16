# HANDOFF 2026-09-16 — operator-assigned bounded formalization node: both halves landed

**Branch** `main`. **HEAD at checkpoint** `f05b7f7` (this doc), on top of `2a1478b` (Node 2)
and `8510836` (Node 1). Working tree clean, `lake build` green (8773 jobs), `src/` sorry-free,
`box done` signalled and honored — the treadmill does not relaunch after this lap.

**Exact next steps if the pause is lifted** (none of these is currently assigned):
1. Rhin-lite polynomial corollary for the harmonic mean: copy
   `TrunkBound.segMin_lt_poly_of_acyclicParadoxical` with `harmonicMean` in place of `segMin`,
   feeding `harmonicMean_lt_of_subcritical` into `rhinLite_log23_measure`; it will inherit the
   eleven allow-listed natives, so it must be a separate declaration with the ledger docstring.
2. The standing open problem is unchanged: turning the trajectory dip `x_min < a/(3Λ)` (now also
   `h < a/(3Λ)`) into an admission constraint on `D·c_m < N`. No mechanism for that is specified.

Assignment: `DIRECTION.md` attended override 2026-09-15 23:58 EDT. Both nodes complete,
repo sorry-free, `bash scripts/check-fixed-block-bound.sh` still FORMALIZE-TIER GREEN.

## Node 1 — Front B statement hygiene (`CollatzMoonshot/FrontB/Threads.lean`), commit `8510836`

- `countingGivesFinite_iff_frontB : CountingGivesFinite ↔ FrontB`. Forward via
  `Set.infinite_of_injective_forall_mem` on `j ↦ wpow v (j+1)`; injective because
  `length_wpow` makes the lengths `(j+1)·|v|` distinct, membership from
  `integerCycle_wpow_iff` / `isTrivial_wpow_iff`. Backward: the set is empty.
- `not_finitenessIsNotEmptiness : ¬ FinitenessIsNotEmptiness` — the "finiteness is not
  emptiness" gap is uninhabited *as typed*, which is what the 2026-09-13 reflection found.
- `ladderCompletes_iff_frontB : LadderCompletes ↔ FrontB`. Forward takes `C := circuits u`
  for the primitive root `u` from `exists_primitive_root`; quantifying over *all* `C` is
  what kills it. The fixed-`C` rungs (`hercher_min_circuit_count`, `C ≤ 91`) are unaffected
  and remain the genuinely weaker published content.
- `PrimitiveCountingGivesFinite` added as the honest Simons-de Weger/Hercher population;
  **no** implication from it to `FrontB` is claimed or provable here.
- The two docstrings the reflection called false are corrected in place.

All three theorems: `[propext, Classical.choice, Quot.sound]`.

## Node 2 — Rozier–Terracol Thm 4.2, harmonic-mean half (`CollatzMoonshot/FrontA/HarmonicMean.lean`), commit `2a1478b`

`I = oddSteps n m`, `a = |I|`, `x_i = tstep^[i] n`, `harmSum = H = ∑_{i∈I} 1/x_i`,
`harmonicMean = h = a/H`.

- `prod_le_pow_harmonic`: `∏_{i∈I} (1 + 1/(3x_i)) ≤ (1 + H/(3a))^a` — weighted AM–GM
  (`Real.geom_mean_le_arith_mean_weighted`, weights `1/a`), with the rpow→npow transfer done
  by `Real.finsetProd_rpow` + `Real.rpow_le_rpow` + `Real.rpow_natCast`.
- `harmonic_mean_inequality`: `n < x_m → (2:ℝ)^m < (3 + H/a)^a`, from
  `tstep_iterate_prod_identity` after splitting `∏(3x_i+1) = ∏(3x_i)·∏(1+1/(3x_i))` and
  cancelling `n·∏(3x_i)`. This is RT 4.2's `log 2 / log(3 + 1/h) ≤ a/m`.
- `three_mul_log_lt_harmSum` / `harmonicMean_lt_of_subcritical`: under `3^a < 2^m`,
  `Λ ≤ a·log(1 + H/(3a)) ≤ H/3`, so `3Λ < H` and `h < a/(3Λ)`.
- `segMin_le_harmonicMean`: `x_min ≤ h`, exhibiting this as strictly stronger than
  `TrunkBound.segMin_lt_of_subcritical`.
- `acyclicParadoxical_harmonicMean_lt`; `harmonicMean_control_seven_eight` kernel-checks
  `H = 1/7+1/11+1/17+1/13+1/5`, `a = 5`, `2^8 < (3+H/5)^5`.

All trust triple; **no** Rhin-lite native certificate is inherited (unlike TrunkBound's
polynomial corollary). A Rhin-lite polynomial corollary for `h` is not written; it would be
the verbatim analogue of `segMin_lt_poly_of_acyclicParadoxical` and would carry the eleven
allow-listed natives — the obvious next bounded leaf if anyone wants it.

## Standing position

Unchanged: the "awaiting a new mechanism" directive resumes. Nothing here claims new
mathematics or moves toward `U.Finite`; both nodes are formalization of known results
(RT Thm 4.2) and of the repository's own already-recorded statement-fidelity findings.
