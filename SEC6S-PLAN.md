# SEC6S-PLAN — Tao §6 for the slice laws (the edge `SliceCharDecay → SliceOscDecayCentral`)

*Campaign spec, 2026-11-04 (kickoff `KICKOFF-2026-11-04-beyond-words-aligned.md`, item (d)).
Model: `~/src/tao-collatz-sec7p/SEC7P-PLAN.md`.  Sources read: `TaoCollatz/Sec6/*.lean` (as the
lake dependency `.lake/packages/TaoCollatz`), `TaoCollatz/Fourier/ZMod3.lean`.  The transfer
in §2–§3 is paper-level; every load-bearing claim below names the Lean statement that records
it.*

## 0. What changed while writing this plan

The kickoff asked for the edge `SliceCharDecay → SliceOscDecay` (window `1/5 ≤ a/j ≤ 3/5`).  Tao's
§6 mechanism does **not** reach that window; it reaches the CLT band around `a/j = 1/2`, and
that band is all the consumers need.  So the campaign target is re-scoped (all in
`Conjugacy/SliceOscCentral.lean`):

| statement | status |
|---|---|
| `SliceOscDecayCentral` (node: `levelOsc ≤ C m^{−A} card` on `|2a − j| ≤ K√j`, every `A`, `K`) | node |
| `sliceOscDecayCentral_of_sliceOscDecay` (window node ⇒ central node) | proved |
| `beyondWordsUniformLinear_of_sliceOscDecayCentral` (linear depth `κ < (log₂3)/2` from the central node) | proved |
| `tail_budgets_incompatible` (the obstruction kernel, §3) | proved |
| `SliceOscStep` (node: one scale step `osc_{a−1,a} ≤ C a^{−A} card` on `|2a − j| ≤ K√(j log j)`) | node |
| **target 1** `sliceOscStep_of_sliceCharDecay` | frozen `sorry`, 55% |
| **target 2** `sliceOscDecayCentral_of_sliceOscStep` | frozen `sorry`, 80% |

The consumers' chain is then `sliceCharDecay` (theorem, via Sec7P) → target 1 → target 2 →
`beyondWordsUniformLinear_of_sliceOscDecayCentral`.

## 1. The sliced objects (item i) — DONE in Lean

* Slice law: `levelMass j a y = #{r < 2^j : oddCount r j = a, T^j r = y}`, supported on
  `y < 3^a` (`tstep_iterate_lt_three_pow`).  As a density on `ZMod (3^a)`: `sliceDensity j a`
  (`Conjugacy/SliceOscBridge.lean`).
* **Bridge** `levelOsc_eq_osc : levelOsc j a m = TaoCollatz.osc m a hma (sliceDensity j a)`
  (proved, axioms `propext, Classical.choice, Quot.sound`).  Consequently every `Sec6` lemma
  that is generic in the density applies to slices by `rw [levelOsc_eq_osc]`; first use:
  `levelOsc_le_two_mul_card` from `TaoCollatz.osc_le_two_mul_l1`.
* The Sec6 generic lemmas are **imported** from the lake dependency (no vendoring needed, and
  none done).

## 2. The two structural facts (item ii)

**(a) Reduction mod `3^{a'}` is a mixture of sub-slices.**  In the repo's convention the slice
law on `ℤ/3^a` is `Σ_k 3^{k−1} 2^{−T_k}`, `T_1 < … < T_a` a uniform `a`-subset of `[1, j]`.  Mod
`3^{a'}` only `T_1, …, T_{a'}` matter; given `T_{a'+1} = t` they are a uniform `a'`-subset of
`[1, t−1]`, i.e. the slice `(t − 1, a')`.  In counts:

    levelClass j a a' c = Σ_{t=1}^{j} C(j − t, a − a' − 1) · levelMass (t − 1) a' c     (a' < a)

Exact check `experiments/conjugacy/mixture.py` (`mixture.out`): 455 triples `(j, a, a')`,
`j ≤ 13`, all `c`, 0 mismatches; control (weight `C(j−t, a−a')`) 449/455 mismatches.  At
`a' = a − 1` the weights are all `1`: the slice mod `3^{a−1}` is literally the sum of the slices
`(t − 1, a − 1)`, `t ≤ j`.  **Lean statement owed** (lap 1): `levelClass_eq_sum_levelMass`.
Route: the trace word of `r` splits at its `(a'+1)`-th one; `numer` of a concatenation
(`FrontB/Words.lean`) gives the residue; count the suffixes.

**(b) Oscillation is subadditive over mixtures.**  `TaoCollatz.osc_sum_le` verbatim (generic in
the density), through the bridge.

Together with the generic levels triangle (Sec6 `osc_syracZ_levels_triangle`, whose proof uses
only lifts, restated for an arbitrary density and its pushforward) these give the telescope
(target 2):

    osc_{m,a}(slice j a) ≤ osc_{a−1,a}(slice j a) + Σ_{t ≤ j} osc_{m,a−1}(slice (t−1) (a−1))

and, unrolled, `osc_{m,a}(j, a) ≤ Σ_{k=m+1}^{a} Σ_{j'} w_k(j') · osc_{k−1,k}(slice j' k)` with
`Σ_{j'} w_k(j') card(j', k) = card(j, a)`.  Sub-slices with `|2k − j'| > K'√(j' log j')` carry
`O(k^{−A−2})` of the mass for `K' = K'(A)` (hypergeometric tail of `T_{k+1}`), charged by
`levelOsc_le_two_mul_card`; the rest use `SliceOscStep`.  This is exactly Tao's (6.1)
(`osc_syracZ_regime_telescope_at` only calls its high-regime hypothesis at `(k+1, k)`), with
consistency (1.22) replaced by the mixture.

## 3. The conditioning step and where it stops (item iii)

**Tao (6.2)–(6.10) at one step `(a−1, a)`, for slices.**  Condition on `T_{p+1} = t`.  Then
`X = tail + 3^p 2^{−t} (1 + 3·head)` with tail a uniform `p`-subset of `[1, t−1]` (low digits)
and head a uniform `(a−p−1)`-subset of `[t+1, j]` shifted to `[1, j−t]` (high digits),
**independent given `t`**.  So the conditioned character sum factors exactly (cleaner than
Tao's: no geometric iid, just two uniform subsets); for `3 ∤ ξ` the head factor is a slice
character sum of `(j − t, a − p − 1)` at a unit frequency, `≤ C_B a^{−B} card` by
`SliceCharDecay` once that sub-slice is in `[1/5, 3/5]`.  The tail factor's `ℓ²` mass is the
tail collision entropy, bounded by injectivity of the tail integer
`N = Σ_{k≤p} 3^{k−1} 2^{t−T_k}` below `3^a` (Tao's `fnat_lt_of_suffix_window`).

**The obstruction.**  The two tail budgets are

* entropy: per-configuration slice probability `C(j−t, a−p−1)/C(j,a) ≈ e^{−t H(ρ)}` must be
  `≲ 3^{−a} a^{O(C_A²)}` (Tao: `2^{−l} ≈ 3^{−n} n^{C_A²}`), so `a log 3 ≤ t H(ρ) + O(log a)`;
* injectivity: `N ≈ 2^t < 3^a`, so `t log 2 ≤ a log 3 − O(log a)`.

`tail_budgets_incompatible` (proved): for `ρ ≠ 1/2` no `t > 0` meets both, since
`H(ρ) < log 2`.  With the `O(C_A² log a)` slack, and `log 2 − H(ρ) ≈ 2(ρ − 1/2)²`, they are
compatible iff `|ρ − 1/2| ≲ C_A √(log a / a)`, i.e. on `|2a − j| ≤ K √(j log j)` with
`K ≲ C_A`, which is why `SliceOscStep` carries that band (`C_A` is chosen after `K`).  At
`ρ = 1/2` the budgets coincide: Tao's case.  **Reopen condition for the full window**: an
`ℓ²`-spreading bound for off-centre tail integers mod `3^a` that does not go through
injectivity; no mechanism known.  (The same budgets explain the head share: on the band the
head keeps `1 − log 3/log 4 ≈ 0.2075` of the odd steps, Tao's ratio; at `ρ = 0.55` it would be
`0.122`, at `0.6` only `0.021`, at the entropy cutoff `ρ ≈ 0.609` zero.)

**Which Sec6 pieces port how.**

| Sec6 piece | port |
|---|---|
| `osc_eq_sum_norm_devC`, `devC_eq_highfreq_invDFT`, `sum_norm_sq_devC_eq`, `osc_le_sqrt_highfreq`, `highfreq_l2_le_collision`, `osc_add_le`, `osc_sum_le`, `osc_le_two_mul_l1`, `sum_sq_le_max_mul_sum`, `coset_char_sum`, `fiber_card`, `sum_comp_castHom` | **imported verbatim** (generic in the density) |
| `osc_syracZ_levels_triangle`, `osc_syracZ_le_sum_steps`, `osc_syracZ_regime_telescope_at` | proof text generic; restate for a density + its pushforward; consistency (1.22) → mixture §2(a) |
| `cond_char_factor`, `condDens`, `dft_condDens_eq_cond_char`, `tailDens` | **rewrite**: conditioning on `T_{p+1} = t` over words (`traceWord`, `numer` of a concatenation); exact independence replaces `geomHalf.iid` |
| `head_factor_*`, `head_uniform_highFreq_of_margin_at` | **rewrite** with `SliceCharDecay` in place of `charFn_decay` (Prop 1.17); `zmod_three_factor` imported |
| `fnat_lt_of_suffix_window`, `tailDensW_le_single_mass`, `condWindow`, `stopEvent`, `lRange`, `caThr` | **rewrite** on the band: suffix window for `T_k` against `k/ρ`, threshold `a log 3/H(ρ)`; injectivity algebra (`sum_two_pow_lt`) reusable |
| `globalGood`, `g1/g2/g3_mass_le`, `prob_not_globalGood_le` | **Syracuse-specific**: replace geometric tail bounds by slice (hypergeometric) tails; route: `P_slice(E) ≤ P_{Bernoulli(ρ)}(E)/P(#ones = a)` with `P(#ones = a) ≍ j^{−1/2}` (the SliceDecay docstring's conditioning-cost trick), so any `n^{−A}` geometric bound survives |
| `mainDecayExponent`, `main_polynomial_loss_absorbed`, constant bookkeeping | adapt (same polynomial-loss accounting) |

## 4. Lap plan (gates, sorry budget ≤ 6 named leaves at any time)

1. **Mixture + telescope skeleton** (`SliceTelescope.lean`): `levelClass_eq_sum_levelMass`
   (§2a); generic `osc_levels_triangle`; target 2 reduced to one named leaf
   `sliceMixture_offBand_le` (hypergeometric tail).  Gate: target 2's `#print axioms` shows only
   that leaf's `sorryAx`.  Probe already done (`mixture.py`).
2. **Hypergeometric tail**: `sliceMixture_offBand_le` via the second moment of `T_{k+1}`
   (Chebyshev suffices only for fixed `K'`; `k^{−A}` needs `A`-th moments or a Chernoff bound —
   use the Bernoulli(`1/2`) bit representation, all `r < 2^j`, as in `sum_oddDeviation_sq`).
   Gate: target 2 sorry-free.
3. **Slice conditioning factorization** (`SliceCondition.lean`): words split at the
   `(p+1)`-th one; exact `cond_char_factor` analogue; DFT bridge.  Gate: proved.
4. **Head factor** from `SliceCharDecay` (valuation peel `zmod_three_factor`, sub-slice window
   bookkeeping).  Gate: proved.
5. **Tail injectivity + Rényi** on the band (suffix window, threshold, `hbudget` analogue).
   Expected crux: the band-dependent budget `(log 2 − H(ρ)) t ≤ C_A² log a`.  Gate: proved.
6. **Bad events (6.3)** via the conditioning-cost trick; assembly of target 1.  Gate: target 1
   sorry-free; `#print axioms` of `beyondWordsUniformLinear_of_sliceOscDecayCentral ∘ …`
   composed with `sliceCharDecay` = base three.

Rules for the campaign: never edit the frozen statements above (a `JUDGE-FLAG` if one is
believed false); no vendoring from `tao-collatz` (import from the dependency; port by rewriting
when a statement is Syracuse-specific); one `lake build` at a time.

## 5. Probe status (`experiments/conjugacy/levelosc_table.c`, exact, `j ≤ 36`)

`levelosc_table_c.out`, central slice `a = j/2`: at fixed co-scale `a − m` the ratio falls by a
very stable `0.872–0.873` per two steps of `j` (`a − m = 1`: `0.188 → 0.050` over
`j = 16 → 36`); at fixed `m` it still rises at `j = 36` with increments shrinking only like
`≈ j^{−2}` (per-two-step increment ratios `0.89–0.93`), so the handoff's `j = 26` geometric
extrapolation (`m = 3 → 0.61`) is refuted: `m = 3` is `0.607` at `j = 36` and rising; a
power-law extrapolation gives `≈ 0.67`.  Fixed-`m` values at `j = 36`: `m = 1, 2, 3, 4, 6, 8`:
`0.846, 0.712, 0.607, 0.523, 0.396, 0.298` (about `0.87` per unit `m`, drifting toward `0.9`).
Not refuting `SliceOscDecayCentral` (bounded data cannot); `SliceOscGeometric` stays open with
a weaker-looking ratio.
