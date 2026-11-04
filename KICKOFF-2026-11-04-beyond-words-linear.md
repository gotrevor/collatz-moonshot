# KICKOFF 2026-11-04: beyond-Terras uniformity at growing depth (log depth unconditional; linear depth from one node)

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists and every older `HANDOFF-*.md`
for this branch** (`wip/beyond-words-linear`, worktree `~/src/collatz-moonshot-champmix`, based on
`wip/beyond-terras-words` @ 9ca5c33, which proved `beyondWordsUniform` and the letter form).
Operator: Ren (Claude), attended session 2026-11-04.  Lane: new mathematics (conjugacy ladder).

## The target

File: `CollatzMoonshot/Conjugacy/BeyondWordsLinear.lean` (planted, builds green with four `sorry`s).
Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/BeyondWordsLinear.lean`.

    noncomputable def beyondTV (j K : ℕ) : ℝ :=
      ∑ c ∈ Finset.range (2 ^ K), |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K|
    def SliceOscDecay : Prop := ∀ A > 0, ∃ C > 0, ∀ j a m, 1 ≤ m → m ≤ a → j ≤ 5a → 5a ≤ 3j →
      levelOsc j a m ≤ C * m^(-A) * (levelSet j a).card
    def BeyondWordsUniformLinear (κ : ℝ) : Prop := ∀ ε > 0, ∀ᶠ j, ∀ K, K ≤ κ j → beyondTV j K ≤ ε
    def BeyondWordsUniformLog : Prop := ∀ C, ∀ ε > 0, ∀ᶠ j, ∀ K, K ≤ C log₂ j → beyondTV j K ≤ ε

    theorem truncatedSyracMixing_of_sliceOscDecay (h : SliceOscDecay) : TruncatedSyracMixing
    theorem beyondWordsUniformLinear_of_sliceOscDecay (h : SliceOscDecay) : BeyondWordsUniformLinear (1/8)
    theorem beyondWordsUniformLog : BeyondWordsUniformLog            -- unconditional, the headline
    theorem beyondWordsUniform_of_log (h : BeyondWordsUniformLog) : BeyondWordsUniform

All six declarations are FROZEN: never weaken, restate or re-hypothesise them.  If you believe one
is false, write `JUDGE-FLAG:` in the handoff with the exact obstruction and stop.  Build only what
you touch: `lake build CollatzMoonshot.Conjugacy.BeyondWordsLinear` (every dependency is prebuilt;
never `lake update`).  Add the module to the root `CollatzMoonshot.lean` only once sorry-free.

## Why this is the right target

`beyondWordsUniform` (this branch's base) is the fixed-`K` statement.  `beyondWordsUniformLog` is its
first growing-depth form: the first `C log₂ j` parity letters past the Terras horizon are JOINTLY
uniform over the `j`-bit starts, for every `C`.  `SliceOscDecay` is the sliced Tao 2019 Prop 1.14;
its input, the sliced Prop 1.17, is the theorem `sliceCharDecay` (via Sec7P).  The linear-depth
edge shows that node is exactly what linear depth (`K = j/8`) costs.  Nothing here is about an
individual orbit; it is the ensemble rung of the ladder (research note §5).

## The proofs (execute; split into named lemmas; commit after each green lemma)

Read first: `BeyondWords.lean` end to end, `SliceFourierGeneral.lean` (`resFourier`,
`sum_levelSet_eq_fourier_slice`, `LayeredWeight`, `exists_norm_levelSum_le`,
`eventually_norm_levelSum_le`, `norm_sum_range_le_of_levelSum`), `ResidueIndicator.lean`
(`resInd`, `layeredWeight_resInd`: layered weight `4(a+1)` uniformly in `K, c`), `SliceDecay.lean`
(`SliceCharDecay`, `sliceCharDecay`: `‖sliceChar j a ξ‖ ≤ C j^{-A} card` on `j ≤ 5a ≤ 3j`, `3 ∤ ξ`),
`Bridge3.lean` (`levelSet`, `levelMass`, `levelClass`, `levelOsc`, `TruncatedSyracMixing`,
`abs_bias_le_of_levelMixing`), `Bridge3Aux.lean` (`outOddSet`, `outOddSet_card_mul_sq_le`).

1. **`truncatedSyracMixing_of_sliceOscDecay`.**  Given `ε`, apply `h` with `A = 1`.  For large
   `j` and `a` with `j ≤ 4a`, `a ≤ 11j/20` (inside `j ≤ 5a ≤ 3j`), take `m = a / 2` (nat division;
   `1 ≤ m` since `a ≥ j/4 ≥ 1`).  Then `3^m ≤ ε 3^a` because `a − m ≥ a/2 ≥ j/8 ≥ log₃(1/ε)`, and
   `levelOsc ≤ C m^{-1} card ≤ ε card` because `m ≥ j/8 − 1 ≥ C/ε`.

2. **`beyondWordsUniformLog`** (the headline).  Fix `C`, `ε`.  Re-run the assembly of
   `BeyondWords.lean` keeping the rate.  For a slice in the window and a residue `c < 2^K`, the
   centred count `Σ_{r ∈ levelSet j a} resInd K c (T^j r)` is bounded, through
   `sum_levelSet_eq_fourier_slice` and `layeredWeight_resInd`, by (frequencies `3 ∤ ξ`)
   `4(a+1) · C_A j^{-A} · card` plus (frequencies `3^k ∣ ξ`, `k ≥ 1`) the sub-slice terms.  Keep
   whatever cutoff `SliceFourierGeneral` uses for the sub-slices (`s ≤ j/12`-type): the terms below
   the cutoff decay like `j^{-A}` through `sliceCharDecay` on the sub-slices, the terms above are
   bounded by their layered weight `3^{-k}(a−k+1) · card ≤ a 3^{-j/12} card`.  If the existing
   `exists_norm_levelSum_le` hides its rate behind `∀ ε, ∃ j₀`, add a quantitative sibling
   `norm_levelSum_le_rate : ∃ C', ∀ A, ∃ C'', ∀ j a K c (window), ‖levelSum‖ ≤ C'' (a+1) j^{-A} card
   + C' a 3^{-j/12} card`; do not edit the existing statements.  Then, with `2^K ≤ j^C`,

       beyondTV j K ≤ Σ_c Σ_{a in window} ‖levelSum‖ / 2^j + 2 · (outOddSet j).card / 2^j
                    ≤ j^C · (C'' (j+1) j^{-A} + C' j 3^{-j/12}) + 2 · (outOddSet j).card / 2^j,

   and `A = C + 2` makes the first term `O(1/j)`; `outOddSet_card_mul_sq_le` makes the last
   `O(1/j)`.  (The `outOddSet` slices contribute at most `2 · card / 2^j` to the TV sum: once as
   their counts, once as their share of the uniform mass; `Σ_c beyondCount j K c = 2^j`.)
   Residues `c` with `2^K > j^C` do not occur, since `K ≤ C log₂ j` means `2^K ≤ j^C`.

3. **`beyondWordsUniformLinear_of_sliceOscDecay`.**  Apply `h` with `A = 1` and `m = a / 2` on
   every slice with `j ≤ 4a ≤ 11j/5` (the `outOddSet` complement).  Unfold `levelOsc` and read it
   as the `ℓ¹` distance between the slice counts `levelMass j a y`, `y < 3^a`, and the fibrewise
   averages `levelClass j a m (y mod 3^m) / 3^{a−m}` (check the exact definition and adapt).  For
   the averaged law, the count of `y ≡ d (mod 2^K)` inside a fibre `{c + 3^m t : t < 3^{a−m}}` is
   `3^{a−m}/2^K + O(1)` because `3^m` is odd, so `t ↦ c + 3^m t mod 2^K` runs over a complete
   residue system every `2^K` consecutive `t`.  Hence for each slice
   `Σ_d |#{r ∈ slice : T^j r ≡ d (2^K)} − card/2^K| ≤ levelOsc j a m + 2^K · 3^{m} · 3^{-a} · card`
   (the `O(1)` per fibre, summed over `3^m` fibres and `2^K` residues, against the fibre mass).
   With `m = a/2` and `a ≥ j/4`: `2^K 3^{m−a} ≤ 2^K 3^{-j/8} ≤ 2^{K − 0.198 j}`, which is
   `≤ 2^{-0.07 j}` for `K ≤ j/8`.  Sum over slices (card weights) and add the `outOddSet` term as in
   step 2.  Numerics on the way, if useful: `experiments/conjugacy/fsm_bridge.py` computes the
   slice laws exactly for `j ≤ 20`.

4. **`beyondWordsUniform_of_log`.**  For fixed `K` and `c`, `K ≤ 1 · log₂ j` eventually, and
   `|beyondCount j K c / 2^j − 2^{-K}| ≤ beyondTV j K`.

Stretch (only after the gate passes; separate file `BeyondWordsLinearAligned.lean`):
(a) the aligned-window form: for `2^j ∣ A`, `T^j (A + r) = T^j r + 3^a · (A / 2^j)` on
`levelSet j a` (`tstep_iterate_identity`), so every TV statement above holds verbatim for the window
`[A, A + 2^j)`; (b) `BeyondWordsUniformLinear κ` for every `κ < (log₂ 3)/2` from `SliceOscDecay`,
by a Chebyshev tail on `|a − j/2|`; (c) a probe `experiments/conjugacy/levelosc_table.py` tabulating
`levelOsc j a m / card` for `j ≤ 22` to test the `m^{-A}` shape of `SliceOscDecay` (a refutation
probe for the node; record the result in the handoff, no claim beyond the data); (d) a campaign spec
`SEC6S-PLAN.md` for the edge `SliceCharDecay → SliceOscDecay`, modelled on `SEC7P-PLAN.md` in
tao-collatz: the two structural facts (reducing a slice mod `3^k` is a mixture of slices;
oscillation is subadditive over mixtures, `TaoCollatz.osc_sum_le`) and which of
`TaoCollatz/Sec6/Mixing*.lean` port verbatim.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment;
  `decide` on small teeth is fine.
- Never edit statements in other files; new lemmas go in this file, in a new file, or (quantitative
  siblings only) appended to `SliceFourierGeneral.lean`.  Do not touch `RESEARCH-*.md`,
  `DIRECTION.md`, `Maze.lean`; do not `git add -A` (pathspec only).
- Handoff: `HANDOFF-2026-11-04-beyond-words-linear.md` with `#print axioms` of all four theorems
  (expect only `propext`, `Classical.choice`, `Quot.sound` for `beyondWordsUniformLog` and
  `beyondWordsUniform_of_log`; the two conditional edges likewise, their hypothesis being a binder),
  and the probe table if (c) was reached.
- Lines ≤ 100 chars; docstrings on every new theorem.
