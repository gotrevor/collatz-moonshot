# KICKOFF 2026-11-04: the linear edge at its natural limit, aligned windows, and the node probe

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists and every older
`HANDOFF-*.md` for this branch** (`wip/beyond-words-stretch`, worktree
`~/src/collatz-moonshot-stretch`, based on `wip/beyond-words-linear` @ bfa745a, which proved
`beyondWordsUniformLog` and `beyondWordsUniformLinear_of_sliceOscDecay`).  Operator: Ren
(Claude), attended session 2026-11-04.  Lane: new mathematics (conjugacy ladder).

## The target

File: `CollatzMoonshot/Conjugacy/BeyondWordsLinearSharp.lean` (planted, builds green with one
`sorry`).  Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/BeyondWordsLinearSharp.lean`.

    theorem beyondWordsUniformLinear_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
        (hκ : κ < Real.logb 2 3 / 2) : BeyondWordsUniformLinear κ

FROZEN: never weaken, restate or re-hypothesise it.  If you believe it is false, write
`JUDGE-FLAG:` in the handoff with the exact obstruction and stop.  Build only what you touch:
`lake build CollatzMoonshot.Conjugacy.BeyondWordsLinearSharp` (every dependency is prebuilt; never
`lake update`).  Add the module to the root `CollatzMoonshot.lean` only once sorry-free.

## Why

`beyondWordsUniformLinear_of_sliceOscDecay` reaches `κ = 1/8` with the fixed scale `m = ⌊a/2⌋`
on the band `j ≤ 4a ≤ 11j/5`.  The per-slice bound it rests on,
`sum_norm_levelSum_resInd_le j a m K (hma : m ≤ a) : Σ_{c<2^K} ‖Σ_{r ∈ levelSet j a} resInd K c
(T^j r)‖ ≤ 2 levelOsc j a m + 2^K (3^m/3^a) card`, is general in `m`.  The natural limit of the
mechanism is `κ < (log₂ 3)/2 ≈ 0.792`: concentrate on `a ≈ j/2` and take `m` just far enough
below `a` that `2^K 3^{m−a}` is small.  (The write-up chain to a Collatz–Champernowne normal
number needs `ShortIntervalMixing C` with integer `C ≥ 2`, i.e. `κ ≥ 1`: NOT reachable this
way; do not pursue it.)

## The proof (execute; split into named lemmas; commit after each green lemma)

Read first: `BeyondWordsLinear.lean` end to end (`beyondTV_le_of_slice`,
`sum_norm_levelSum_resInd_le`, the proof of `beyondWordsUniformLinear_of_sliceOscDecay`),
`Bridge3Aux.lean` (`oddDeviation = 2·oddCount − j`, `sum_oddDeviation_sq_real : Σ_{r<2^j}
oddDeviation² = j 2^j`, `outOddSet`, `outOddSet_card_mul_sq_le`), `Bridge3.lean` (`levelSet`,
`levelOsc`), `SliceDecay.lean` (`SliceOscDecay` lives in `BeyondWordsLinear.lean`; its window is
`j ≤ 5a ≤ 3j`).

1. **Band Chebyshev.**  For `δ > 0`: the starts `r < 2^j` with `|oddCount r j − j/2| > δ j` number
   at most `2^j / (4 δ² j)` (`sum_oddDeviation_sq_real`; `|oddDeviation| > 2δj` on the complement).
   Define the band set `bandSet j δ` or reuse the `levelSet` decomposition: the slices `a` with
   `|a − j/2| ≤ δ j`, the rest is the complement.
2. **TV from slices on a general band.**  Generalise `beyondTV_le_of_slice` from the fixed band
   `j ≤ 4a ≤ 11j/5` with complement `outOddSet` to an arbitrary band predicate `P a` with
   complement mass `E`: `beyondTV j K ≤ M + 2 E / 2^j` whenever every slice with `P a` has
   `Σ_c ‖slice residue sum‖ ≤ M card` and the starts in slices with `¬P a` number `≤ E`.  (The
   existing proof charges non-band starts once in total; keep that.)
3. **Choice of parameters.**  Given `κ < (log₂ 3)/2` and `ε > 0`: let `δ := min (1/10)
   ((1/2 − κ / logb 2 3)/2) > 0`, so `κ · logb 3 2 < 1/2 − δ` and the band lies inside the
   `SliceOscDecay` window (`j ≤ 5a ≤ 3j` holds for `|a − j/2| ≤ j/10`, `j ≥ 10`).  Take `C` from
   `h` with `A = 1`.  For a slice `a` in the band and `K ≤ κ j`, set
   `m := a − ⌈K · logb 3 2 + logb 3 (4/ε)⌉` (as a natural number, `a − s` with `s := ⌈…⌉₊`); then
   `2^K · 3^{m−a} ≤ ε/4` (because `3^{a−m} ≥ 3^{K logb 3 2} · (4/ε) = 2^K · 4/ε`), and
   `m ≥ (1/2 − δ) j − κ j logb 3 2 − logb 3 (4/ε) − 1 ≥ c j − O(1)` with `c := (1/2 − δ) −
   κ logb 3 2 > 0`, so `m ≥ max 1 (8C/ε)` eventually in `j`, and `levelOsc j a m ≤ C m^{−1} card ≤
   (ε/8) card`.  Real-exponent bookkeeping: `(3:ℝ)^(logb 3 2 · K) = 2^K` via
   `Real.rpow_logb`/`Real.rpow_natCast`; compare `3^{a−m}` (a natural power) with the real power by
   `Real.rpow_le_rpow_left_iff` or by taking `logb 3` of both sides.
4. **Assembly.**  Per band slice: `Σ_c ‖…‖ ≤ 2 (ε/8) card + (ε/4) card = (ε/2) card`.  Step 2 with
   `M = ε/2`, `E = 2^j/(4δ² j)`: `beyondTV j K ≤ ε/2 + 2/(4 δ² j) ≤ ε` for `j ≥ 1/(δ² ε)`.  Unfold
   `BeyondWordsUniformLinear`; `∀ᶠ j` is `Filter.eventually_atTop` with the max of the thresholds.

Stretch (only after the gate passes; do (c) before filing `box done` if the budget allows, since
it is the measurement everything conditional hangs on):

(a) **Aligned windows** (new file `BeyondWordsAligned.lean`): `beyondCountAt A j K c :=
    ((Finset.Ico A (A + 2^j)).filter (fun r => T^j r % 2^K = c)).card`, `beyondTVAt A j K` likewise;
    for `2^j ∣ A`, `T^j (A + r) = T^j r + 3^a (A/2^j)` on `levelSet j a` (`tstep_iterate_identity`:
    `2^j T^j r = 3^a r + N`, with `oddCount (A + r) j = oddCount r j` since the first `j` parities
    depend on `r mod 2^j`), so per slice the residue sums are the same up to a shift of `c`, and
    both `beyondWordsUniformLog` and the two linear edges hold verbatim with `beyondTVAt A j K`
    for every aligned `A`.  State them as `…At` theorems with `∀ A, 2^j ∣ A →`.
(b) (done above.)
(c) **Probe** `experiments/conjugacy/levelosc_table.py`: tabulate `levelOsc j a m / card` for
    `j ≤ 22` (as far as feasible; `fsm_bridge.py` computes the slice laws exactly for `j ≤ 20`),
    `a` within `±2` of `j/2`, all `1 ≤ m ≤ a`.  The node says this is `≤ C m^{−A}` for every `A`;
    report the table and the empirical shape (power-law? geometric? flat?), no claim beyond the
    data.  Record it in the handoff.
(d) **Campaign spec** `SEC6S-PLAN.md` for the edge `SliceCharDecay → SliceOscDecay` (sliced Tao §6),
    modelled on `~/src/tao-collatz/SEC7P-PLAN.md`: the two structural facts (reducing a slice
    mod `3^k` is a mixture of slices; oscillation is subadditive over mixtures,
    `TaoCollatz.osc_sum_le`) and which of `TaoCollatz/Sec6/Mixing*.lean` port verbatim.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment;
  `decide` on small teeth is fine.
- Never edit statements in other files; new lemmas go in the gate file, in a new file, or
  (generalisations only, as NEW declarations) appended to `BeyondWordsLinear.lean`.  Do not touch
  `RESEARCH-*.md`, `DIRECTION.md`, `Maze.lean`; no `git add -A` (pathspec only).
- Handoff: `HANDOFF-2026-11-04-beyond-words-stretch.md` with `#print axioms` of the frozen theorem
  (expect only `propext`, `Classical.choice`, `Quot.sound`; the hypothesis is a binder), plus the
  probe table if (c) was reached.
- Lines ≤ 100 chars; docstrings on every new theorem.
