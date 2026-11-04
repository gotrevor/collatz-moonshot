# HANDOFF 2026-11-04: the linear edge at its natural limit — GATE MET

Branch `wip/beyond-words-stretch`, worktree `~/src/collatz-moonshot-stretch`.
Kickoff: `KICKOFF-2026-11-04-beyond-words-stretch.md`.
Gate `sorry-free:CollatzMoonshot/Conjugacy/BeyondWordsLinearSharp.lean`: met (commit 7e42b47).

## Result

    theorem beyondWordsUniformLinear_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
        (hκ : κ < Real.logb 2 3 / 2) : BeyondWordsUniformLinear κ

    #print axioms beyondWordsUniformLinear_of_sliceOscDecay_sharp
      -- [propext, Classical.choice, Quot.sound]

Statement unchanged from the kickoff (`git diff 82ae007` removes only the `sorry`; the module
docstring's parameter sketch was updated to the scale actually used).  Root import added;
`lake build CollatzMoonshot` green (8907 jobs).

## Proof (all in `Conjugacy/BeyondWordsLinearSharp.lean`)

* `sum_levelSet_card_filter`, `beyondTV_le_of_band`: TV ≤ M + 2·#(off-band starts)/2^j for an
  arbitrary decidable band `P` on the odd-step count (generalises `beyondTV_le_of_slice`).
* `card_offBand_mul_le`, `two_mul_card_offBand_div_le`: Chebyshev for `|oddCount − j/2| > δj`,
  share `≤ 1/(2δ²j)`.
* `two_pow_div_three_pow_le`: `2^K/3^s ≤ exp(−η)^j` from `K ≤ kj`, `s ≥ ρj`,
  `ρ log 3 − k log 2 = η`.
* Main: `k = max κ 0`, `t = k log 2/log 3 < 1/2`, `g = 1/2 − t`, `δ = min(1/10, g/3)`,
  `ρ = t + g/3`, `η = (g/3) log 3`; scale `m = a − ⌈ρj⌉` (independent of `K` and `ε`, a
  simplification of the kickoff's `⌈K log₃2 + log₃(4/ε)⌉`).  Per band slice `≤ (ε/2)·card`.

## Stretch status

(a) aligned windows: not started.  (d) SEC6S-PLAN.md: not started.

(c) **levelOsc probe: done.**  `experiments/conjugacy/levelosc_table.js` (node; the box has no
numpy, so the `.py` twin is pure Python and only practical to `j ≈ 18`), output
`experiments/conjugacy/levelosc_table.out`, exact over all `2^j` starts, `j = 16, …, 26` (`j ≤ 14`
cross-checked between the two scripts).  Ratio `levelOsc j a m / card`, central slice `a = j/2`:

    j \ m   1     2     3     4     5     ... a-3   a-2   a-1
    16     .816  .659  .534  .431  .338        .265  .188  (m=a-1)
    20     .828  .680  .562  .466  .384        .254  .200  .144
    24     .834  .691  .579  .487  .411        .193  .152  .111
    26     .837  .696  .585  .495  .421        .168  .133  .098

Shape: at fixed co-scale `a − m` the ratio falls with `j` (`a−m = 1`: `.259 → .098` over
`j = 10 → 26`, ≈ 0.88 per digit); at fixed `m` it RISES with `j` toward a limit (increments
shrink geometrically; `m = 3` extrapolates to ≈ 0.61), and the extrapolated limits fall roughly
geometrically in `m` (≈ 0.86 per digit).  Not refuting; consistent with superpolynomial decay.
Caveat: the window edge `a ≈ 3j/5` is sparse (fewer starts than `3^a`) up to `j ≈ 210`, ratio at
small `m` ≈ 1.4–1.7 there.  Control: `m = a` gives 0.

Lean home: `Conjugacy/SliceOscGeometric.lean`: the conjecture node `SliceOscGeometric`
(`levelOsc ≤ C θ^m card` on the window, confidence 55%) and the proved edge
`sliceOscDecay_of_geometric : SliceOscGeometric → SliceOscDecay`.

## Checkpoint (2026-11-04, final)

* Branch `wip/beyond-words-stretch`, HEAD `df1ae88` before this commit; not pushed (host pushes).
* Commits this run: 7e42b47 (sharp edge proved, root import), e4eaaea (handoff), df1ae88
  (levelOsc probe, `SliceOscGeometric` node + edge).
* `box done --green` filed; treadmill stopped.
* `#print axioms` (both `[propext, Classical.choice, Quot.sound]`):
  `beyondWordsUniformLinear_of_sliceOscDecay_sharp`, `sliceOscDecay_of_geometric`.
* Exact next steps (operator): review/merge into the conjugacy-ladder branch; for a new kickoff,
  stretch (a) aligned windows (`BeyondWordsAligned.lean`, `beyondTVAt A j K` for `2^j ∣ A`, via
  `tstep_iterate_identity` and `oddCount (A + r) j = oddCount r j`) or (d) `SEC6S-PLAN.md`
  (port of `~/src/tao-collatz/TaoCollatz/Sec6/Mixing*.lean` to the sliced law, modelled on
  `SEC7P-PLAN.md`).  Probe extension: `j ≥ 28` needs a compiled language (node takes ~1 min at
  `j = 26`, ×4 per two steps).
