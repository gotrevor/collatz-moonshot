# HANDOFF 2026-11-04: beyond-Terras uniformity at growing depth — DONE

Branch `wip/beyond-words-linear`, worktree `~/src/collatz-moonshot-champmix`.
Kickoff: `KICKOFF-2026-11-04-beyond-words-linear.md`.
Gate `sorry-free:CollatzMoonshot/Conjugacy/BeyondWordsLinear.lean`: met.

## Results

* `beyondWordsUniformLog` (unconditional): for every `C`, `ε`, eventually every depth
  `K ≤ C log₂ j` has `beyondTV j K ≤ ε`.  The first `C log₂ j` parity letters past the Terras
  horizon are jointly uniform over the `j`-bit starts, in total variation.
* `beyondWordsUniformLinear_of_sliceOscDecay`: the sliced Prop 1.14 node gives the same to depth
  `K ≤ j/8`.
* `truncatedSyracMixing_of_sliceOscDecay`: the node gives `TruncatedSyracMixing` (`m = ⌊a/2⌋`).
* `beyondWordsUniform_of_log`: log depth recovers the fixed-`K` statement.

    #print axioms beyondWordsUniformLog                      -- [propext, Classical.choice, Quot.sound]
    #print axioms beyondWordsUniform_of_log                  -- [propext, Classical.choice, Quot.sound]
    #print axioms truncatedSyracMixing_of_sliceOscDecay      -- [propext, Classical.choice, Quot.sound]
    #print axioms beyondWordsUniformLinear_of_sliceOscDecay  -- [propext, Classical.choice, Quot.sound]

Frozen statements unchanged: `git diff 8338b5e -- BeyondWordsLinear.lean` removes only the four
`sorry`s and the old `open Filter Topology` line (widened to add `CollatzMoonshot.FrontB`).

## Where the proof lives

* `Conjugacy/SliceFourierRate.lean` (new): `exists_norm_sliceChar_pow_le_rate`,
  `exists_norm_levelSum_le_rate` (the pipeline at any exponent `n`; the old one hard-wires
  `A = 2`), `logMajorant`, `tendsto_logMajorant` (the majorant at exponent `N+2`, inflated by
  `j^N`, still → 0).
* `Conjugacy/BeyondWordsLinear.lean`:
  - `sum_norm_resInd_le` (one start carries mass ≤ 2 over all residues),
    `beyondTV_le_of_slice` (TV ≤ M + 2·outOdd/2^j from per-slice residue-sum bounds; the
    non-central starts are charged once in total, not once per residue — this is what makes the
    `2^K = j^N` sum affordable);
  - `abs_card_progression_sub_le` (odd-step progression equidistributed mod `2^K` up to one
    point, via `Nat.count_modEq_card`), `norm_sum_resInd_progression_le`,
    `sum_levelSet_eq_sum_mass`, `sum_levelClass_eq_card`, `sum_range_mul_eq_sum_sum`;
  - `sum_norm_levelSum_resInd_le`: per slice, `Σ_c ‖slice residue sum‖ ≤ 2 levelOsc j a m +
    2^K 3^{m−a} #slice` for every `m ≤ a`.

Root imports added (`SliceFourierRate`, `BeyondWordsLinear`); `lake build CollatzMoonshot` green
(8906 jobs).

## Not done (stretch, kickoff §Stretch; none on the gate path)

(a) aligned-window form; (b) `BeyondWordsUniformLinear κ` for all `κ < (log₂ 3)/2` (with
`sum_norm_levelSum_resInd_le` in hand this needs only a Chebyshev tail on `|a − j/2|` and a
better choice of `m`; the per-slice bound is already general in `m`); (c) the `levelOsc` table
probe for the `m^{−A}` shape of `SliceOscDecay`; (d) `SEC6S-PLAN.md` for
`SliceCharDecay → SliceOscDecay`.
