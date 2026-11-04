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

(a) aligned windows: not started.  (c) levelOsc probe: next.  (d) SEC6S-PLAN.md: not started.
