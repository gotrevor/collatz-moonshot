# HANDOFF 2026-11-03/04: beyond-Terras words are uniform (the K-letter C1) — DONE

Branch `wip/beyond-terras-words`, worktree `~/src/collatz-moonshot-beyondwords`.
Kickoff: `KICKOFF-2026-11-03-beyond-terras-words.md`.  Gate `sorry-free:CollatzMoonshot/Conjugacy/BeyondWords.lean`: met.

## Result

`BeyondWordsUniform`: for every `K` and `c < 2^K`, `#{r < 2^j : T^j r ≡ c (mod 2^K)} / 2^j → 2^{−K}`.
Every fixed-length word of parities past the Terras horizon is asymptotically uniform.  Unconditional
(`beyondWordsUniform`, through `sliceCharDecay_of_pascalDampingDecay pascalDampingDecay`).

    #print axioms beyondWordsUniform                    -- [propext, Classical.choice, Quot.sound]
    #print axioms beyondWordsUniform_of_sliceCharDecay  -- [propext, Classical.choice, Quot.sound]
    #print axioms biasDecays_of_beyondWordsUniform      -- [propext, Classical.choice, Quot.sound]

Frozen statements unchanged (the only removed lines in `BeyondWords.lean` are the two `sorry`s).

## Where the proof lives

* `Conjugacy/SliceFourierGeneral.lean`: the C1 pipeline for an arbitrary observable `f : ℕ → ℂ`:
  `resFourier`, `sum_levelSet_eq_fourier_slice`, `LayeredWeight`, `exists_norm_levelSum_le`,
  `eventually_norm_levelSum_le`, `norm_sum_range_le_of_levelSum`; `layeredWeight_paritySign` shows
  parity is an instance.
* `Conjugacy/ResidueIndicator.lean`: the centred indicator `resInd K c` and
  `layeredWeight_resInd` (layered weight `4(a+1)`, uniformly in `K`, `c`), via
  the geometric-sum closed form `resFourier_resInd`, `norm_resFourier_resInd_le`
  (`≤ 3^{−a}(1/|sin(π(2^K ξ)/3^a)| + 1)`), the unit reindex `dvd_val_two_pow_mul_iff`, and
  `sum_inv_abs_sin_le` (`Σ_{u<N} 1/|sin(πu/N)| ≤ N·H_N`).
* `Conjugacy/BeyondWords.lean`: `norm_resInd_le_one`, `sum_resInd_eq`, the assembly, and
  `bias_eq_two_mul_beyondCount` for the consistency check.

## Not done / next

* The new modules are not imported from the root `CollatzMoonshot.lean` (kickoff: build only what you
  touch).  Add `SliceFourierGeneral`, `ResidueIndicator`, `BeyondWords` there on the next full build.
* Stretch (kickoff): `BeyondWordsLetters.lean`, the word form via the Terras bijection
  `m mod 2^K ↔ first K parities` (`accWord_congr_mod`).  Not started.
