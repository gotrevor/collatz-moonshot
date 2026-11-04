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

* Root imports added (`CollatzMoonshot.lean`; full `lake build CollatzMoonshot` green, 8904 jobs).
* Stretch (kickoff): DONE in `Conjugacy/BeyondWordsLetters.lean`.  `beyondWordCount_tendsto`: for
  every binary word `w` of length `K`, the proportion of `j`-bit starts whose parity letters
  `j, …, j+K−1` spell `w` tends to `2^{−K}` (axioms `propext, Classical.choice, Quot.sound`).  Bridge:
  `mod_two_pow_eq_prefixInt_iff` (first `K` letters of `m` are `w` iff `m ≡ prefixInt w K mod 2^K`,
  Terras at finite length via `letterMap_injective`), so `beyondWordCount_eq`.  Add it to the root
  imports with the others.

## Checkpoint (2026-11-04, final)

* Branch `wip/beyond-terras-words`, HEAD `3091ef7` before this commit; not pushed (host pushes).
* Commits this run: b4f4fdd (consistency), f4e4b01 (SliceFourierGeneral), 146f19c + e53e4fd
  (ResidueIndicator), a6ed9cc (main assembly), c76455f (letter form), 3091ef7 (root imports).
* `lake build CollatzMoonshot` green (8904 jobs); `box done --green` filed; treadmill stopped.
* Exact next steps (operator): review and open a PR from `wip/beyond-terras-words` into
  `ren/conjugacy-ladder`; optionally a `docs/notes/beyond-terras-words.md` note citing
  `beyondWordsUniform` and `beyondWordCount_tendsto` at a pinned commit.  No proof work open on
  this kickoff's path; remaining `src/` sorries are designated-open and untouched.
