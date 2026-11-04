# HANDOFF 2026-11-04: beyond-Terras uniformity on every aligned window — GATE MET

Branch `wip/beyond-words-stretch`, worktree `~/src/collatz-moonshot-stretch`.
Kickoff: `KICKOFF-2026-11-04-beyond-words-aligned.md`.
Gate `sorry-free:CollatzMoonshot/Conjugacy/BeyondWordsAligned.lean`: met (commit 7895fff).

## Result

    theorem beyondWordsUniformLogAt :
        ∀ C : ℝ, ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ C * Real.logb 2 j →
          ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε
    theorem beyondWordsUniformLinearAt_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
        (hκ : κ < Real.logb 2 3 / 2) :
        ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * j →
          ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε

    #print axioms beyondWordsUniformLogAt                              -- [propext, Classical.choice, Quot.sound]
    #print axioms beyondWordsUniformLinearAt_of_sliceOscDecay_sharp    -- [propext, Classical.choice, Quot.sound]
    #print axioms beyondTVAt_zero                                      -- [propext, Classical.choice, Quot.sound]

Statements of all three planted theorems are byte-identical to the kickoff commit 464c5da
(checked by diffing each `theorem … := by` header).  Root import added; `lake build
CollatzMoonshot` green (8909 jobs).  The bounds are uniform in `q` (the `∀ q` sits inside the
`∀ᶠ j`), as frozen.

## Proof (all in `Conjugacy/BeyondWordsAligned.lean`)

* `tstep_iterate_add_mul`: `T^j (r + q 2^j) = T^j r + 3^(oddCount r j) q`, for every `r` (no
  `r < 2^j` needed), from `tstep_iterate_identity` twice and `OrbitPacking.traceWord_add_mul`.
* `sum_norm_sum_resInd_add`: for any finite family `y` and shift `s`,
  `Σ_{c<2^K} ‖Σ_r resInd K c (y r + s)‖ = Σ_{c<2^K} ‖Σ_r resInd K c (y r)‖`, by
  `Finset.sum_nbij'` with `c ↦ (c − s).val` in `ZMod (2^K)` (helper `mod_eq_iff_zmod`).
* `sum_resInd_window_eq`, `sum_resInd_window_eq_sum_levelSet`: the window's centred sum via
  `Finset.sum_Ico_eq_sum_range`, split by slices of the offset.
* `beyondTVAt_le_of_band`: same hypothesis as `beyondTV_le_of_band` (the first window's per-slice
  bound), same conclusion for `beyondTVAt (q 2^j) j K`.
* The frozen theorems: the assemblies of `beyondWordsUniformLog` and
  `beyondWordsUniformLinear_of_sliceOscDecay_sharp` copied, final TV step replaced by
  `beyondTVAt_le_of_band` (log: band `j ≤ 4a ∧ a ≤ 11j/20`, off-band set identified with
  `outOddSet j` by `omega`).

## Stretch status

(c') probe at `j = 28..32`: see below / PENDING_WORK.  (d) `SEC6S-PLAN.md`: see below.

## Checkpoint

* Commits: 4ed589a (helpers, teeth, window band lemma), 7895fff (frozen theorems, root import).
* Not pushed (host pushes).
