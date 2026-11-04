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

## Stretch status (after the gate)

**(c') probe to `j = 36`: done.**  `experiments/conjugacy/levelosc_table.c` (C, threads; the box
has no system C compiler or libc headers, so it declares its few libc prototypes and builds with
Lean's bundled toolchain: `leanc -O2 levelosc_table.c -o …`; j = 32 in 40 s, j = 36 in ~12 min
on 16 threads).  Output `levelosc_table_c.out` (5 decimals, `j = 16..36`, central `a = j/2 ± 1`,
edge `a = ⌊3j/5⌋` to `j = 32`), matching the node table at `j = 16, 20, 26` exactly.  Bug caught
and fixed: `uint32` class counts overflow at `j = 36` (slice values are never `≡ 0 mod 3`, so each
nonzero class mod 3 holds `n/2 > 2^32`); classes are `uint64` now.
* Fixed co-scale `a − m`: ratio `0.872–0.873` per two steps of `j`, very stable.
* Fixed `m`: still rising at `j = 36`; increments shrink only like `≈ j^{−2}`.  The `j = 26`
  extrapolation `m = 3 → 0.61` is **refuted** (`0.607` at `j = 36`, rising; power-law
  extrapolation `≈ 0.67`).  Values at `j = 36`, `m = 1,2,3,4,6,8`: `.846 .712 .607 .523 .396 .298`.
* Not refuting `SliceOscDecayCentral`/`SliceOscDecay`; `SliceOscGeometric` looks weaker (ratio
  per `m` drifting from `0.87` toward `0.9`).

**(d) `SEC6S-PLAN.md`: written**, plus Lean:
* `Conjugacy/SliceOscBridge.lean` (sorry-free): `levelOsc_eq_osc` (`levelOsc = TaoCollatz.osc` of
  `sliceDensity`), `levelOsc_le_two_mul_card`.
* `Conjugacy/SliceOscCentral.lean`: **finding** — Tao's §6 tail budgets (entropy `a log 3 ≤ t H(ρ)`,
  injectivity `t log 2 ≤ a log 3`) are compatible only at `ρ = 1/2` up to `√(log a/a)`
  (`tail_budgets_incompatible`, proved).  So the edge targets the CLT band: node
  `SliceOscDecayCentral`; proved `sliceOscDecayCentral_of_sliceOscDecay` and
  `beyondWordsUniformLinear_of_sliceOscDecayCentral` (same depth `κ < (log₂3)/2`); frozen campaign
  targets `sliceOscStep_of_sliceCharDecay` (55%) and `sliceOscDecayCentral_of_sliceOscStep` (80%),
  via the node `SliceOscStep` (one scale step on the `√(j log j)` band).
* `experiments/conjugacy/mixture.py` / `.out`: the slice mixture identity
  `levelClass j a a' c = Σ_t C(j−t, a−a'−1) levelMass (t−1) a' c` exact on 455 triples (`j ≤ 13`);
  control weight off by one fails 449/455.

`#print axioms` (all `[propext, Classical.choice, Quot.sound]`): `levelOsc_eq_osc`,
`levelOsc_le_two_mul_card`, `sliceOscDecayCentral_of_sliceOscDecay`,
`beyondWordsUniformLinear_of_sliceOscDecayCentral`, `tail_budgets_incompatible`.

## Checkpoint

* Commits: 4ed589a, 7895fff (gate), d4beab0 (handoff), f9e9da4 (bridge), 9fc28c3 (central node,
  edges, targets), 454d1e2 (probe + mixture check), ff69755 (plan + handoff); HEAD after this checkpoint commit. `box done --green` filed.
* Root imports: `BeyondWordsAligned`, `SliceOscBridge`, `SliceOscCentral`; `lake build
  CollatzMoonshot` green (8913 jobs).  Not pushed (host pushes).
* Next (SEC6S lap 1): `levelClass_eq_sum_levelMass` in Lean (the mixture identity), generic levels
  triangle, target 2 down to the hypergeometric-tail leaf.
