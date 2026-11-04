# KICKOFF 2026-11-03: beyond-Terras words of every fixed length are uniform (the K-letter C1)

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists and every older `HANDOFF-*.md`
for this branch** (`wip/beyond-terras-words`, worktree `~/src/collatz-moonshot-beyondwords`, based on
`ren/conjugacy-ladder` @ 4c671fc).  Operator: Ren (Claude), attended session 2026-11-03/04.
Lane: new mathematics (Collatz conjugacy ladder, the rung just above C1).

## The target

File: `CollatzMoonshot/Conjugacy/BeyondWords.lean` (planted, builds green with two `sorry`s).

    def beyondCount (j K c : ℕ) : ℕ :=
      ((Finset.range (2 ^ j)).filter (fun r => tstep^[j] r % 2 ^ K = c)).card

    def BeyondWordsUniform : Prop :=
      ∀ K c : ℕ, c < 2 ^ K →
        Tendsto (fun j : ℕ => (beyondCount j K c : ℝ) / 2 ^ j) atTop (𝓝 (1 / 2 ^ K))

    theorem beyondWordsUniform_of_sliceCharDecay (h : SliceCharDecay) : BeyondWordsUniform
    theorem biasDecays_of_beyondWordsUniform (h : BeyondWordsUniform) : BiasDecays

Both statements are FROZEN (never weaken, restate or re-hypothesise).  `beyondWordsUniform`
(unconditional, via `pascalDampingDecay`) is already wired and needs nothing.  Host gate:
`--done-when sorry-free:CollatzMoonshot/Conjugacy/BeyondWords.lean`.  Build only what you touch:
`lake build CollatzMoonshot.Conjugacy.BeyondWords` (the `TaoCollatz` dependency is prebuilt in
`.lake/packages`; never `lake update`).

## Why this is the right target

C1 (`biasDecays`, PR #87) says the `j`-th parity letter of a uniform `j`-bit start is asymptotically
balanced.  The first `K` letters past the Terras horizon are the parities of `T^j r, …, T^{j+K−1} r`,
a bijective function of `T^j r mod 2^K` (Terras).  So `BeyondWordsUniform` says: **every fixed-length
beyond-Terras word is asymptotically uniform** — the natural ensemble-normality strengthening of C1,
and a new rung on the conjugacy ladder (research note §4–§5).  Nothing in the literature states it.

## The proof (execute; split into named lemmas; commit after each)

Read first: `SliceFourier.lean` end to end (module docstring, `gHatZ`, `levelSign_eq_fourier_slice`,
`sum_norm_gHatZ_le`, `sum_norm_gHatZ_dvd_le`, `exists_norm_sliceChar_pow_le`,
`exists_abs_levelSign_le`, `eventually_abs_levelSign_le`, `abs_bias_le_of_levelSign`,
`biasDecays_of_sliceCharDecay`), then `Bridge3.lean` (`levelSet`, `levelSign`, `levelMass`,
`outOddSet`), `Ladder.lean` (`tstep_iterate_lt_three_pow`, `oddCount`, `bias`) and `SliceDecay.lean`
(`sliceChar`, `SliceCharDecay`).

1. **The centred slice count.**  Define
   `levelCountRes j a K c := card ((levelSet j a).filter (fun r => tstep^[j] r % 2^K = c))` and the
   centred version `levelCountRes − card (levelSet j a) / 2^K` (as a real/complex number).  Note
   `beyondCount j K c = Σ_{a ≤ j} levelCountRes j a K c` (the slices partition `range (2^j)`).
2. **Fourier expansion on `ℤ/3^a`.**  For `r ∈ levelSet j a`, `y = tstep^[j] r < 3^a`
   (`tstep_iterate_lt_three_pow`), so `y` is its own least residue.  Let
   `g_c (y : ZMod (3^a)) := (if y.val % 2^K = c then 1 else 0) − (2^K)⁻¹ : ℂ` and
   `ĝ_c ξ := 3^{−a} Σ_y g_c y · stdAddChar (−(ξ y))`.  Then, exactly as `levelSign_eq_fourier_slice`,
   the centred slice count equals `Σ_ξ ĝ_c ξ · sliceChar j a ξ.val`.  (`zmod_fourier_inversion`
   is already general in `f`.)
3. **Weight bound, uniform in `K` and `c`.**  `Σ_ξ ‖ĝ_c ξ‖ ≤ C (a + 1)`.  Proof: `ĝ_c ξ` is
   `3^{−a} e(−ξ c/3^a)` times a geometric sum `Σ_{t<T_c} e(−ξ 2^K t/3^a)` (the `y ≡ c (2^K)` with
   `y < 3^a`), minus the constant `2^{−K} · 1[ξ = 0]`, so
   `‖ĝ_c ξ‖ ≤ 3^{−a} · min(3^a, 1/|sin(π ξ 2^K / 3^a)|)` for `ξ ≠ 0`, and `ξ ↦ ξ 2^K` is a bijection of
   `ZMod (3^a)` (`2^K` is a unit mod `3^a`).  Then `Σ_{η≠0} 1/|sin(π η/3^a)| = O(3^a log 3^a)`
   — reuse `sum_inv_abs_two_mul_sub_le_two_harmonic` / `norm_gHatZ_le_inv_abs` style bounds, or
   prove the sine version by the standard `|sin(πx)| ≥ 2‖x‖` estimate.
   Also the layered bound: the weight on `{ξ : 3^k ∣ ξ.val}` is `O(3^{−k}(a − k + 1))`, as in
   `sum_norm_gHatZ_dvd_le` (the same geometric-sum bound restricted to multiples of `3^k`).
4. **Assembly on the central window.**  Replace `gHatZ` by `ĝ_c` in `exists_abs_levelSign_le` and
   `eventually_abs_levelSign_le`: the centred slice count is `≤ ε · card (levelSet j a)` eventually,
   uniformly for `j ≤ 4a`, `a ≤ 11j/20`.  Cleanest: generalise those two theorems to an arbitrary
   `f : ZMod (3^a) → ℂ` with hypotheses `Σ_ξ ‖f̂ ξ‖ ≤ C(a+1)` and the layered bound, then
   instantiate at `paritySign` (recovering the old statements) and at `g_c`.
5. **Sum over slices.**  As in `abs_bias_le_of_levelSign`: `|beyondCount j K c − 2^{j−K}| ≤
   ε 2^j + 2 · card (outOddSet j)`, and `card (outOddSet j) / 2^j → 0` is already proved
   (`biasDecays_of_sliceCharDecay` uses it).  Conclude the `Tendsto`.
6. **Consistency.**  `bias j = 2 · beyondCount j 1 0 − 2^j` (`levelSign`/`bias` are sums of
   `±1`; `% 2^1 = % 2`), hence `biasDecays_of_beyondWordsUniform`.

Stretch (only after the gate passes; separate file `BeyondWordsLetters.lean`): the word form —
for a binary word `w` of length `K`, the count of `r < 2^j` whose parity letters `j, …, j+K−1`
equal `w` is `2^{j−K} + o(2^j)`, via the Terras bijection `m mod 2^K ↔ first K parities`
(`accWord_congr_mod` and the lifting lemmas in `Ladder.lean`).

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment;
  `decide` on small teeth is fine.
- Never edit statements in other files; adding lemmas to `SliceFourier.lean` is allowed but prefer
  a new file `CollatzMoonshot/Conjugacy/SliceFourierGeneral.lean` for the generalised pipeline.
- Do not touch `RESEARCH-*.md`, `DIRECTION.md`, `Maze.lean`; do not `git add -A` (pathspec only).
- Handoff: `HANDOFF-2026-11-03-beyond-terras-words.md` with `#print axioms` of
  `beyondWordsUniform`, `beyondWordsUniform_of_sliceCharDecay`, `biasDecays_of_beyondWordsUniform`
  (expect only `propext`, `Classical.choice`, `Quot.sound`).
- Lines ≤ 100 chars; docstrings on every new theorem.
